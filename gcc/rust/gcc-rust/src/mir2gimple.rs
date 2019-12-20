use crate::gcc_api::*;
use rustc::{
    hir::def_id::LOCAL_CRATE,
    mir::{
        interpret::{ConstValue, Scalar},
        BasicBlock, BasicBlockData, BinOp, Body, Local, Operand, Place, PlaceBase, ProjectionElem,
        Rvalue, StatementKind, TerminatorKind,
    },
    ty::{AdtKind, ConstKind, Ty, TyCtxt, TyKind},
};
use rustc_interface::Queries;
use std::{collections::HashMap, convert::TryInto, ffi::CString};
use syntax::ast::{IntTy, UintTy};
use syntax_pos::symbol::Symbol;

/// Cache the types so if we convert the same anonymous type twice, we get the exact same
/// Tree object. Otherwise, we get errors about anonymous structs not being the same, even
/// though they have the same fields.
struct TypeCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    hashmap: HashMap<Ty<'tcx>, Tree>,
}

impl<'tcx> TypeCache<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            hashmap: HashMap::new(),
        }
    }

    fn do_convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        use TyKind::*;

        match ty.kind {
            Bool => TreeIndex::BooleanType.into(),
            // TODO: are these correct?
            Int(IntTy::Isize) => IntegerTypeKind::Long.into(),
            Int(IntTy::I8) => IntegerTypeKind::SignedChar.into(),
            Int(IntTy::I16) => IntegerTypeKind::Short.into(),
            Int(IntTy::I32) => IntegerTypeKind::Int.into(),
            Int(IntTy::I64) => IntegerTypeKind::LongLong.into(),
            Uint(UintTy::Usize) => IntegerTypeKind::UnsignedLong.into(),
            Uint(UintTy::U8) => IntegerTypeKind::UnsignedChar.into(),
            Uint(UintTy::U16) => IntegerTypeKind::UnsignedShort.into(),
            Uint(UintTy::U32) => IntegerTypeKind::UnsignedInt.into(),
            Uint(UintTy::U64) => IntegerTypeKind::UnsignedLongLong.into(),

            Tuple(substs) => {
                if substs.is_empty() {
                    TreeIndex::VoidType.into()
                } else {
                    let fields = DeclList::new(
                        TreeCode::FieldDecl,
                        &substs
                            .types()
                            .map(|field_ty| self.convert_type(field_ty))
                            .collect::<Vec<_>>(),
                    );

                    Tree::new_record_type(TreeCode::RecordType, fields)
                }
            }

            Adt(adt_def, substs) => {
                match adt_def.adt_kind() {
                    AdtKind::Struct | AdtKind::Union => {
                        let variant = adt_def.non_enum_variant();

                        // TODO: field names
                        let fields = DeclList::new(
                            TreeCode::FieldDecl,
                            &variant
                                .fields
                                .iter()
                                .map(|field| self.convert_type(field.ty(self.tcx, substs)))
                                .collect::<Vec<_>>(),
                        );

                        let code = match adt_def.adt_kind() {
                            AdtKind::Struct => TreeCode::RecordType,
                            AdtKind::Union => TreeCode::UnionType,
                            _ => unreachable!(),
                        };

                        Tree::new_record_type(code, fields)
                    }

                    _ => unimplemented!("adt type: {:?}", ty),
                }
            }

            _ => unimplemented!("type: {:?}", ty),
        }
    }

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        if let Some(tree) = self.hashmap.get(ty) {
            return *tree;
        }

        // TODO: return a placeholder when called recursively!
        // do_convert_type can recursively call convert_type
        let tree = self.do_convert_type(ty);
        *self.hashmap.entry(ty).or_insert(tree)
    }

    fn make_function_return_type(&mut self, body: &Body<'tcx>) -> Tree {
        self.convert_type(body.return_ty())
    }

    fn convert_decls<I>(&mut self, body: &Body<'tcx>, iter: I) -> Vec<Tree>
    where
        I: Iterator<Item = Local>,
    {
        iter.map(|local| self.convert_type(body.local_decls[local].ty))
            .collect()
    }

    fn make_function_arg_types(&mut self, body: &Body<'tcx>) -> Vec<Tree> {
        self.convert_decls(body, body.args_iter())
    }
}

struct FunctionConversion<'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    type_cache: TypeCache<'tcx>,
    fn_decl: Function,
    return_type_is_void: bool,
    res_decl: Tree,
    /// If res_decl is a struct, and one of its fields is also a struct, and we try to set it
    /// directly, we crash gcc. This may be due to the struct being anonymous. Anyway, if we
    /// do it via a temporary variable, no crash. This is the temporary variable.
    tmp_var_decl_for_res: Tree,
    parm_decls: DeclList,
    vars: DeclList,
    block_labels: Vec<Tree>,
    main_gcc_block: Tree,
    stmt_list: StatementList,
}

impl<'tcx> FunctionConversion<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, name: Symbol, body: &'tcx Body<'tcx>) -> Self {
        let mut type_cache = TypeCache::new(tcx);

        let return_type_is_void = if let TyKind::Tuple(substs) = &body.return_ty().kind {
            substs.is_empty()
        } else {
            false
        };

        let return_type = type_cache.make_function_return_type(body);
        let arg_types = type_cache.make_function_arg_types(body);
        let fn_type = Tree::new_function_type(return_type, &arg_types);

        let name = CString::new(&*name.as_str()).unwrap();
        let mut fn_decl = Function::new(&name, fn_type);
        fn_decl.set_external(false);
        fn_decl.set_preserve_p(true);

        let main_gcc_block = Tree::new_block(NULL_TREE, NULL_TREE, fn_decl.0, NULL_TREE);
        fn_decl.set_initial(main_gcc_block);

        let res_decl = Tree::new_result_decl(UNKNOWN_LOCATION, return_type);
        fn_decl.set_result(res_decl);

        let parm_decls = DeclList::new(TreeCode::ParmDecl, &arg_types);
        fn_decl.attach_parm_decls(&parm_decls);

        let vars = {
            let mut var_types = type_cache.convert_decls(body, body.vars_and_temps_iter());
            assert_eq!(
                1 + arg_types.len() + var_types.len(),
                body.local_decls.len()
            );

            // Add a var decl for tmp_var_decl_for_res
            var_types.push(return_type);

            DeclList::new(TreeCode::VarDecl, &var_types)
        };

        let tmp_var_decl_for_res = *vars.last().unwrap();

        let block_labels = body
            .basic_blocks()
            .iter()
            .map(|_bb| Tree::new_label_decl(UNKNOWN_LOCATION, fn_decl.0))
            .collect::<Vec<_>>();

        let stmt_list = StatementList::new();

        Self {
            tcx,
            body,
            type_cache,
            fn_decl,
            return_type_is_void,
            res_decl,
            tmp_var_decl_for_res,
            parm_decls,
            vars,
            block_labels,
            main_gcc_block,
            stmt_list,
        }
    }

    fn get_place(&mut self, place: &Place<'tcx>) -> Tree {
        let base = match &place.base {
            PlaceBase::Local(local) => {
                let n = local.as_usize();
                if n == 0 {
                    self.tmp_var_decl_for_res
                } else if n <= self.parm_decls.len() {
                    self.parm_decls[n - 1]
                } else {
                    self.vars[n - self.parm_decls.len() - 1]
                }
            }

            _ => unimplemented!("base {:?}", place),
        };

        // Now apply any projections

        let mut component = base;

        for elem in place.projection {
            use ProjectionElem::*;

            match elem {
                Field(field_index, _field_ty) => {
                    // TODO: this is broken for enums, maybe also structs
                    let field_decl = component
                        .get_type()
                        .get_record_type_field_decl(field_index.as_usize());
                    component = Tree::new_component_ref(component, field_decl);
                }

                _ => unimplemented!("projection {:?}", elem),
            }
        }

        component
    }

    fn convert_operand(&mut self, operand: &Operand<'tcx>) -> Tree {
        use ConstKind::*;
        use Operand::*;
        use TyKind::*;

        match operand {
            Copy(place) => self.get_place(place),
            Move(place) => self.get_place(place),

            Constant(c) => {
                let lit = &c.literal;

                match &lit.val {
                    Value(ConstValue::Scalar(Scalar::Raw { data, size: _ })) => match lit.ty.kind {
                        Int(_) | Uint(_) => Tree::new_int_constant(
                            self.type_cache.convert_type(lit.ty),
                            (*data).try_into().unwrap(),
                        ),
                        _ => unimplemented!("const {:?} {:?}", lit.ty, lit.val),
                    },

                    _ => unimplemented!("literal {:?} {:?}", lit.ty, lit.val),
                }
            }
        }
    }

    fn convert_rvalue(&mut self, rv: &Rvalue<'tcx>) -> Tree {
        use Rvalue::*;

        match rv {
            Use(operand) => self.convert_operand(operand),

            BinaryOp(op, operand1, operand2) => {
                use TreeCode::*;

                let code = match op {
                    BinOp::Add => PlusExpr,
                    BinOp::Sub => MinusExpr,
                    BinOp::Mul => MultExpr,
                    // TODO: non-integer division
                    // TODO: verify truncating type is correct
                    BinOp::Div => TruncDivExpr,
                    // TODO: non-integer division
                    // TODO: verify truncating type is correct
                    BinOp::Rem => TruncModExpr,
                    BinOp::BitXor => BitXorExpr,
                    BinOp::BitAnd => BitAndExpr,
                    BinOp::BitOr => BitIorExpr,
                    BinOp::Shl => LShiftExpr,
                    BinOp::Shr => RShiftExpr,
                    BinOp::Eq => EqExpr,
                    BinOp::Lt => LtExpr,
                    BinOp::Le => LeExpr,
                    BinOp::Ne => NeExpr,
                    BinOp::Gt => GtExpr,
                    BinOp::Ge => GeExpr,
                    // TODO: offset
                    _ => unimplemented!("binop {:?}", op),
                };

                let type_ = self.type_cache.convert_type(rv.ty(self.body, self.tcx));
                let operand1 = self.convert_operand(operand1);
                let operand2 = self.convert_operand(operand2);
                Tree::new2(code, type_, operand1, operand2)
            }

            CheckedBinaryOp(op, operand1, operand2) => {
                let type_ = self.type_cache.convert_type(rv.ty(self.body, self.tcx));
                let unchecked_value =
                    self.convert_rvalue(&BinaryOp(*op, operand1.clone(), operand2.clone()));
                // TODO: perform the check
                let check_value = TreeIndex::BooleanTrue.into();
                let constructor = Tree::new_constructor(
                    type_,
                    &[
                        type_.get_record_type_field_decl(0),
                        type_.get_record_type_field_decl(1),
                    ],
                    &[unchecked_value, check_value],
                );
                Tree::new_compound_literal_expr(type_, constructor, self.fn_decl.0)
            }

            _ => unimplemented!("rvalue {:?}", rv),
        }
    }

    fn convert_goto(&self, target: BasicBlock) -> Tree {
        let target = self.block_labels[target.as_usize()];
        Tree::new_goto(target)
    }

    fn convert_basic_block(&mut self, block_index: BasicBlock, block: &BasicBlockData<'tcx>) {
        println!("{:?}", block);

        self.stmt_list.push(Tree::new_label_expr(
            self.block_labels[block_index.as_usize()],
        ));

        use StatementKind::*;
        use TerminatorKind::*;

        for stmt in &block.statements {
            match &stmt.kind {
                StorageLive(_) | StorageDead(_) => {}
                Nop => {}
                Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    eprintln!("{:?} = {:?}", place, rvalue);

                    let place = self.get_place(place);
                    let rvalue = self.convert_rvalue(rvalue);
                    self.stmt_list.push(Tree::new_init_expr(place, rvalue));
                }
                _ => unimplemented!("{:?}", stmt),
            }
        }

        let terminator = block.terminator();
        match &terminator.kind {
            Goto { target } => {
                self.stmt_list.push(self.convert_goto(*target));
            }

            Assert { msg, target, .. } => {
                // TODO
                eprintln!("WARNING: ignoring assert with message: {:?}", msg);
                self.stmt_list.push(self.convert_goto(*target));
            }

            SwitchInt {
                discr,
                switch_ty,
                values,
                targets,
            } => {
                assert!(values.len() >= 1);
                assert_eq!(targets.len(), values.len() + 1);

                let switch_ty_tree = self.type_cache.convert_type(switch_ty);

                if values.len() == 1 {
                    let value = values[0];

                    let cond = Tree::new2(
                        TreeCode::EqExpr,
                        TreeIndex::BooleanType.into(),
                        self.convert_operand(discr),
                        Tree::new_int_constant(switch_ty_tree, value.try_into().unwrap()),
                    );

                    let if_eq_expr = self.convert_goto(targets[0]);
                    let else_expr = self.convert_goto(targets[1]);
                    self.stmt_list
                        .push(Tree::new_cond_expr(cond, if_eq_expr, else_expr));
                } else {
                    let mut cases_list = StatementList::new();

                    for (value, target) in values.into_iter().zip(targets) {
                        let case_expr = Tree::new_case_label_expr(
                            Some(Tree::new_int_constant(
                                switch_ty_tree,
                                (*value).try_into().unwrap(),
                            )),
                            Tree::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                        );

                        cases_list.push(case_expr);
                        cases_list.push(self.convert_goto(*target));
                    }

                    // default case
                    cases_list.push(Tree::new_case_label_expr(
                        None,
                        Tree::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                    ));
                    cases_list.push(self.convert_goto(*targets.last().unwrap()));

                    let discr = self.convert_operand(discr);
                    self.stmt_list
                        .push(Tree::new_switch_expr(switch_ty_tree, discr, cases_list.0));
                }
            }

            Return => {
                let return_value = if self.return_type_is_void {
                    NULL_TREE
                } else {
                    Tree::new_init_expr(self.res_decl, self.tmp_var_decl_for_res)
                };

                self.stmt_list.push(Tree::new_return_expr(return_value));
            }

            _ => unimplemented!("{:?}", terminator),
        }
    }

    fn finalize(mut self) {
        let vars_chain_head = self.vars.head().unwrap_or(NULL_TREE);
        let bind_expr = Tree::new_bind_expr(vars_chain_head, self.stmt_list.0, self.main_gcc_block);
        self.fn_decl.set_saved_tree(bind_expr);

        self.fn_decl.gimplify();
        self.fn_decl.finalize();
    }
}

fn func_mir_to_gcc<'tcx>(tcx: TyCtxt<'tcx>, name: Symbol, func_mir: &'tcx Body) {
    let mut fn_conv = FunctionConversion::new(tcx, name, func_mir);

    println!("name: {}", name);
    for (bb_idx, bb) in func_mir.basic_blocks().iter_enumerated() {
        fn_conv.convert_basic_block(bb_idx, bb);
    }

    println!();

    fn_conv.finalize();
}

pub fn mir2gimple<'tcx>(queries: &'tcx Queries<'tcx>) {
    queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
        for &mir_key in tcx.mir_keys(LOCAL_CRATE) {
            // TODO: symbol_name?
            let name = tcx.item_name(mir_key);
            let mir = tcx.optimized_mir(mir_key);
            func_mir_to_gcc(tcx, name, mir);
        }
    });
}
