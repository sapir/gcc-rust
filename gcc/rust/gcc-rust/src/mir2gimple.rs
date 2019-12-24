use crate::gcc_api::*;
use rustc::{
    mir::{
        interpret::{ConstValue, Scalar},
        mono::MonoItem,
        AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, Local, Operand, Place, PlaceBase,
        ProjectionElem, Rvalue, StatementKind, TerminatorKind, UnOp,
    },
    ty::{
        subst::{Subst, SubstsRef},
        AdtKind, ConstKind, Instance, ParamEnv, PolyFnSig, Ty, TyCtxt, TyKind, TypeAndMut,
        VariantDef,
    },
};
use rustc_interface::Queries;
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};
use std::{collections::HashMap, convert::TryInto, ffi::CString};
use syntax::ast::{IntTy, UintTy};
use syntax_pos::symbol::Symbol;

struct ConvertedFnSig {
    pub return_type: Tree,
    pub arg_types: Vec<Tree>,
}

/// Cache the types so if we convert the same anonymous type twice, we get the exact same
/// Tree object. Otherwise, we get errors about anonymous structs not being the same, even
/// though they have the same fields.
struct TypeCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    func_substs: SubstsRef<'tcx>,
    hashmap: HashMap<Ty<'tcx>, Tree>,
}

impl<'tcx> TypeCache<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, func_substs: SubstsRef<'tcx>) -> Self {
        Self {
            tcx,
            func_substs,
            hashmap: HashMap::new(),
        }
    }

    fn convert_variant_fields(
        &mut self,
        variant: &VariantDef,
        substs: SubstsRef<'tcx>,
    ) -> DeclList {
        // TODO: field names
        DeclList::new(
            TreeCode::FieldDecl,
            &variant
                .fields
                .iter()
                .map(|field| self.convert_type(field.ty(self.tcx, substs)))
                .collect::<Vec<_>>(),
        )
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

                    let mut ty = Tree::new_record_type(TreeCode::RecordType);
                    ty.finish_record_type(fields);
                    ty
                }
            }

            Adt(adt_def, substs) => {
                // Cache type before creating fields to avoid infinite recursion for
                // self-referential types.
                let code = match adt_def.adt_kind() {
                    AdtKind::Struct | AdtKind::Enum => TreeCode::RecordType,
                    AdtKind::Union => TreeCode::UnionType,
                };

                let mut tt = Tree::new_record_type(code);
                self.hashmap.insert(ty, tt);

                // Now add the fields...
                match adt_def.adt_kind() {
                    AdtKind::Struct | AdtKind::Union => {
                        let variant = adt_def.non_enum_variant();
                        tt.finish_record_type(self.convert_variant_fields(variant, substs));
                    }

                    AdtKind::Enum => {
                        // Pretend it looks like
                        // struct {
                        //     long discriminant;
                        //     union {
                        //         variant1;
                        //         variant2;
                        //         ...
                        //     }
                        // }
                        //
                        // (It seems rustc expects the discriminant to be an isize, which is
                        // currently converted into a long.)

                        let discr_ty = IntegerTypeKind::Long.into();

                        let variants = adt_def
                            .variants
                            .iter()
                            .map(|variant| {
                                // afaik variants cannot currently be treated as a separate type,
                                // so they can't be self-referential and we don't need to cache
                                // them.
                                let mut variant_ty = Tree::new_record_type(TreeCode::RecordType);
                                variant_ty.finish_record_type(
                                    self.convert_variant_fields(variant, substs),
                                );
                                variant_ty
                            })
                            .collect::<Vec<_>>();
                        let mut variant_union_ty = Tree::new_record_type(TreeCode::UnionType);
                        variant_union_ty
                            .finish_record_type(DeclList::new(TreeCode::FieldDecl, &variants));

                        tt.finish_record_type(DeclList::new(
                            TreeCode::FieldDecl,
                            &[discr_ty, variant_union_ty],
                        ));
                    }
                }

                tt
            }

            RawPtr(TypeAndMut { ty, mutbl: _ }) => {
                // TODO: mutability
                Tree::new_pointer_type(self.convert_type(ty))
            }

            FnDef(..) => {
                let ConvertedFnSig {
                    return_type,
                    arg_types,
                } = self.convert_fn_sig(ty.fn_sig(self.tcx));
                Tree::new_function_type(return_type, &arg_types)
            }

            Ref(_region, ty, _mutbl) => {
                // TODO: mutability
                Tree::new_pointer_type(self.convert_type(ty))
            }

            Projection(_proj_ty) => unreachable!(concat!(
                "Projection types should have been resolved previously by",
                " subst_and_normalize_erasing_regions"
            )),

            Array(element_type, num_elements) => {
                if let ConstKind::Value(ConstValue::Scalar(num_elements)) = num_elements.val {
                    let num_elements = num_elements.to_u64().expect("expected bits, got a ptr?");
                    Tree::new_array_type(self.convert_type(element_type), num_elements)
                } else {
                    unreachable!("array with non-const number of elements");
                }
            }

            _ => unimplemented!("type: {:?} ({:?})", ty, ty.kind),
        }
    }

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        let ty = self.tcx.subst_and_normalize_erasing_regions(
            self.func_substs,
            ParamEnv::reveal_all(),
            &ty,
        );

        if let Some(tree) = self.hashmap.get(ty) {
            return *tree;
        }

        // TODO: return a placeholder when called recursively!
        // do_convert_type can recursively call convert_type
        let tree = self.do_convert_type(ty);
        *self.hashmap.entry(ty).or_insert(tree)
    }

    fn convert_fn_sig(&mut self, fn_sig: PolyFnSig<'tcx>) -> ConvertedFnSig {
        // TODO: fn_sig.c_variadic, fn_sig.abi
        let inputs_and_output = fn_sig.inputs_and_output();
        let inputs_and_output = self.tcx.erase_late_bound_regions(&inputs_and_output);
        let (return_type, arg_types) = inputs_and_output.split_last().expect("missing return type");

        let return_type = self.convert_type(return_type);
        let arg_types = arg_types
            .into_iter()
            .map(|arg| self.convert_type(arg))
            .collect();

        ConvertedFnSig {
            return_type,
            arg_types,
        }
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

struct FunctionConversion<'tcx, 'body> {
    tcx: TyCtxt<'tcx>,
    body: &'body Body<'tcx>,
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

impl<'tcx, 'body> FunctionConversion<'tcx, 'body> {
    fn new(
        tcx: TyCtxt<'tcx>,
        name: Symbol,
        instance: Instance<'tcx>,
        body: &'body Body<'tcx>,
    ) -> Self {
        let mut type_cache = TypeCache::new(tcx, instance.substs);

        let return_type_is_void = if let TyKind::Tuple(substs) = &body.return_ty().kind {
            substs.is_empty()
        } else {
            false
        };

        let return_type = type_cache.make_function_return_type(&body);
        let arg_types = type_cache.make_function_arg_types(&body);
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
            let mut var_types = type_cache.convert_decls(&body, body.vars_and_temps_iter());
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

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        self.type_cache.convert_type(ty)
    }

    fn get_local(&self, local: Local) -> Tree {
        let n = local.as_usize();
        if n == 0 {
            self.tmp_var_decl_for_res
        } else if n <= self.parm_decls.len() {
            self.parm_decls[n - 1]
        } else {
            self.vars[n - self.parm_decls.len() - 1]
        }
    }

    fn get_place(&mut self, place: &Place<'tcx>) -> Tree {
        let base = match &place.base {
            PlaceBase::Local(local) => self.get_local(*local),
            _ => unimplemented!("base {:?}", place),
        };

        // Now apply any projections

        let mut component = base;

        for elem in place.projection {
            use ProjectionElem::*;

            match elem {
                Field(field_index, _field_ty) => {
                    let field_decl = component
                        .get_type()
                        .get_record_type_field_decl(field_index.as_usize());
                    component = Tree::new_component_ref(component, field_decl);
                }

                Downcast(_, variant_index) => {
                    // variants_ref = enum_structs.variants. The union is the 2nd field.
                    let variants_union_field_decl =
                        component.get_type().get_record_type_field_decl(1);
                    let variants_ref =
                        Tree::new_component_ref(component, variants_union_field_decl);

                    // component = variants_ref.variantN
                    let variant_struct_field_decl = variants_ref
                        .get_type()
                        .get_record_type_field_decl(variant_index.as_usize());
                    component = Tree::new_component_ref(variants_ref, variant_struct_field_decl);
                }

                Deref => {
                    component = Tree::new_indirect_ref(component);
                }

                Index(index) => {
                    let index = self.get_local(*index);

                    // an ArrayType's type field contains its element type
                    let array_type = component.get_type();
                    assert_eq!(array_type.get_code(), TreeCode::ArrayType);
                    let element_type = array_type.get_type();

                    component = Tree::new_array_index_ref(element_type, component, index);
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
                            self.convert_type(lit.ty),
                            // TODO: this is incorrect on big-endian architectures; data should be
                            // treated as a byte array up to size bytes long.
                            (*data).try_into().unwrap(),
                        ),

                        Bool => {
                            if *data != 0 {
                                TreeIndex::BooleanTrue.into()
                            } else {
                                TreeIndex::BooleanFalse.into()
                            }
                        }

                        FnDef(def_id, substs) => {
                            let name = self.tcx.symbol_name(Instance::new(def_id, substs));
                            let name = name.name;
                            let fn_type = self.convert_type(lit.ty);
                            // TODO: move next line into Function::new
                            let name = CString::new(&*name.as_str()).unwrap();
                            Function::new(&name, fn_type).0
                        }

                        Tuple(substs) if substs.is_empty() => TreeIndex::Void.into(),

                        _ => unimplemented!(
                            "const, ty.kind={:?}, ty={:?}, val={:?}",
                            lit.ty.kind,
                            lit.ty,
                            lit.val
                        ),
                    },

                    _ => unimplemented!("literal {:?} {:?}", lit.ty, lit.val),
                }
            }
        }
    }

    /// Get a component_ref for an enum's discriminant field
    fn get_discriminant_ref(&mut self, place: &Place<'tcx>) -> Tree {
        let place = self.get_place(place);

        // enum_struct.discriminant = variant_index.
        // discriminant is 1st field.
        let discr_field_decl = place.get_type().get_record_type_field_decl(0);
        Tree::new_component_ref(place, discr_field_decl)
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

                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let operand1 = self.convert_operand(operand1);
                let operand2 = self.convert_operand(operand2);
                Tree::new2(code, type_, operand1, operand2)
            }

            CheckedBinaryOp(op, operand1, operand2) => {
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let unchecked_value =
                    self.convert_rvalue(&BinaryOp(*op, operand1.clone(), operand2.clone()));
                // TODO: perform the check
                let check_value = TreeIndex::BooleanTrue.into();
                let constructor = Tree::new_record_constructor(
                    type_,
                    &[
                        type_.get_record_type_field_decl(0),
                        type_.get_record_type_field_decl(1),
                    ],
                    &[unchecked_value, check_value],
                );
                Tree::new_compound_literal_expr(type_, constructor, self.fn_decl.0)
            }

            UnaryOp(op, operand) => {
                let operand = self.convert_operand(operand);
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let code = match op {
                    UnOp::Neg => TreeCode::NegateExpr,
                    UnOp::Not => TreeCode::BitNotExpr,
                };
                Tree::new1(code, type_, operand)
            }

            Discriminant(place) => self.get_discriminant_ref(place),

            Ref(_region, _borrow_kind, place) => Tree::new_addr_expr(self.get_place(place)),

            Aggregate(agg_kind, operands) => {
                use AggregateKind::*;

                match &**agg_kind {
                    Array(_element_type) => {
                        let array_type = self.convert_type(rv.ty(self.body, self.tcx));
                        let constructor = Tree::new_array_constructor(
                            array_type,
                            &operands
                                .into_iter()
                                .map(|operand| self.convert_operand(operand))
                                .collect::<Vec<_>>(),
                        );
                        Tree::new_compound_literal_expr(array_type, constructor, self.fn_decl.0)
                    }

                    _ => unimplemented!(
                        "rvalue aggregate kind {:?}, operands={:?}",
                        agg_kind,
                        operands
                    ),
                }
            }

            _ => unimplemented!("rvalue {:?}", rv),
        }
    }

    fn convert_goto(&self, target: BasicBlock) -> Tree {
        let target = self.block_labels[target.as_usize()];
        Tree::new_goto(target)
    }

    fn convert_unreachable(&self) -> Tree {
        Tree::new_call_expr(
            UNKNOWN_LOCATION,
            TreeIndex::VoidType.into(),
            Tree::new_addr_expr(BuiltinFunction::Unreachable.into()),
            &[],
        )
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
                Nop => {}

                // These may be useful in the future, but are currently ignored.
                StorageLive(_) | StorageDead(_) => {}

                // I think these can be ignored safely, although I'm not sure about FakeRead.
                AscribeUserType(_, _) | Retag(_, _) | FakeRead(_, _) => {}

                Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    eprintln!("{:?} = {:?}", place, rvalue);

                    let place = self.get_place(place);
                    let rvalue = self.convert_rvalue(rvalue);
                    self.stmt_list.push(Tree::new_init_expr(place, rvalue));
                }

                SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    let discr_ref = self.get_discriminant_ref(place);

                    let variant_index = Tree::new_int_constant(
                        IntegerTypeKind::Long,
                        variant_index.as_u32().into(),
                    );

                    self.stmt_list
                        .push(Tree::new_init_expr(discr_ref, variant_index));
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

                let switch_ty_tree = self.convert_type(switch_ty);

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

            Unreachable => {
                self.stmt_list.push(self.convert_unreachable());
            }

            Call {
                func,
                args,
                destination,
                cleanup: _,
                from_hir_call: _,
            } => {
                let func = self.convert_operand(func);
                let args = args
                    .into_iter()
                    .map(|arg| self.convert_operand(arg))
                    .collect::<Vec<_>>();
                // TODO: don't ignore cleanup
                // TODO: how to use from_hir_call?

                let (call_expr_type, returns_void) = if let Some((place, _)) = destination {
                    let place_ty = place.ty(&self.body.local_decls, self.tcx);
                    if place_ty.variant_index.is_some() {
                        unreachable!("call's return type is an enum variant");
                    }

                    let call_expr_type = self.convert_type(place_ty.ty);
                    let returns_void = place_ty.ty.is_unit();
                    (call_expr_type, returns_void)
                } else {
                    (TreeIndex::VoidType.into(), true)
                };

                let call_expr = Tree::new_call_expr(
                    UNKNOWN_LOCATION,
                    call_expr_type,
                    Tree::new_addr_expr(func),
                    &args,
                );

                if let Some((place, destination)) = destination {
                    if returns_void {
                        self.stmt_list.push(call_expr);
                    } else {
                        let init_expr = Tree::new_init_expr(self.get_place(place), call_expr);
                        self.stmt_list.push(init_expr);
                    }

                    self.stmt_list.push(self.convert_goto(*destination));
                } else {
                    self.stmt_list.push(call_expr);
                    self.stmt_list.push(self.convert_unreachable());
                }
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

fn func_mir_to_gcc<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: Symbol,
    instance: Instance<'tcx>,
    body: &'tcx Body,
) {
    let body = body.subst(tcx, instance.substs);
    let mut fn_conv = FunctionConversion::new(tcx, name, instance, &body);

    println!("name: {}", name);
    for (bb_idx, bb) in body.basic_blocks().iter_enumerated() {
        fn_conv.convert_basic_block(bb_idx, bb);
    }

    println!();

    fn_conv.finalize();
}

pub fn mir2gimple<'tcx>(queries: &'tcx Queries<'tcx>) {
    queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
        let (mono_items, _inlining_map) =
            collect_crate_mono_items(tcx, MonoItemCollectionMode::Eager);

        for item in mono_items {
            match item {
                MonoItem::Fn(instance) => {
                    let name = tcx.symbol_name(instance).name;
                    let mir = tcx.optimized_mir(instance.def_id());
                    func_mir_to_gcc(tcx, name, instance, mir);
                }

                _ => unimplemented!("monoitem {:?}", item),
            }
        }
    });
}
