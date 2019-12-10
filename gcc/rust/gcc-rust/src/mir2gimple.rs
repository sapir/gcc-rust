use crate::gcc_api::*;
use rustc::{
    hir::def_id::LOCAL_CRATE,
    mir::{
        interpret::{ConstValue, Scalar},
        BasicBlock, BasicBlockData, Body, Local, Operand, Place, PlaceBase, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{ConstKind, Ty, TyKind},
};
use rustc_interface::Queries;
use std::{convert::TryInto, ffi::CString};
use syntax::ast::{IntTy, UintTy};
use syntax_pos::symbol::Symbol;

fn convert_type(ty: Ty) -> Tree {
    use TyKind::*;

    match ty.kind {
        Tuple(substs) if substs.is_empty() => TreeIndex::VoidType.into(),
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
        _ => unimplemented!("type: {:?}", ty),
    }
}

fn make_function_return_type(body: &Body) -> Tree {
    convert_type(body.return_ty())
}

fn convert_decls<I>(body: &Body, iter: I) -> Vec<Tree>
where
    I: Iterator<Item = Local>,
{
    iter.map(|local| convert_type(body.local_decls[local].ty))
        .collect()
}

fn make_function_arg_types(body: &Body) -> Vec<Tree> {
    convert_decls(body, body.args_iter())
}

struct FunctionConversion {
    fn_decl: Function,
    return_type_is_void: bool,
    res_decl: Tree,
    parm_decls: DeclList,
    vars: DeclList,
    block_labels: Vec<Tree>,
    main_gcc_block: Tree,
    stmt_list: StatementList,
}

impl FunctionConversion {
    fn new(name: Symbol, body: &Body) -> Self {
        let return_type_is_void = if let TyKind::Tuple(substs) = &body.return_ty().kind {
            substs.is_empty()
        } else {
            false
        };

        let return_type = make_function_return_type(body);
        let arg_types = make_function_arg_types(body);
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

        let var_types = convert_decls(body, body.vars_and_temps_iter());
        let vars = DeclList::new(TreeCode::VarDecl, &var_types);
        assert_eq!(1 + arg_types.len() + vars.len(), body.local_decls.len());

        let block_labels = body
            .basic_blocks()
            .iter()
            .map(|_bb| Tree::new_artificial_label(UNKNOWN_LOCATION))
            .collect::<Vec<_>>();

        let stmt_list = StatementList::new();

        Self {
            fn_decl,
            return_type_is_void,
            res_decl,
            parm_decls,
            vars,
            block_labels,
            main_gcc_block,
            stmt_list,
        }
    }

    fn get_place(&self, place: &Place) -> Tree {
        if !place.projection.is_empty() {
            unimplemented!("non-empty projection");
        }

        match &place.base {
            PlaceBase::Local(local) => {
                let n = local.as_usize();
                if n == 0 {
                    self.res_decl
                } else if n <= self.parm_decls.len() {
                    self.parm_decls[n - 1]
                } else {
                    self.vars[n - self.parm_decls.len() - 1]
                }
            }

            _ => unimplemented!("base {:?}", place),
        }
    }

    fn convert_rvalue(&self, rv: &Rvalue) -> Tree {
        use ConstKind::*;
        use Operand::*;
        use Rvalue::*;
        use TyKind::*;

        match rv {
            Use(Copy(place)) => self.get_place(place),
            Use(Move(place)) => self.get_place(place),

            Use(Constant(c)) => {
                let lit = &c.literal;

                match &lit.val {
                    Value(ConstValue::Scalar(Scalar::Raw { data, size: _ })) => match lit.ty.kind {
                        Int(_) | Uint(_) => Tree::new_int_constant(
                            convert_type(lit.ty),
                            (*data).try_into().unwrap(),
                        ),
                        _ => unimplemented!("const {:?} {:?}", lit.ty, lit.val),
                    },

                    _ => unimplemented!("literal {:?} {:?}", lit.ty, lit.val),
                }
            }

            _ => unimplemented!("rvalue {:?}", rv),
        }
    }

    fn convert_basic_block(&mut self, block_index: BasicBlock, block: &BasicBlockData) {
        println!("{:?}", block);

        self.stmt_list
            .push(self.block_labels[block_index.as_usize()]);

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
            Return => {
                let return_value = if self.return_type_is_void {
                    NULL_TREE
                } else {
                    self.res_decl
                };

                self.stmt_list.push(Tree::new_return_expr(return_value));
            }

            _ => unimplemented!("{:?}", terminator),
        }
    }

    fn finalize(mut self) {
        let vars_chain_head = self.vars.get(0).map(|t| *t).unwrap_or(NULL_TREE);
        let bind_expr = Tree::new_bind_expr(vars_chain_head, self.stmt_list.0, self.main_gcc_block);
        self.fn_decl.set_saved_tree(bind_expr);

        self.fn_decl.gimplify();
        self.fn_decl.finalize();
    }
}

fn func_mir_to_gcc(name: Symbol, func_mir: &Body) {
    let mut fn_conv = FunctionConversion::new(name, func_mir);

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
            func_mir_to_gcc(name, mir);
        }
    });
}
