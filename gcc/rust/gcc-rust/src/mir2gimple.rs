use crate::gcc_api::*;
use rustc::{
    hir::def_id::LOCAL_CRATE,
    mir::{BasicBlockData, Body},
    ty::{Ty, TyKind},
};
use rustc_interface::Queries;
use std::ffi::CString;
use syntax::ast::{IntTy, UintTy};
use syntax_pos::symbol::Symbol;

fn convert_type(ty: Ty<'_>) -> Tree {
    use TyKind::*;

    match ty.kind {
        Tuple(substs) if substs.is_empty() => TreeIndex::VoidType.into(),
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

fn make_function_type(body: &Body<'_>) -> Tree {
    let return_type = convert_type(body.return_ty());
    let arg_types = body
        .args_iter()
        .map(|arg| convert_type(body.local_decls[arg].ty))
        .collect::<Vec<_>>();
    Tree::new_function_type(return_type, arg_types)
}

fn handle_basic_block(block_labels: &[Tree], block: &BasicBlockData) {
    println!("{:?}", block);
}

fn func_mir_to_gcc(name: Symbol, func_mir: &Body<'_>) {
    use IntegerTypeKind::Int;

    let fn_type = make_function_type(func_mir);

    let name = CString::new(&*name.as_str()).unwrap();
    let mut fn_decl = Function::new(&name, fn_type);

    let mut stmt_list = StatementList::new();

    let resdecl = Tree::new_result_decl(UNKNOWN_LOCATION, Int.into());
    fn_decl.set_result(resdecl);

    let set_result = Tree::new_init_expr(resdecl, Tree::new_int_constant(Int, 5));
    stmt_list.push(Tree::new_return_expr(set_result));

    let main_block = Tree::new_block(NULL_TREE, NULL_TREE, fn_decl.0, NULL_TREE);
    let bind_expr = Tree::new_bind_expr(NULL_TREE, stmt_list.0, main_block);

    fn_decl.set_initial(main_block);
    fn_decl.set_saved_tree(bind_expr);
    fn_decl.set_external(false);
    fn_decl.set_preserve_p(true);

    fn_decl.gimplify();
    fn_decl.finalize();

    /*
    let block_labels = func_mir
        .basic_blocks()
        .iter()
        .map(|_bb| unsafe { create_artifical_label(UNKNOWN_LOCATION) })
        .collect::<Vec<_>>();

    println!("name: {}", name.as_str());
    for bb in func_mir.basic_blocks() {
        handle_basic_block(&block_labels, bb);
    }

    println!();
    */
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
