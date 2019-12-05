use crate::gcc_api::*;
use rustc::{
    hir::def_id::LOCAL_CRATE,
    mir::{BasicBlockData, Body},
};
use rustc_interface::Queries;
use std::{
    ffi::CString,
    os::raw::{c_char, c_uint, c_ulong},
    ptr::null_mut,
};
use syntax_pos::symbol::Symbol;

fn handle_basic_block(block_labels: &[Tree], block: &BasicBlockData) {
    println!("{:?}", block);
}

fn func_mir_to_gcc<'tcx>(name: Symbol, func_mir: &Body<'tcx>) {
    use IntegerTypeKind::Int;
    use TreeCode::{BindExpr, InitExpr, ResultDecl, ReturnExpr};
    use TreeIndex::VoidType;

    unsafe {
        let fn_type = _build_function_type_array(Int.into(), 0, std::ptr::null_mut());
        let name = CString::new(&*name.as_str()).unwrap();
        let fn_decl = _build_fn_decl(name.as_ptr(), fn_type);

        let mut stmt_list = StatementList::new();

        let resdecl = _build_decl(UNKNOWN_LOCATION, ResultDecl, NULL_TREE, Int.into());
        set_fn_result(fn_decl, resdecl.clone());

        let set_result = _build2(
            InitExpr,
            VoidType.into(),
            resdecl,
            build_int_constant(Int.into(), 5),
        );
        let return_stmt = _build1(ReturnExpr, VoidType.into(), set_result);
        stmt_list.push(return_stmt);

        let main_block = _build_block(NULL_TREE, NULL_TREE, fn_decl, NULL_TREE);
        let bind_expr = _build3(
            BindExpr,
            VoidType.into(),
            NULL_TREE,
            stmt_list.0,
            main_block,
        );

        set_fn_initial(fn_decl, main_block);
        set_fn_saved_tree(fn_decl, bind_expr);
        set_fn_external(fn_decl, false);
        set_fn_preserve_p(fn_decl, true);

        _gimplify_function_tree(fn_decl);
        finalize_function(fn_decl, true);
    }

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
