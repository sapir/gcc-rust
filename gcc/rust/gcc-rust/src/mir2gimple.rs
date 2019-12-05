use rustc::{hir::def_id::LOCAL_CRATE, mir::Body};
use rustc_interface::Queries;
use syntax_pos::symbol::Symbol;

#[repr(C)]
pub struct Tree {
    _private: [u8; 0],
}

extern "C" {
    fn make_a_tree() -> *mut Tree;
    fn gimplify_and_finalize(tree: *mut Tree);
}

fn func_mir_to_gcc<'tcx>(name: Symbol, func_mir: &Body<'tcx>) {
    println!("name: {}", name.as_str());
    for bb in func_mir.basic_blocks() {
        println!("{:?}", bb);
    }

    println!();
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

    unsafe {
        let tree = make_a_tree();
        gimplify_and_finalize(tree);
    }
}
