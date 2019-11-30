#![feature(rustc_private)]

#[macro_use]
extern crate log;
extern crate log_settings;
extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate syntax_pos;

use rustc::{hir::def_id::LOCAL_CRATE, mir::Body};
use rustc_driver::Compilation;
use rustc_interface::interface;
use syntax_pos::symbol::Symbol;

struct GccRustCompilerCalls;

impl rustc_driver::Callbacks for GccRustCompilerCalls {
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> Compilation {
        compiler.session().abort_if_errors();

        compiler.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            for &mir_key in tcx.mir_keys(LOCAL_CRATE) {
                // TODO: symbol_name?
                let name = tcx.item_name(mir_key);
                let mir = tcx.optimized_mir(mir_key);
                func_mir_to_gcc(name, mir);
            }
        });

        compiler.session().abort_if_errors();
        Compilation::Stop
    }
}

fn func_mir_to_gcc<'tcx>(name: Symbol, func_mir: &Body<'tcx>) {
    println!("name: {}", name.as_str());
    for bb in func_mir.basic_blocks() {
        println!("{:?}", bb);
    }

    println!();
}

// copied from miri
/// Returns the "default sysroot" that Miri will use if no `--sysroot` flag is set.
/// Should be a compile-time constant.
fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc would
    // end up somewhere in the build dir.
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build Miri without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn main() {
    let mut rustc_args = std::env::args().into_iter().collect::<Vec<_>>();

    // copied from miri
    // Determine sysroot if needed.  Make sure we always call `compile_time_sysroot`
    // as that also does some sanity-checks of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error, but
    // CTFE does not seem powerful enough for that yet.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !rustc_args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc would compute.
            rustc_args.push(sysroot_flag.to_owned());
            rustc_args.push(sysroot);
        }
    }

    rustc_driver::install_ice_hook();
    let result = rustc_driver::catch_fatal_errors(move || {
        rustc_driver::run_compiler(&rustc_args, &mut GccRustCompilerCalls, None, None)
    })
    .and_then(|result| result);

    std::process::exit(result.is_err() as i32);
}
