# Rust frontend for GCC

This is currently at a very early stage. At the time of writing, it can compile
trivial functions, like:

```rust
fn my_function(x: i32) -> i32 { x }
```

But most language features don't work yet.


## How does it work?

The `gcc/rust` directory contains a frontend with some boilerplate that links to
a Rust crate in `gcc/rust/gcc_rust`. The Rust code runs rustc up to the MIR
stage, then generates a GENERIC tree (a GCC IR) and passes it back to the C
code. Access to GCC's internal APIs (especially macros) is handled by C wrapper
functions in `gcc/rust/rust1.cc`.


## Build instructions

(Be warned, these are currently rather rough.)

```sh
mkdir gcc
cd gcc
git clone --depth 50 -b rust https://github.com/sapir/gcc-rust/ gcc-src

RUST_TOOLCHAIN=$(cat gcc-src/gcc/rust/gcc-rust/rust-toolchain)
rustup toolchain add "$RUST_TOOLCHAIN"
rustup component add --toolchain="$RUST_TOOLCHAIN" rustc-dev

mkdir gcc-build
cd gcc-build
../gcc-src/configure \
    --prefix=$(pwd)/../gcc-install \
    --enable-languages=c,c++,rust \
    --disable-multilib \
    --disable-bootstrap
make
make install

cd ..
gcc-install/bin/gcc whatever.rs -o whatever.so -shared
```
