# Rust frontend for GCC


## Build instructions

(Be warned, these are currently rather rough.)

Build Rust with this patch: https://github.com/rust-lang/rust/pull/67126

```
mkdir gcc
cd gcc
git clone --depth 50 -b rust https://github.com/sapir/gcc-rust/ gcc-src
(cd gcc-src/gcc/rust/gcc-rust; cargo build)

mkdir gcc-build
cd gcc-build
../gcc-src/configure --prefix=$(pwd)/../gcc-install --enable-languages=c,c++,rust --disable-multilib --disable-bootstrap
make
make install

cd ..
gcc-install/bin/gcc whatever.rs -o whatever
```
