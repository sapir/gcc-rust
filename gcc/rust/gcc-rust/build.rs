extern crate bindgen;

use std::env;

use bindgen::callbacks::*;
use bindgen::EnumVariation::Rust;

fn main() {
    println!("cargo:rerun-if-changed=wrapper.h");

    // Needed for compile-time generated header like config.h
    let build_dir =
        env::var("GCC_BUILD_DIR").expect("GCC_BUILD_DIR must be set to the build directory!");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .whitelist_type("tree")
        .whitelist_type("integer_type_kind")
        .whitelist_type("size_type_kind")
        .whitelist_type("tree_index")
        .whitelist_type("built_in_function")
        .whitelist_function("alloc_stmt_list")
        .whitelist_function("append_to_statement_list")
        .whitelist_function("build.*")
        .whitelist_function("gimplify_function_tree")
        .whitelist_function("make_signed_type")
        .whitelist_function("make_unsigned_type")
        .whitelist_function("get_identifier")
        .blacklist_type("poly_int64")
        .default_enum_style(Rust {
            non_exhaustive: false,
        })
        .raw_line("#![allow(dead_code, non_upper_case_globals, non_camel_case_types)]")
        .raw_line("pub type poly_int64 = i64;")
        .clang_arg(format!("-I{}", build_dir))
        .clang_arg("-I../../../include")
        .clang_arg("-I../../../libcpp/include")
        .clang_arg("-I../../")
        .clang_arg("-x")
        .clang_arg("c++")
        .parse_callbacks(Box::new(RustyNameEnum {}))
        .rustfmt_bindings(true)
        .generate()
        .expect("Unable to generate bindings");

    bindings
        .write_to_file("src/gcc_api_sys.rs")
        .expect("Couldn't write bindings!");
}

#[derive(Debug)]
struct RustyNameEnum {}

impl ParseCallbacks for RustyNameEnum {
    fn will_parse_macro(&self, _: &str) -> MacroParsingBehavior {
        MacroParsingBehavior::Default
    }

    fn int_macro(&self, name: &str, value: i64) -> Option<IntKind> {
        match name {
            // TODO: Fix poly_int64 for architecture where poly_int64 != HOST_WIDE_INT
            "NUM_POLY_INT_COEFFS" => {
                if value != 1 {
                    panic!("Architecture with NUM_POLY_INT_COEFFS != 1 are not supported yet")
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn str_macro(&self, _name: &str, _value: &[u8]) {}

    fn enum_variant_behavior(
        &self,
        _enum_name: Option<&str>,
        _original_variant_name: &str,
        _variant_value: EnumVariantValue,
    ) -> Option<EnumVariantCustomBehavior> {
        None
    }

    fn enum_variant_name(
        &self,
        enum_name: Option<&str>,
        original_variant_name: &str,
        _variant_value: EnumVariantValue,
    ) -> Option<String> {
        match enum_name {
            Some("tree_code") => match original_variant_name {
                "LSHIFT_EXPR" => Some("LShiftExpr".to_string()),
                "RSHIFT_EXPR" => Some("RShiftExpr".to_string()),
                _ => Some(snake_to_camel_case(original_variant_name)),
            },
            Some("integer_type_kind") => {
                let mut t = original_variant_name.replacen("itk_", "", 1);
                t = t.replace("N_", "_n");
                Some(snake_to_camel_case(&t))
            }
            Some("size_type_kind") => match original_variant_name {
                "stk_sizetype" => Some("UnsignedBytes".to_string()),
                "stk_ssizetype" => Some("SignedBytes".to_string()),
                "stk_bitsizetype" => Some("UnsignedBits".to_string()),
                "stk_sbitsizetype" => Some("SignedBits".to_string()),
                "stk_type_kind_last" => Some("Last".to_string()),
                _ => None,
            },

            Some("tree_index") => Some(snake_to_camel_case(
                &original_variant_name.replacen("TI_", "", 1),
            )),
            Some("built_in_function") => match original_variant_name {
                "BUILT_IN__EXIT" => Some("_Exit".to_string()),
                "BUIlT_IN__EXIT2" => Some("_Exit2".to_string()),
                _ => Some(snake_to_camel_case(&original_variant_name.replacen(
                    "BUILT_IN_",
                    "",
                    1,
                ))),
            },

            Some(_) => None,
            None => None,
        }
    }

    fn item_name(&self, item_name: &str) -> Option<String> {
        match item_name {
            "tree_code" => Some(String::from("TreeCode")),
            "integer_type_kind" => Some(String::from("IntegerTypeKind")),
            "size_type_kind" => Some(String::from("SizeTypeKind")),
            "tree_index" => Some(String::from("TreeIndex")),
            "built_in_function" => Some(String::from("BuiltinFunction")),
            _ => None,
        }
    }
}

fn snake_to_camel_case(s: &str) -> String {
    let mut must_upper = true;
    let mut r = String::from("");
    for i in s.chars() {
        if i == '_' {
            must_upper = true;
            continue;
        }
        if must_upper {
            r.push(i.to_uppercase().next().unwrap())
        } else {
            r.push(i.to_lowercase().next().unwrap())
        }
        must_upper = false;
    }
    r
}
