#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tree.h"
#include "gimple-expr.h"
#include "diagnostic.h"
#include "opts.h"
#include "fold-const.h"
#include "gimplify.h"
#include "stor-layout.h"
#include "debug.h"
#include "convert.h"
#include "langhooks.h"
#include "langhooks-def.h"
#include "tree-iterator.h"
#include "cgraph.h"
#include "common/common-target.h"

struct GTY(()) lang_type {
  char dummy;
};

struct GTY(()) lang_decl {
  char dummy;
};

struct GTY(()) lang_identifier {
  struct tree_identifier common;
};

struct GTY(()) language_function {
  int dummy;
};

union GTY(
    (desc("TREE_CODE (&%h.generic) == IDENTIFIER_NODE"),
     chain_next(
         "CODE_CONTAINS_STRUCT (TREE_CODE (&%h.generic), TS_COMMON)"
         " ? ((union lang_tree_node *) TREE_CHAIN (&%h.generic)) : NULL")))
    lang_tree_node {
  union tree_node GTY((tag("0"), desc("tree_node_structure (&%h)"))) generic;
  struct lang_identifier GTY((tag("1"))) identifier;
};

tree convert(tree type, tree expr) {
  if (type == error_mark_node || expr == error_mark_node ||
      TREE_TYPE(expr) == error_mark_node)
    return error_mark_node;

  if (type == TREE_TYPE(expr))
    return expr;

  if (TYPE_MAIN_VARIANT(type) == TYPE_MAIN_VARIANT(TREE_TYPE(expr)))
    return fold_convert(type, expr);

  switch (TREE_CODE(type)) {
  case VOID_TYPE:
  case BOOLEAN_TYPE:
    return fold_convert(type, expr);
  case INTEGER_TYPE:
    return fold(convert_to_integer(type, expr));
  case POINTER_TYPE:
    return fold(convert_to_pointer(type, expr));
  case REAL_TYPE:
    return fold(convert_to_real(type, expr));
  case COMPLEX_TYPE:
    return fold(convert_to_complex(type, expr));
  default:
    break;
  }

  gcc_unreachable();
}

static bool rust_langhook_init(void) {
  build_common_tree_nodes(false);
  void_list_node = build_tree_list(NULL_TREE, void_type_node);
  build_common_builtin_nodes();
  return true;
}

// Defined by Rust gcc_rust library
extern "C" void compile_to_mir(const char **filenames, size_t num_filenames);

extern "C" {
  tree _alloc_stmt_list() {
    return alloc_stmt_list();
  }

  void _append_to_statement_list(tree stmt, tree *list) {
    append_to_statement_list(stmt, list);
  }

  tree _build0(enum tree_code code, tree tt) {
    return build0(code, tt);
  }

  tree _build1(enum tree_code code, tree tt, tree arg0) {
    return build1(code, tt, arg0);
  }
  tree _build2(enum tree_code code, tree tt, tree arg0, tree arg1) {
    return build2(code, tt, arg0, arg1);
  }
  tree _build3(enum tree_code code, tree tt, tree arg0, tree arg1, tree arg2) {
    return build3(code, tt, arg0, arg1, arg2);
  }
  tree _build4(enum tree_code code, tree tt, tree arg0, tree arg1, tree arg2, tree arg3) {
    return build4(code, tt, arg0, arg1, arg2, arg3);
  }
  tree _build5(
      enum tree_code code,
      tree tt,
      tree arg0,
      tree arg1,
      tree arg2,
      tree arg3,
      tree arg4
  ) {
    return build5(code, tt, arg0, arg1, arg2, arg3, arg4);
  }
  tree _build_decl(location_t loc, enum tree_code code, tree name, tree tt) {
    return build_decl(loc, code, name, tt);
  }
  tree _build_string_literal(
      size_t len,
      const char *string,
      tree eltype,
      unsigned long size
  ) {
    return build_string_literal(len, string, eltype, size);
  }
  tree _build_block(tree vars, tree subblocks, tree supercontext, tree chain) {
    return build_block(vars, subblocks, supercontext, chain);
  }
  tree _build_call_array_loc(
      location_t loc,
      tree returntype,
      tree fn_ptr,
      size_t num_args,
      tree *args
  ) {
    return build_call_array_loc(loc, returntype, fn_ptr, num_args, args);
  }
  tree _build_pointer_type(tree totype) {
    return build_pointer_type(totype);
  }
  tree _build_function_type_array(
      tree returntype,
      size_t num_args,
      tree *arg_types
  ) {
    return build_function_type_array(returntype, num_args, arg_types);
  }
  tree _build_fn_decl(const char *name, tree type) {
    return build_fn_decl(name, type);
  }
  tree _create_artificial_label(location_t loc) {
    return create_artificial_label(loc);
  }
  void _gimplify_function_tree(tree t) {
    return gimplify_function_tree(t);
  }

  tree build_int_constant(tree int_type, int64_t value) {
    return build_int_cst_type(int_type, value);
  }

  void set_fn_result(tree fn_decl, tree result) {
    DECL_RESULT(fn_decl) = result;
  }

  void set_fn_initial(tree fn_decl, tree t) {
    DECL_INITIAL(fn_decl) = t;
  }

  void set_fn_saved_tree(tree fn_decl, tree t) {
    DECL_SAVED_TREE(fn_decl) = t;
  }

  void set_fn_external(tree fn_decl, bool value) {
    DECL_EXTERNAL(fn_decl) = value;
  }

  void set_fn_preserve_p(tree fn_decl, bool value) {
    DECL_PRESERVE_P(fn_decl) = value;
  }

  void add_fn_parm_decls(
    tree fn_decl,
    size_t num_args,
    tree *arg_types,
    tree *decls
  ) {
    tree prev_parm_decl = NULL_TREE;

    for (size_t i = num_args; i > 0; --i) {
      tree arg_type = arg_types[i - 1];
      tree parm_decl = build_decl(UNKNOWN_LOCATION, PARM_DECL, NULL_TREE, arg_type);
      DECL_CONTEXT(parm_decl) = fn_decl;
      // passed in with the same type as the regular type
      DECL_ARG_TYPE(parm_decl) = arg_type;
      DECL_CHAIN(parm_decl) = prev_parm_decl;

      decls[i - 1] = parm_decl;

      prev_parm_decl = parm_decl;
    }

    DECL_ARGUMENTS(fn_decl) = prev_parm_decl;
  }

  void finalize_decl(tree decl) {
    varpool_node::finalize_decl(decl);
  }

  void finalize_function(tree fndecl, bool no_collect) {
    cgraph_node::finalize_function(fndecl, no_collect);
  }
}

static void rust_langhook_parse_file(void) {
  compile_to_mir(in_fnames, num_in_fnames);
}

static tree rust_langhook_type_for_mode(enum machine_mode mode,
                                         int unsignedp) {
  if (mode == TYPE_MODE(float_type_node))
    return float_type_node;

  if (mode == TYPE_MODE(double_type_node))
    return double_type_node;

  if (mode == TYPE_MODE(intQI_type_node))
    return unsignedp ? unsigned_intQI_type_node : intQI_type_node;
  if (mode == TYPE_MODE(intHI_type_node))
    return unsignedp ? unsigned_intHI_type_node : intHI_type_node;
  if (mode == TYPE_MODE(intSI_type_node))
    return unsignedp ? unsigned_intSI_type_node : intSI_type_node;
  if (mode == TYPE_MODE(intDI_type_node))
    return unsignedp ? unsigned_intDI_type_node : intDI_type_node;
  if (mode == TYPE_MODE(intTI_type_node))
    return unsignedp ? unsigned_intTI_type_node : intTI_type_node;

  if (mode == TYPE_MODE(integer_type_node))
    return unsignedp ? unsigned_type_node : integer_type_node;

  if (mode == TYPE_MODE(long_integer_type_node))
    return unsignedp ? long_unsigned_type_node : long_integer_type_node;

  if (mode == TYPE_MODE(long_long_integer_type_node))
    return unsignedp ? long_long_unsigned_type_node
                     : long_long_integer_type_node;

  if (COMPLEX_MODE_P(mode)) {
    if (mode == TYPE_MODE(complex_float_type_node))
      return complex_float_type_node;
    if (mode == TYPE_MODE(complex_double_type_node))
      return complex_double_type_node;
    if (mode == TYPE_MODE(complex_long_double_type_node))
      return complex_long_double_type_node;
    if (mode == TYPE_MODE(complex_integer_type_node) && !unsignedp)
      return complex_integer_type_node;
  }

  return NULL;
}

static tree rust_langhook_type_for_size(unsigned int bits ATTRIBUTE_UNUSED,
                                         int unsignedp ATTRIBUTE_UNUSED) {
  gcc_unreachable();
  return NULL;
}

static tree rust_langhook_builtin_function(tree decl) { return decl; }

static bool rust_langhook_global_bindings_p(void) {
  gcc_unreachable();
  return true;
}

static tree rust_langhook_pushdecl(tree decl ATTRIBUTE_UNUSED) {
  gcc_unreachable();
}

static tree rust_langhook_getdecls(void) { return NULL; }

#undef LANG_HOOKS_NAME
#define LANG_HOOKS_NAME "Rust"

#undef LANG_HOOKS_INIT
#define LANG_HOOKS_INIT rust_langhook_init

#undef LANG_HOOKS_PARSE_FILE
#define LANG_HOOKS_PARSE_FILE rust_langhook_parse_file

#undef LANG_HOOKS_TYPE_FOR_MODE
#define LANG_HOOKS_TYPE_FOR_MODE rust_langhook_type_for_mode

#undef LANG_HOOKS_TYPE_FOR_SIZE
#define LANG_HOOKS_TYPE_FOR_SIZE rust_langhook_type_for_size

#undef LANG_HOOKS_BUILTIN_FUNCTION
#define LANG_HOOKS_BUILTIN_FUNCTION rust_langhook_builtin_function

#undef LANG_HOOKS_GLOBAL_BINDINGS_P
#define LANG_HOOKS_GLOBAL_BINDINGS_P rust_langhook_global_bindings_p

#undef LANG_HOOKS_PUSHDECL
#define LANG_HOOKS_PUSHDECL rust_langhook_pushdecl

#undef LANG_HOOKS_GETDECLS
#define LANG_HOOKS_GETDECLS rust_langhook_getdecls

struct lang_hooks lang_hooks = LANG_HOOKS_INITIALIZER;

#include "gt-rust-rust1.h"
#include "gtype-rust.h"
