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
#include "stringpool.h"
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
  const char *crate_type = NULL;

  tree _builtin_decl_implicit(enum built_in_function fncode) {
    return builtin_decl_implicit(fncode);
  }

  tree get_tree_type(tree t) {
    return TREE_TYPE(t);
  }

  enum tree_code get_tree_code(tree t) {
    return TREE_CODE(t);
  }

  tree get_type_size_bytes(tree t) {
    return TYPE_SIZE_UNIT(t);
  }

  void set_type_name(tree tt, tree identifier) {
    TYPE_NAME(tt) = identifier;
  }

  tree build_constructor_from_field_array(
      tree type,
      size_t num_fields,
      const tree *field_decls,
      const tree *field_values
  ) {
    vec<constructor_elt, va_gc> *v = NULL;

    if (num_fields > 0) {
      vec_alloc(v, num_fields);
      for (size_t i = 0; i < num_fields; ++i) {
	CONSTRUCTOR_APPEND_ELT(v, field_decls[i], field_values[i]);
      }
    }

    return build_constructor(type, v);
  }

  tree build_int_constant(tree int_type, int64_t value) {
    return build_int_cst_type(int_type, value);
  }

  tree build_constructor_from_element_array(
      tree type,
      size_t num_elements,
      const tree *elements
  ) {
    vec<constructor_elt, va_gc> *v = NULL;

    if (num_elements > 0) {
      vec_alloc(v, num_elements);
      for (size_t i = 0; i < num_elements; ++i) {
	CONSTRUCTOR_APPEND_ELT(v, build_int_cst_type(integer_type_node, i), elements[i]);
      }
    }

    return build_constructor(type, v);
  }

  tree build_label_decl(location_t loc, tree context) {
    tree decl = build_decl(loc, LABEL_DECL, NULL_TREE, void_type_node);
    DECL_ARTIFICIAL(decl) = 1;
    DECL_IGNORED_P(decl) = 1;
    DECL_CONTEXT(decl) = context;
    SET_DECL_MODE(decl, VOIDmode);
    return decl;
  }

  void set_tree_static(tree t, bool value) {
    TREE_STATIC(t) = value;
  }

  void set_tree_public(tree t, bool value) {
    TREE_PUBLIC(t) = value;
  }

  void make_decl_chain(
    enum tree_code code,
    size_t num_decls,
    const tree *types,
    tree *decls
  ) {
    tree prev_decl = NULL_TREE;

    for (size_t i = num_decls; i > 0; --i) {
      tree type = types[i - 1];
      tree decl = build_decl(UNKNOWN_LOCATION, code, NULL_TREE, type);
      if (PARM_DECL == code) {
        // parameters are passed in with the same type as the regular type
        DECL_ARG_TYPE(decl) = type;
      }
      DECL_CHAIN(decl) = prev_decl;

      decls[i - 1] = decl;

      prev_decl = decl;
    }
  }

  void set_decl_context(tree decl, tree context) {
      DECL_CONTEXT(decl) = context;
  }

  void set_decl_initial(tree decl, tree value) {
      DECL_INITIAL(decl) = value;
  }

  void set_decl_chain_context(
    tree chain_head,
    tree context
  ) {
    for (tree cur = chain_head; cur; cur = DECL_CHAIN(cur)) {
      DECL_CONTEXT(cur) = context;
    }
  }

  void place_field_manually(tree field_decl, uint64_t byte_offset) {
    layout_decl(field_decl, byte_offset);

    if (byte_offset == 0) {
      DECL_FIELD_OFFSET(field_decl) = size_zero_node;
      SET_DECL_OFFSET_ALIGN(field_decl, BIGGEST_ALIGNMENT);
    } else {
      DECL_FIELD_OFFSET(field_decl) = build_int_cstu(sizetype, byte_offset);
      SET_DECL_OFFSET_ALIGN(field_decl, 1 << ffs(byte_offset));
    }

    // We don't use bitfields or bit-unaligned fields
    DECL_FIELD_BIT_OFFSET(field_decl) = bitsize_zero_node;
  }

  void finish_record_type(
    tree record_type,
    tree fields_chain_head,
    uint64_t byte_size,
    uint64_t byte_alignment
  ) {
    // see stor-layout.c:finish_record_layout()

    TYPE_FIELDS(record_type) = fields_chain_head;
    TYPE_SIZE(record_type) = build_int_cstu(bitsizetype, byte_size * BITS_PER_UNIT);
    TYPE_SIZE_UNIT(record_type) = build_int_cstu(sizetype, byte_size);
    SET_TYPE_ALIGN(record_type, byte_alignment * BITS_PER_UNIT);
    // TODO: is this necessary?
    TYPE_USER_ALIGN(record_type) = 1;

    compute_record_mode(record_type);
    // TODO: TYPE_PACKED
  }

  // TODO: store these in a rust vec? then no need for a loop here
  tree get_record_type_field_decl(tree record_type, size_t index) {
    tree cur = TYPE_FIELDS(record_type);
    for (size_t i = 0; cur != NULL_TREE && i < index; ++i) {
      cur = DECL_CHAIN(cur);
    }
    return cur;
  }

  // based on build_compound_literal in c_decl.c
  tree build_compound_literal_expr(tree type, tree value, tree context) {
    tree decl = build_decl(UNKNOWN_LOCATION, VAR_DECL, NULL_TREE, type);
    DECL_EXTERNAL(decl) = 0;
    TREE_PUBLIC(decl) = 0;
    TREE_STATIC(decl) = false;
    DECL_CONTEXT(decl) = context;
    TREE_USED(decl) = 1;
    DECL_READ_P(decl) = 1;
    DECL_ARTIFICIAL(decl) = 1;
    DECL_IGNORED_P(decl) = 1;
    TREE_TYPE(decl) = type;
    DECL_INITIAL(decl) = value;
    tree decl_expr = build1(DECL_EXPR, type, decl);
    return build1(COMPOUND_LITERAL_EXPR, type, decl_expr);
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

  void attach_fn_parm_decls(tree fn_decl, tree decl_chain) {
    DECL_ARGUMENTS(fn_decl) = decl_chain;
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
  return current_function_decl == NULL_TREE;
}

static tree rust_langhook_pushdecl(tree decl ATTRIBUTE_UNUSED) {
  gcc_unreachable();
}

static tree rust_langhook_getdecls(void) { return NULL; }

static unsigned int rust_langhook_option_lang_mask(void)
{
  return CL_Rust;
}

static bool rust_langhook_handle_option(
    size_t scode,
    const char *arg,
    HOST_WIDE_INT value ATTRIBUTE_UNUSED,
    int kind ATTRIBUTE_UNUSED,
    location_t loc ATTRIBUTE_UNUSED,
    const struct cl_option_handlers *handlers ATTRIBUTE_UNUSED)
{
  enum opt_code code = (enum opt_code)scode;

  switch (code) {
  case OPT_fcrate_type_:
    crate_type = arg;
    break;

  default:
    break;
  }

  return true;
}

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

#undef LANG_HOOKS_OPTION_LANG_MASK
#define LANG_HOOKS_OPTION_LANG_MASK rust_langhook_option_lang_mask

#undef LANG_HOOKS_HANDLE_OPTION
#define LANG_HOOKS_HANDLE_OPTION rust_langhook_handle_option

struct lang_hooks lang_hooks = LANG_HOOKS_INITIALIZER;

#include "gt-rust-rust1.h"
#include "gtype-rust.h"
