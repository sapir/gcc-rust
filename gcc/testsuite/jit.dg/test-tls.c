#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "libgccjit.h"

#include "harness.h"

void
create_code (gcc_jit_context *ctxt, void *user_data)
{
  /* Let's try to inject the equivalent of:

     _Thread_local int foo;
  */
  gcc_jit_type *int_type =
    gcc_jit_context_get_type (ctxt, GCC_JIT_TYPE_INT);

  gcc_jit_lvalue *foo =
    gcc_jit_context_new_global (
      ctxt, NULL, GCC_JIT_GLOBAL_EXPORTED, int_type, "foo");
  gcc_jit_lvalue_set_tls_model (foo, GCC_JIT_TLS_MODEL_GLOBAL_DYNAMIC);
}

void
verify_code (gcc_jit_context *ctxt, gcc_jit_result *result)
{
}
