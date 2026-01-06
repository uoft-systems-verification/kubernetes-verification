From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_IsNotFound_nil err:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.errors.errors ∗
      ⌜ err = interface.nil ⌝
  }}}
    @! errors.IsNotFound #err
  {{{ RET (#false);
    True%I
  }}}.
Proof.
Admitted.

End proof.
