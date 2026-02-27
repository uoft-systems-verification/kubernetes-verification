From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_deepCopy i pure_obj:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i pure_obj 1
  }}}
    @! apimodel.deepCopy #i
  {{{ i', RET #i';
      KObjectV.deepown_i i' pure_obj 1 ∗
      KObjectV.deepown_i i pure_obj 1
  }}}.
Proof.
Admitted.

End proof.