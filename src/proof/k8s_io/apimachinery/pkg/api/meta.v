From proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_Accessor i (o: v1.Object.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.meta ∗
      "%i_is_Object" ∷ ⌜i = interface.mk v1.Object.id (# o)⌝
  }}}
    @! meta.Accessor #i
  {{{ ret (err: error.t), RET (#ret, #err);
      ⌜ ret = o ⌝ ∗ ⌜ err = interface.nil ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. subst.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros Object_id. exists o. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ok_is_true.
  { destruct ok; [done|]. intuition. }
  subst ok. inversion if_ok.
  apply (inj to_val) in H0. subst o.
  wp_auto. iApply "HΦ". done.
Qed.

End proof.
