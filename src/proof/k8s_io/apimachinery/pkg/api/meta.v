From proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

(* FIXME: this spec is wrong because o's value should be a Pod pointer. will fix it after Goose has better support for
  interface method dispatch *)
Lemma wp_Accessor i ptr:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.meta ∗
      ⌜i = interface.mk (ptrT.id v1.Pod.id) (# ptr)⌝
  }}}
    @! meta.Accessor #i
  {{{ o (err: error.t), RET (#o, #err);
      ⌜ o = interface.mk (ptrT.id v1.ObjectMeta.id) #(struct.field_ref_f v1.Pod "ObjectMeta" ptr) ⌝ ∗
      ⌜ err = interface.nil ⌝
  }}}.
Proof.
  (* wp_start as "H". iNamed "H". wp_auto. subst.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros Object_id. exists o. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ok_is_true.
  { destruct ok; [done|]. intuition. }
  subst ok. inversion if_ok.
  apply (inj to_val) in H0. subst o.
  wp_auto. iApply "HΦ". done.
Qed. *)
Admitted.

End proof.
