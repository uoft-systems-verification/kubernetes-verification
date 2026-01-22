From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

(* FIXME: Accessor should return the same pointer *)
Lemma wp_Accessor i l o:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.meta ∗
      ⌜ PureKObject.interface_agree i l o ⌝
  }}}
    @! meta.Accessor #i
  {{{ RET (#(interface.mk (ptrT.id v1.ObjectMeta.id) #(PureKObject.objectmeta_ptr l o)), #interface.nil);
    True
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
