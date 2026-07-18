From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : meta.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

(* FIXME: Accessor should return the same pointer *)
Lemma wp_Accessor i l o:
  {{{ is_pkg_init meta ∗
      ⌜ KObjectV.valid_interface i l o ⌝
  }}}
    @! meta.Accessor #(interface.ok i)
  {{{ RET (#(interface.ok (interface.mk (go.PointerType v1.ObjectMeta) #(KObjectV.objectmeta_ptr l o))), #interface.nil);
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
