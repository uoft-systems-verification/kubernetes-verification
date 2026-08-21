From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.

From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {schema_sem : schema.Assumptions}.
Collection W := sem + schema_sem.

Lemma wp_SchemeGroupVersion__WithKind kind :
  {{{ "#Hinit" ∷ is_pkg_init code.k8s_io.api.apps.v1.pkg_id.v1 }}}
    (global_addr code.k8s_io.api.apps.v1.v1.SchemeGroupVersion) @!
      (go.PointerType schema.GroupVersion) @! "WithKind" #kind
  {{{ gvk, RET #gvk;
      ⌜ gvk.(schema.GroupVersionKind.Group') = "apps"%go ∧
        gvk.(schema.GroupVersionKind.Version') = "v1"%go ∧
        gvk.(schema.GroupVersionKind.Kind') = kind ⌝
  }}}.
Proof using hG schema_sem sem Σ.
  wp_start as "H". iNamed "H".
  iDestruct (is_pkg_init_access with "Hinit") as "Happs_init".
  simpl.
  iDestruct "Happs_init" as (gv)
    "(#Hglobal_gv & %HSchemeGroupVersion_Group &
      %HSchemeGroupVersion_Version)".
  wp_pures.
  wp_load.
  wp_pures.
  iDestruct (is_pkg_init_unfold_deps with "Hinit") as
    "(_ & _ & #Hschema_init & _)".
  wp_apply (schema.wp_GroupVersion__WithKind with "[$Hschema_init]").
  iIntros (gvk) "%Hgvk".
  destruct Hgvk as (Hgroup & Hversion & Hkind).
  iApply "HΦ". iPureIntro.
  rewrite Hgroup Hversion HSchemeGroupVersion_Group
    HSchemeGroupVersion_Version.
  done.
Qed.

Context {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma get_owner_references_capability_ReplicaSet rs_l rs dq :
  ⊢ get_owner_references_capability
    (interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l)
    rs.(ReplicaSetV.ObjectMeta') dq
    (ReplicaSetV.deepown_l rs_l rs dq).
Proof.
  unfold get_owner_references_capability.
  wp_start as "H". iNamed "H".
  iPoseProof (ReplicaSetV.deepown_l_split with "Hown") as
    "(%Hrs_l_nonnull & Htypemeta & Hmeta & Hspec & Hstatus)".
  wp_auto.
  wp_method_call.
  wp_pures.
  wp_apply (wp_GetOwnerReferences_deepown with "[$Hinit $Hmeta]").
  iIntros (sl) "(%Hnil & Hrefs)".
  iApply "HΦ". iSplit; first done.
  destruct rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.OwnerReferences') as
    [refs|] eqn:Hrefs_some.
  - iDestruct "Hrefs" as (cs) "(Hsl & Hrefs & Hmeta_restore)".
    iExists cs. iFrame "Hsl Hrefs".
    iIntros (cs') "[Hsl Hrefs]".
    iDestruct ("Hmeta_restore" with "[$Hsl $Hrefs]") as "Hmeta".
    iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_nonnull).
    iFrame.
  - iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_nonnull).
    iFrame.
Qed.

Lemma wp_GetControllerOf_ReplicaSet owner rs_l rs dq :
  {{{ "Hinit" ∷ is_pkg_init v1 ∗
      "%Howner" ∷ ⌜ owner = interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l ⌝ ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq
  }}}
    @! v1.GetControllerOf #owner
  {{{ controller_ref_l, RET #controller_ref_l;
      ReplicaSetV.deepown_l rs_l rs dq ∗
      (⌜ controller_ref_l = null ⌝ ∨
       ∃ controller_ref,
         ⌜ controller_ref_l ≠ null ∧
           is_controller_reference_of rs.(ReplicaSetV.ObjectMeta') controller_ref ⌝ ∗
         OwnerReferenceV.deepown_l controller_ref_l controller_ref 1)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". subst owner.
  iPoseProof (get_owner_references_capability_ReplicaSet rs_l rs dq) as
    "Hget".
  iApply (wp_GetControllerOf_general with "[$Hinit $Hget $Hrs]").
  iExact "HΦ".
Qed.

End proof.
