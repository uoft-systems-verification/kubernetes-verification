From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get replicaset_update_status.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.k8s_io.client_go Require Export kubernetes_init gentype_init.

Module client_apps_v1 := code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module client_core_v1 := code.k8s_io.client_go.kubernetes.typed.core.v1.v1.
Module client_gentype := code.k8s_io.client_go.gentype.gentype.
Module trusted_client_apps_v1 := trusted_code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module trusted_client_gentype := trusted_code.k8s_io.client_go.gentype.gentype.
(* See progress.v: the trusted gentype shim spells [Client] with [go.Named]. *)
Transparent client_gentype.Client.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
(* The client instances only serve method resolution; priority 100 keeps them
   from supplying the object-type assumptions used by the model specs. *)
#[local] Instance clientset_sem : kubernetes.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_kubernetes_Assumption.
#[local] Instance client_apps_v1_sem : client_apps_v1.Assumptions | 100 :=
  kubernetes.import_apps_v1_Assumption.
#[local] Instance client_core_v1_sem : client_core_v1.Assumptions | 100 :=
  kubernetes.import_core_v1_Assumption.
#[local] Instance client_gentype_sem : client_gentype.Assumptions | 100 :=
  client_core_v1.import_gentype_Assumption.
(* Object-type assumptions route through [apimodel], as in calculate_status.v,
   so statements here match the model specs. *)
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
(* The same constructed instances as in top_level.v, so that [is_kubernetes]
   in these specs matches the top-level specs. *)
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

(* The ReplicaSet client returned by [AppsV1().ReplicaSets(namespace)]: an
   immutable [gentype.Client] whose only field read by the model shim is the
   namespace. *)
Definition is_rs_client (c : interface.t) (namespace : go_string) : iProp Σ :=
  ∃ (cl : loc) (v : client_gentype.Client.t loc),
    ⌜ c = interface.mk_ok (go.PointerType trusted_client_apps_v1.replicaSetClientType) #cl ⌝ ∗
    ⌜ v.(client_gentype.Client.namespace') = namespace ⌝ ∗
    cl ↦□ v.

#[global] Instance is_rs_client_persistent c namespace : Persistent (is_rs_client c namespace).
Proof. apply _. Qed.

(* [kubeClient.AppsV1().ReplicaSets(namespace)], in the form [wp_auto] leaves it
   once the [AppsV1()] method on the clientset has been resolved. *)
Lemma wp_AppsV1_ReplicaSets (kube_client : loc) namespace :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset }}}
    (MethodResolve client_apps_v1.AppsV1Interface "ReplicaSets"%go
      (kube_client @! (go.PointerType kubernetes.Clientset) @! "AppsV1"%go #()))
      #namespace
  {{{ c, RET #c; is_rs_client c namespace }}}.
Proof.
  iIntros (Φ) "#Hpkg HΦ".
  iApply wp_fupd.
  wp_method_call. rewrite /kubernetes.Clientset__AppsV1ⁱᵐᵖˡ. wp_call. wp_auto.
  wp_method_call. rewrite /trusted_client_apps_v1.AppsV1Client__ReplicaSetsⁱᵐᵖˡ. wp_call. wp_auto.
  iPersist "replicaSetClient".
  iModIntro. iApply "HΦ". iExists _, _. iFrame "#". done.
Qed.

(* [c.UpdateStatus(ctx, rs, opts)] forwards to [State.ReplicaSetUpdateStatusTx], which retries
   resource-version conflicts (see the trusted shim), so a failure means the requested status is
   invalid. *)
Lemma wp_ReplicaSetInterface__UpdateStatus γ l c namespace (ctx opts : val)
    rs_l rs requested dq dq_in :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclient" ∷ is_rs_client c namespace ∗
      "%Hnamespace" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hinput" ∷ ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hstatus" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    (MethodResolve client_apps_v1.ReplicaSetInterface "UpdateStatus"%go #c) ctx #rs_l opts
  {{{ result_l rs' err, RET (#result_l, #err);
      ⌜ ReplicaSetV.status_only_changed rs rs' ⌝ ∗
      ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      ((⌜ err = interface.nil ⌝ ∗
        ⌜ ReplicaSetV.valid rs' ⌝ ∗
        ⌜ ReplicaSetStatusV.valid requested →
          ReplicaSetStatusV.updated requested rs'.(ReplicaSetV.Status') ⌝ ∗
        ReplicaSetV.deepown_l result_l rs' 1) ∨
       (⌜ err ≠ interface.nil ∧ result_l = null ∧ rs' = rs ∧ ¬ ReplicaSetStatusV.valid requested ⌝))
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  iDestruct "Hclient" as (cl v) "(-> & %Hns & #Hcl)".
  wp_bind (MethodResolve client_apps_v1.ReplicaSetInterface _ _). wp_pure. wp_pures.
  wp_method_call. rewrite /trusted_client_gentype.Client__UpdateStatusⁱᵐᵖˡ decide_True; try reflexivity.
  rewrite /trusted_client_gentype.clientCreate. wp_call.
  rewrite /trusted_client_gentype.clientType. wp_auto.
  change (go.PointerType trusted_code.k8s_io.client_go.gentype.api_apps_v1.ReplicaSet)
    with (go.PointerType code.k8s_io.api.apps.v1.v1.ReplicaSet).
  try (rewrite !decide_True; try reflexivity).
  try wp_auto.
  rewrite Hns.
  wp_apply (wp_State__ReplicaSetUpdateStatusTx γ l namespace rs_l rs requested dq dq_in
    with "[$Hisk $Hinput $Hmeta $Hspec $Hstatus]").
  { iFrame "#". done. }
  iIntros (result_l rs' err) "Hpost".
  wp_auto. rewrite decide_True; try reflexivity. wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

(* [c.Get(ctx, name, opts)] forwards to [State.ReplicaSetGet]. *)
Lemma wp_ReplicaSetInterface__Get γ l c namespace (ctx opts : val) name
    key uid dq dq_status kmeta kspec kstatus :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclient" ∷ is_rs_client c namespace ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "ReplicaSet"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq_status (ObjectStatusV.ReplicaSetStatus kstatus)
  }}}
    (MethodResolve client_apps_v1.ReplicaSetInterface "Get"%go #c) ctx #name opts
  {{{ rs_l rs, RET (#rs_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.ReplicaSet rs) ⌝ ∗
      "%Hextra_valid" ∷ ⌜ ReplicaSetV.extra_valid rs ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ReplicaSetV.key rs ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version rs.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = rs.(ReplicaSetV.Spec') ⌝ ∗
      "%Hstatus_eq" ∷ ⌜ kstatus = rs.(ReplicaSetV.Status') ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq_status (ObjectStatusV.ReplicaSetStatus kstatus)
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  iDestruct "Hclient" as (cl v) "(-> & %Hns & #Hcl)".
  wp_bind (MethodResolve client_apps_v1.ReplicaSetInterface _ _). wp_pure. wp_pures.
  wp_method_call. rewrite /trusted_client_gentype.Client__Getⁱᵐᵖˡ decide_True; try reflexivity.
  rewrite /trusted_client_gentype.clientGet. wp_call.
  rewrite /trusted_client_gentype.clientType. wp_auto.
  change (go.PointerType trusted_code.k8s_io.client_go.gentype.api_apps_v1.ReplicaSet)
    with (go.PointerType code.k8s_io.api.apps.v1.v1.ReplicaSet).
  try (rewrite !decide_True; try reflexivity).
  try wp_auto.
  rewrite Hns.
  wp_apply (wp_State__ReplicaSetGet_status γ l key namespace name uid dq dq_status kmeta kspec kstatus
    with "[$Hisk $Hown_meta_frag $Hown_spec_frag $Hown_status_frag]").
  { iFrame "#". done. }
  iIntros (rs_l rs) "Hpost".
  wp_auto. rewrite decide_True; try reflexivity. wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

End proof.
