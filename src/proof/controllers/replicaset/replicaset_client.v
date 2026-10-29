From New.proof Require Import wp_keep.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get.
From New.proof.kubernetes_model.replicaset Require Export update_status.
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
Context {model_sem : apimodel.Assumptions}.
Collection W := sem + package_sem + model_sem.
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
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem model_sem.
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

(* [kubeClient.AppsV1().ReplicaSets(namespace)], in the form [wp_auto_keep] leaves it
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
  wp_method_call. rewrite /kubernetes.Clientset__AppsV1ⁱᵐᵖˡ. wp_call. wp_auto_keep.
  wp_method_call. rewrite /trusted_client_apps_v1.AppsV1Client__ReplicaSetsⁱᵐᵖˡ. wp_call. wp_auto_keep.
  iPersist "replicaSetClient".
  iModIntro. iApply "HΦ". iExists _, _. iFrame "#". done.
Qed.

(* [c.UpdateStatus(ctx, rs, opts)] forwards to [State.ReplicaSetUpdateStatusTx], which retries
   resource-version conflicts (see the trusted shim), so a requested status passing the guard
   [ReplicaSetStatusV.valid_update] is always written. *)
Lemma wp_ReplicaSetInterface__UpdateStatus γ l c namespace (ctx opts : val)
    rs_l rs requested dq dq_in :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
      "#Hclient" ∷ is_rs_client c namespace ∗
      "%Hnamespace" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hvalid_requested" ∷ ⌜ ReplicaSetStatusV.valid_update rs.(ReplicaSetV.Status') requested ⌝ ∗
      "Hinput" ∷ ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hstatus" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    (MethodResolve client_apps_v1.ReplicaSetInterface "UpdateStatus"%go #c) ctx #rs_l opts
  {{{ (result_l : loc) rs', RET (#result_l, #interface.nil);
      ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ∧
        rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
      ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      ⌜ ReplicaSetV.valid rs' ⌝ ∗
      ⌜ ReplicaSetStatusV.updated requested rs'.(ReplicaSetV.Status') ⌝
      (* The returned object [result_l] (Go's [updatedRS]) is not described:
         the verified controller discards it ([_, err = updateReplicaSetStatus(...)]
         in controllers/replicaset/replica_set.go). Its ownership is available
         from [wp_State__ReplicaSetUpdateStatusTx_same_meta] when a caller needs it,
         for example the availability requeue that reads
         [updatedRS.Spec.MinReadySeconds]. *)
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  iDestruct "Hclient" as (cl v) "(-> & %Hns & #Hcl)".
  wp_bind (MethodResolve client_apps_v1.ReplicaSetInterface _ _). wp_pure. wp_pures_keep.
  wp_method_call. rewrite /trusted_client_gentype.Client__UpdateStatusⁱᵐᵖˡ decide_True; try reflexivity.
  rewrite /trusted_client_gentype.clientCreate. wp_call.
  rewrite /trusted_client_gentype.clientType. wp_auto_keep.
  change (go.PointerType trusted_code.k8s_io.client_go.gentype.api_apps_v1.ReplicaSet)
    with (go.PointerType code.k8s_io.api.apps.v1.v1.ReplicaSet).
  try (rewrite !decide_True; try reflexivity).
  try wp_auto_keep.
  rewrite Hns.
  set input := rs <| ReplicaSetV.Status' := requested |>.
  pose proof Hvalid as (Hvalid_typemeta & Hvalid_rv & Hvalid_meta & Hvalid_spec & _).
  pose proof Hvalid_meta as (_ & Hname_nonempty & _ & _ & _ & Hvalid_uid & Hlabels &
    Hannotations & Howners & Hfinalizers & Hmanaged_fields & _).
  pose proof (valid_uid_non_empty _ Hvalid_uid) as Huid_nonempty.
  (* The guard on the status makes the whole request valid. *)
  assert (ReplicaSetV.valid_status_update ReplicaSetV.kind namespace rs.(ReplicaSetV.ObjectMeta')
      rs.(ReplicaSetV.Status') input) as Hvalid_request.
  { rewrite /ReplicaSetV.valid_status_update /=.
    split_and!; try done.
    rewrite /ObjectMetaV.valid_update. split_and!; try done.
    left. rewrite /ObjectMetaV.valid_simple_update. split_and!; done. }
  wp_apply (wp_State__ReplicaSetUpdateStatusTx_same_meta γ l namespace rs_l input dq_in
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.Status')
    with "[$Hisk $Hinput $Hmeta $Hstatus]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros (result_l rs_c) "(Hinput & Hmeta & %Hvalid' & %Hupdated & %Hmeta_eq & _ & Hstatus)".
  wp_auto_keep. rewrite decide_True; try reflexivity. wp_auto_keep.
  (* [rs'] is [rs] with the stored metadata and status. *)
  iApply ("HΦ" $! result_l
    (rs <| ReplicaSetV.ObjectMeta' := rs_c.(ReplicaSetV.ObjectMeta') |>
        <| ReplicaSetV.Status' := rs_c.(ReplicaSetV.Status') |>)).
  iFrame "Hinput Hstatus". iSplit.
  { iPureIntro. simpl. split; done. }
  iSplitL "Hmeta".
  { iApply (kview.own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hmeta"). }
  iSplit.
  { iPureIntro. destruct Hvalid' as (_ & Hrv' & Hmeta' & _ & Hstatus').
    rewrite /ReplicaSetV.valid /=. split_and!; done. }
  iPureIntro.
  rewrite /ReplicaSetV.status_updated in Hupdated.
  destruct Hupdated as (_ & _ & Hstatus_updated). exact Hstatus_updated.
Qed.

(* A variant of [wp_ReplicaSetInterface__UpdateStatus] that does not require the
   requested status to pass the guard, so the API server may reject it. Either
   way the fragments describe some [rs'] that keeps [rs]'s metadata (up to
   resource version) and spec; on an error [rs'] is [rs]. *)
Lemma wp_ReplicaSetInterface__UpdateStatus_general γ l c namespace (ctx opts : val)
    rs_l rs requested dq dq_in :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
      "#Hclient" ∷ is_rs_client c namespace ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hinput" ∷ ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hstatus" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    (MethodResolve client_apps_v1.ReplicaSetInterface "UpdateStatus"%go #c) ctx #rs_l opts
  {{{ (result_l : loc) (err : interface.t) rs', RET (#result_l, #err);
      ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ∧
        rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
      ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      ⌜ ReplicaSetV.valid rs' ⌝
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
  set input := rs <| ReplicaSetV.Status' := requested |>.
  pose proof Hvalid as (Hvalid_typemeta & Hvalid_rv & Hvalid_meta & Hvalid_spec & _).
  wp_apply (wp_State__ReplicaSetUpdateStatusTx_same_meta_general γ l namespace rs_l input dq_in
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.Status')
    with "[$Hisk $Hinput $Hmeta $Hstatus]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros (result_l err) "(Hinput & Hmeta & Hpost)".
  iDestruct "Hpost" as "[(-> & %rs_c & %Hvalid' & %Hmeta_eq & _ & Hstatus) | (%Herr_ne & Hstatus)]".
  2: {
    wp_auto. rewrite decide_True; try reflexivity. wp_auto.
    iApply ("HΦ" $! result_l err rs). iFrame. iPureIntro. split_and!; done. }
  wp_auto. rewrite decide_True; try reflexivity. wp_auto.
  (* [rs'] is [rs] with the stored metadata and status. *)
  iApply ("HΦ" $! result_l interface.nil
    (rs <| ReplicaSetV.ObjectMeta' := rs_c.(ReplicaSetV.ObjectMeta') |>
        <| ReplicaSetV.Status' := rs_c.(ReplicaSetV.Status') |>)).
  iFrame "Hinput Hstatus". iSplit.
  { iPureIntro. simpl. split; done. }
  iSplitL "Hmeta".
  { iApply (kview.own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hmeta"). }
  iPureIntro. destruct Hvalid' as (_ & Hrv' & Hmeta' & _ & Hstatus').
  rewrite /ReplicaSetV.valid /=. split_and!; done.
Qed.

(* [c.Get(ctx, name, opts)] forwards to [State.ReplicaSetGet], which returns a
   copy of the stored ReplicaSet described by the fragments. *)
Lemma wp_ReplicaSetInterface__Get γ l c key namespace name (ctx opts : val)
    uid dq dq_status kmeta kspec kstatus :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
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
  rewrite Hns.
  wp_apply (wp_State__ReplicaSetGet γ l key namespace name uid dq dq_status kmeta kspec kstatus
    with "[$Hisk $Hown_meta_frag $Hown_spec_frag $Hown_status_frag]").
  { iFrame "#". done. }
  iIntros (rs_l rs) "Hpost".
  wp_auto.
  change (go.PointerType trusted_code.k8s_io.client_go.gentype.api_apps_v1.ReplicaSet)
    with (go.PointerType code.k8s_io.api.apps.v1.v1.ReplicaSet).
  try (rewrite !decide_True; try reflexivity).
  try wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

End proof.
