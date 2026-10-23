From New.proof Require Import prelude empty_ffi wp_helpers.
From New.proof.k8s_io.utils Require Import ptr.
From New.proof Require Import reflect.
From New.proof.controllers.replicaset Require Export replicaset_client calculate_status.
From New.proof.controllers.replicaset Require Import top_level.

Module goreflect := code.reflect.reflect.

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

Local Ltac split_bool :=
  match goal with |- context [bool_decide ?P] => destruct (bool_decide P) eqn:? end.

(* [updateReplicaSetStatus] writes the requested status (with the observed
   generation set). The caller shows that this status passes validation, so the
   first write succeeds and the retry after a GET is never reached. The write
   keeps the stored metadata (up to resource version) and spec; the status
   fragment follows the stored status. *)
Lemma wp_updateReplicaSetStatus γ l c rs_l rs_phy rs status_c status dq :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclient" ∷ is_rs_client c rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hvalid_status" ∷ ⌜ ReplicaSetStatusV.valid_request (status <| ReplicaSetStatusV.ObservedGeneration' :=
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') |>) ⌝ ∗
      "Hrs_l" ∷ rs_l ↦ rs_phy ∗
      "Hrs" ∷ ReplicaSetV.deepown rs_phy rs DfracDiscarded ∗
      "#Hstatus" ∷ ReplicaSetStatusV.deepown status_c status DfracDiscarded ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hstatus_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    @! replicaset.updateReplicaSetStatus #c #rs_l #status_c
  {{{ (result_l : loc) (rs' : ReplicaSetV.t), RET (#result_l, #interface.nil);
      ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ∧
        rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status'))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (⌜ rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') =
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') ⌝)%I as %Hgen.
  { iNamed "Hrs". iNamed "Hdeepown_objectmeta". done. }
  iApply wp_fupd.
  iPoseProof (ReplicaSetStatusV.terminating_rep with "Hstatus") as "#Hnew_term".
  iAssert (opt_ptr_rep rs_phy.(v1.ReplicaSet.Status').(api_apps_v1.ReplicaSetStatus.TerminatingReplicas')
    rs.(ReplicaSetV.Status').(ReplicaSetStatusV.TerminatingReplicas') DfracDiscarded)%I as "#Hold_term".
  { iDestruct "Hrs" as "(_ & _ & _ & Hst)". iApply (ReplicaSetStatusV.terminating_rep with "Hst"). }
  wp_auto.
  (* The no-op check evaluates to some boolean. *)
  wp_bind (if: _ then (let: "$a0" := _ in let: "$a1" := _ in
    FuncResolve goreflect.DeepEqual [] #() "$a0" "$a1") else #false)%E.
  iApply (wp_wand _ _ _ (λ v, ∃ b : bool, ⌜ v = #b ⌝ ∗
      "rs" ∷ rs_ptr ↦ rs_l ∗ "Hrs_l" ∷ rs_l ↦ rs_phy ∗
      "newStatus" ∷ newStatus_ptr ↦ status_c)%I with "[rs Hrs_l newStatus]").
  { repeat (split_bool; try wp_auto; try (iExists false; iFrame; done)).
    all: wp_apply (wp_Equal_int32 with "[]");
      [iSplitR; [iExact "Hold_term"|iExact "Hnew_term"]|].
    all: iIntros (r) "_".
    all: destruct r; try wp_auto; try (iExists false; iFrame; done).
    all: split_bool; try wp_auto; try (iExists false; iFrame; done).
    all: wp_apply wp_DeepEqual.
    all: iIntros (r) "_". all: iExists r; iFrame; done. }
  iIntros (v) "(%b & -> & rs & Hrs_l & newStatus)".
  destruct b.
  { (* already up to date: nothing is written *)
    wp_auto. iApply ("HΦ" $! rs_l rs). iModIntro. iFrame. iPureIntro. done. }
  wp_auto.
  iPoseProof (ReplicaSetStatusV.deepown_set_observed_generation _ _
    rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') with "Hstatus") as "#Hreq".
  set I := (∃ (i : w64) (cur_l : loc) (cur_phy : api_apps_v1.ReplicaSet.t) (cur : ReplicaSetV.t)
      (dqc : dfrac) (upd : loc) (uerr gerr : interface.t),
    "i" ∷ i_ptr ↦ i ∗
    "current" ∷ current_ptr ↦ cur_l ∗
    "updatedRS" ∷ updatedRS_ptr ↦ upd ∗
    "updateErr" ∷ updateErr_ptr ↦ uerr ∗
    "getErr" ∷ getErr_ptr ↦ gerr ∗
    "Hcur_l" ∷ cur_l ↦ cur_phy ∗
    "Hcur" ∷ ReplicaSetV.deepown cur_phy cur dqc ∗
    "%Hcur_valid" ∷ ⌜ ReplicaSetV.valid cur ⌝ ∗
    "%Hcur_meta" ∷ ⌜ ObjectMetaV.equiv_except_resource_version
      cur.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
    "%Hcur_spec" ∷ ⌜ cur.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
    "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq cur.(ReplicaSetV.ObjectMeta') ∗
    "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
    "Hstatus_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus cur.(ReplicaSetV.Status')) ∗
    "%Hi" ∷ ⌜ i = W64 0 ∨ i = W64 1 ⌝)%I.
  iAssert I with "[i current updatedRS updateErr getErr Hrs_l Hrs Hmeta Hspec Hstatus_frag]" as "Hloop".
  { iExists (W64 0), rs_l, rs_phy, rs, DfracDiscarded, null, interface.nil, interface.nil.
    iFrame. iPureIntro. split_and!; try done; by left. }
  wp_for "Hloop".
  iMod (ReplicaSetV.deepown_persist with "Hcur") as "Hcur".
  iDestruct "Hcur" as "(%Hcur_tm & #Hcur_meta_own & Hcur_spec_own & #Hcur_st)".
  wp_func_call. rewrite /context.TODOⁱᵐᵖˡ. wp_call.
  wp_pures.
  wp_load. wp_pures.
  wp_load. wp_pures.
  wp_load.
  (* The current object with the requested status, read-only from now on. *)
  iPersist "Hcur_l".
  iAssert (ReplicaSetV.deepown cur_phy cur DfracDiscarded)%I
    with "[Hcur_spec_own]" as "Hcur".
  { rewrite /ReplicaSetV.deepown. iFrame "∗ # %". }
  iAssert (ReplicaSetV.deepown_l cur_l
    (cur <| ReplicaSetV.Status' := status <| ReplicaSetStatusV.ObservedGeneration' :=
      rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') |> |>)
    DfracDiscarded)%I with "[Hcur]" as "Hinput".
  { iExists _. iFrame "Hcur_l". iApply (ReplicaSetV.deepown_set_status with "Hcur Hreq"). }
  destruct (ReplicaSetV.meta_equiv_key_uid _ _ Hcur_meta) as (Hkey_meta & Huid_meta & Hns_meta & Hname_meta).
  assert (ReplicaSetV.key rs = ReplicaSetV.key cur) as Hkey_cur.
  { rewrite /ReplicaSetV.key Hkey_meta. done. }
  iEval (rewrite Hkey_cur -Huid_meta) in "Hmeta".
  iEval (rewrite Hkey_cur -Huid_meta) in "Hstatus_frag".
  (* The spec fragment is not needed by the status write and stays framed. *)
  wp_apply (wp_ReplicaSetInterface__UpdateStatus γ l c
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') _ _ cur_l cur _ dq DfracDiscarded
    with "[$Hinput $Hmeta $Hstatus_frag]") --no-auto.
  { iFrame "#". iPureIntro. split_and!; [by rewrite Hns_meta|done|].
    rewrite ReplicaSetStatusV.valid_update_iff Hgen. done. }
  iIntros (result_l rs') "(%Hchanged & _ & Hmeta & Hstatus_frag & _ & _)".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hmeta".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hstatus_frag".
  destruct Hchanged as (Hmeta_changed & Hspec_changed).
  wp_auto. iApply wp_for_post_return. wp_auto.
  iApply ("HΦ" $! result_l rs'). rewrite Hspec_changed Hcur_spec. iModIntro. iFrame.
  iPureIntro. split.
  - rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_changed Hcur_meta |- *.
    congruence.
  - congruence.
Qed.

(* A variant of [wp_updateReplicaSetStatus] that does not require the requested
   status to pass validation. A rejected write is retried once after a GET, as
   upstream does, and the error is then returned. Either way the fragments
   describe some [rs'] that keeps [rs]'s metadata (up to resource version) and
   spec. *)
Lemma wp_updateReplicaSetStatus_general γ l c rs_l rs_phy rs status_c status dq :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclient" ∷ is_rs_client c rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hrs_l" ∷ rs_l ↦ rs_phy ∗
      "Hrs" ∷ ReplicaSetV.deepown rs_phy rs DfracDiscarded ∗
      "#Hstatus" ∷ ReplicaSetStatusV.deepown status_c status DfracDiscarded ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hstatus_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    @! replicaset.updateReplicaSetStatus #c #rs_l #status_c
  {{{ (result_l : loc) (err : interface.t) (rs' : ReplicaSetV.t), RET (#result_l, #err);
      ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ∧
        rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status'))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (⌜ rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') =
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') ⌝)%I as %Hgen.
  { iNamed "Hrs". iNamed "Hdeepown_objectmeta". done. }
  iApply wp_fupd.
  iPoseProof (ReplicaSetStatusV.terminating_rep with "Hstatus") as "#Hnew_term".
  iAssert (opt_ptr_rep rs_phy.(v1.ReplicaSet.Status').(api_apps_v1.ReplicaSetStatus.TerminatingReplicas')
    rs.(ReplicaSetV.Status').(ReplicaSetStatusV.TerminatingReplicas') DfracDiscarded)%I as "#Hold_term".
  { iDestruct "Hrs" as "(_ & _ & _ & Hst)". iApply (ReplicaSetStatusV.terminating_rep with "Hst"). }
  wp_auto.
  (* The no-op check evaluates to some boolean. *)
  wp_bind (if: _ then (let: "$a0" := _ in let: "$a1" := _ in
    FuncResolve goreflect.DeepEqual [] #() "$a0" "$a1") else #false)%E.
  iApply (wp_wand _ _ _ (λ v, ∃ b : bool, ⌜ v = #b ⌝ ∗
      "rs" ∷ rs_ptr ↦ rs_l ∗ "Hrs_l" ∷ rs_l ↦ rs_phy ∗
      "newStatus" ∷ newStatus_ptr ↦ status_c)%I with "[rs Hrs_l newStatus]").
  { repeat (split_bool; try wp_auto; try (iExists false; iFrame; done)).
    all: wp_apply (wp_Equal_int32 with "[]");
      [iSplitR; [iExact "Hold_term"|iExact "Hnew_term"]|].
    all: iIntros (r) "_".
    all: destruct r; try wp_auto; try (iExists false; iFrame; done).
    all: split_bool; try wp_auto; try (iExists false; iFrame; done).
    all: wp_apply wp_DeepEqual.
    all: iIntros (r) "_". all: iExists r; iFrame; done. }
  iIntros (v) "(%b & -> & rs & Hrs_l & newStatus)".
  destruct b.
  { (* already up to date: nothing is written *)
    wp_auto. iApply ("HΦ" $! rs_l interface.nil rs). iModIntro. iFrame. iPureIntro. done. }
  wp_auto.
  iPoseProof (ReplicaSetStatusV.deepown_set_observed_generation _ _
    rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') with "Hstatus") as "#Hreq".
  set I := (∃ (i : w64) (cur_l : loc) (cur_phy : api_apps_v1.ReplicaSet.t) (cur : ReplicaSetV.t)
      (dqc : dfrac) (upd : loc) (uerr gerr : interface.t),
    "i" ∷ i_ptr ↦ i ∗
    "current" ∷ current_ptr ↦ cur_l ∗
    "updatedRS" ∷ updatedRS_ptr ↦ upd ∗
    "updateErr" ∷ updateErr_ptr ↦ uerr ∗
    "getErr" ∷ getErr_ptr ↦ gerr ∗
    "Hcur_l" ∷ cur_l ↦ cur_phy ∗
    "Hcur" ∷ ReplicaSetV.deepown cur_phy cur dqc ∗
    "%Hcur_valid" ∷ ⌜ ReplicaSetV.valid cur ⌝ ∗
    "%Hcur_meta" ∷ ⌜ ObjectMetaV.equiv_except_resource_version
      cur.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
    "%Hcur_spec" ∷ ⌜ cur.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec') ⌝ ∗
    "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq cur.(ReplicaSetV.ObjectMeta') ∗
    "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
    "Hstatus_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus cur.(ReplicaSetV.Status')) ∗
    "%Hi" ∷ ⌜ i = W64 0 ∨ i = W64 1 ⌝)%I.
  iAssert I with "[i current updatedRS updateErr getErr Hrs_l Hrs Hmeta Hspec Hstatus_frag]" as "Hloop".
  { iExists (W64 0), rs_l, rs_phy, rs, DfracDiscarded, null, interface.nil, interface.nil.
    iFrame. iPureIntro. split_and!; try done; by left. }
  wp_for "Hloop".
  iMod (ReplicaSetV.deepown_persist with "Hcur") as "Hcur".
  iDestruct "Hcur" as "(%Hcur_tm & #Hcur_meta_own & Hcur_spec_own & #Hcur_st)".
  wp_func_call. rewrite /context.TODOⁱᵐᵖˡ. wp_call.
  wp_pures.
  wp_load. wp_pures.
  wp_load. wp_pures.
  wp_load.
  (* The current object with the requested status, read-only from now on. *)
  iPersist "Hcur_l".
  iAssert (ReplicaSetV.deepown cur_phy cur DfracDiscarded)%I
    with "[Hcur_spec_own]" as "Hcur".
  { rewrite /ReplicaSetV.deepown. iFrame "∗ # %". }
  iAssert (ReplicaSetV.deepown_l cur_l
    (cur <| ReplicaSetV.Status' := status <| ReplicaSetStatusV.ObservedGeneration' :=
      rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') |> |>)
    DfracDiscarded)%I with "[Hcur]" as "Hinput".
  { iExists _. iFrame "Hcur_l". iApply (ReplicaSetV.deepown_set_status with "Hcur Hreq"). }
  destruct (ReplicaSetV.meta_equiv_key_uid _ _ Hcur_meta) as (Hkey_meta & Huid_meta & Hns_meta & Hname_meta).
  assert (ReplicaSetV.key rs = ReplicaSetV.key cur) as Hkey_cur.
  { rewrite /ReplicaSetV.key Hkey_meta. done. }
  iEval (rewrite Hkey_cur -Huid_meta) in "Hmeta".
  iEval (rewrite Hkey_cur -Huid_meta) in "Hstatus_frag".
  (* The spec fragment is not needed by the status write and stays framed. *)
  wp_apply (wp_ReplicaSetInterface__UpdateStatus_general γ l c
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') _ _ cur_l cur _ dq DfracDiscarded
    with "[$Hinput $Hmeta $Hstatus_frag]") --no-auto.
  { iFrame "#". iPureIntro. done. }
  iIntros (result_l werr rs') "(%Hchanged & _ & Hmeta & Hstatus_frag & %Hvalid_rs')".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hmeta".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hstatus_frag".
  destruct Hchanged as (Hmeta_changed & Hspec_changed).
  assert (ObjectMetaV.equiv_except_resource_version
    rs'.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta')) as Hmeta_rs'.
  { rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_changed Hcur_meta |- *.
    congruence. }
  assert (rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec')) as Hspec_rs'.
  { congruence. }
  destruct werr as [werr_ok|].
  2: {
    (* The write succeeded. *)
    wp_auto. iApply wp_for_post_return. wp_auto.
    iApply ("HΦ" $! result_l interface.nil rs'). rewrite Hspec_rs'. iModIntro. iFrame. done. }
  destruct Hi as [-> | ->].
  2: {
    (* The retry was rejected too: its error is returned. *)
    wp_auto. wp_for_post.
    iApply ("HΦ" $! null (interface.ok werr_ok) rs'). rewrite Hspec_rs'. iModIntro. iFrame. done. }
  (* The first write was rejected: re-read the ReplicaSet and retry. *)
  iAssert (⌜ cur_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') =
    cur.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝)%I as %Hcur_name.
  { iNamed "Hcur_meta_own". iNamed "Hdeepown_objectmeta". done. }
  wp_auto.
  wp_func_call. rewrite /context.TODOⁱᵐᵖˡ. wp_call.
  wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load.
  wp_apply (wp_ReplicaSetInterface__Get γ l c (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') _ _ _
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq 1 rs'.(ReplicaSetV.ObjectMeta')
    rs.(ReplicaSetV.Spec') rs'.(ReplicaSetV.Status')
    with "[$Hmeta $Hspec $Hstatus_frag]") --no-auto.
  { iFrame "#". iPureIntro. rewrite Hcur_name Hname_meta. done. }
  iIntros (new_l new) "Hget". iNamed "Hget".
  iDestruct "Hdeepown_l" as (new_phy) "[Hnew_l Hnew]".
  iPoseProof (kview.own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
    as "Hown_meta_frag".
  iEval (rewrite Hstatus_eq) in "Hown_status_frag".
  wp_auto. wp_for_post.
  iFrame "HΦ c rs newStatus updateOptions getOptions". rewrite /named.
  iExists (word.add (W64 0) (W64 1)), new_l, new_phy, new, (DfracOwn 1).
  iFrame. iPureIntro. split_and!; try done.
  - rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_eq Hmeta_rs' |- *.
    congruence.
  - by right.
Qed.

(* After [updateReplicaSetStatus], the owned resources describe the stored
   ReplicaSet: [rs'] (from the status write) with [rs]'s TypeMeta, which no
   fragment tracks. [rs_get] is the ReplicaSet the sync read; the ReplicaSet's
   own fragments are keyed by it, the children fragments by [rs]. *)
Lemma owned_resources_after_status_update γ rs rs_get rs' pods fractions (ready : bool) :
  ReplicaSetV.key rs = ReplicaSetV.key rs_get →
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') = rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') →
  ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') rs_get.(ReplicaSetV.ObjectMeta') →
  NoDup (PodV.key <$> pods) →
  Z.of_nat (length pods) < 2 ^ 31 →
  own_meta_frag γ (ReplicaSetV.key rs_get) rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
    fractions.(rs_dq) rs'.(ReplicaSetV.ObjectMeta') -∗
  own_spec_frag γ (ReplicaSetV.key rs_get) rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
    fractions.(rs_dq) (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) -∗
  own_status_frag γ (ReplicaSetV.key rs_get) rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
    fractions.(rs_status_dq) (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) -∗
  ([∗ list] pod ∈ pods, own_meta_frag γ (PodV.key pod)
    pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq) pod.(PodV.ObjectMeta')) -∗
  ([∗ list] pod ∈ pods, own_unreserved_key_frag γ (PodV.key pod)) -∗
  own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
    fractions.(children_dq) (list_to_set (PodV.key <$> pods)) -∗
  (if ready then
     own_terminating_children_frag γ (ReplicaSetV.key rs)
       rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 0%nat
   else
     ∃ terminating_bound, own_terminating_children_frag γ (ReplicaSetV.key rs)
       rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound) -∗
  owned_resources γ (rs' <| ReplicaSetV.TypeMeta' := rs.(ReplicaSetV.TypeMeta') |>) pods fractions ready.
Proof.
  intros Hrs_key_eq Hrs_uid_eq Hmeta_changed Hnodup Hbound.
  iIntros "Hmeta Hspec Hstatus Hpods #Hunreserved Hchildren Hterminating".
  destruct (ReplicaSetV.meta_equiv_key_uid _ _ Hmeta_changed) as (Hkey' & Huid' & _ & _).
  assert (ReplicaSetV.key (rs' <| ReplicaSetV.TypeMeta' := rs.(ReplicaSetV.TypeMeta') |>) =
    ReplicaSetV.key rs_get) as Hkey''.
  { rewrite /ReplicaSetV.key /=. exact Hkey'. }
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hchildren Hterminating".
  rewrite /owned_resources /= Hkey'' Huid'.
  iFrame "∗ #". iPureIntro. split; [exact Hnodup|exact Hbound].
Qed.

End proof.
