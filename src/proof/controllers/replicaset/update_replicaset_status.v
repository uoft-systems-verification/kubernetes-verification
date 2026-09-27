From New.proof Require Import prelude empty_ffi wp_helpers.
From New.proof.controllers.replicaset Require Export replicaset_client external_specs calculate_status.

Module ptrpkg := code.k8s_io.utils.ptr.ptr.

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

(* An optional [*int32]: a readable cell or nil. *)
Definition opt_ptr_rep (p : loc) (o : option w32) dq : iProp Σ :=
  match o with
  | Some n => p ↦{dq} n
  | None => ⌜ p = null ⌝
  end.

#[global] Instance opt_ptr_rep_persistent p o : Persistent (opt_ptr_rep p o DfracDiscarded).
Proof. rewrite /opt_ptr_rep. destruct o; apply _. Qed.

Lemma wp_ptr_Equal_int32 (a b : loc) oa ob dqa dqb :
  {{{ opt_ptr_rep a oa dqa ∗ opt_ptr_rep b ob dqb }}}
    #(functions ptrpkg.Equal [go.int32]) #a #b
  {{{ (r : bool), RET #r; opt_ptr_rep a oa dqa ∗ opt_ptr_rep b ob dqb }}}.
Proof.
  iIntros (Φ) "[Ha Hb] HΦ".
  wp_func_call. rewrite /ptrpkg.Equalⁱᵐᵖˡ. wp_call. wp_auto.
  destruct oa as [na|]; destruct ob as [nb|]; rewrite /opt_ptr_rep.
  - iDestruct (typed_pointsto_not_null with "Ha") as %Ha.
    iDestruct (typed_pointsto_not_null with "Hb") as %Hb.
    rewrite (bool_decide_false (a = null)) // (bool_decide_false (b = null)) //.
    wp_auto. rewrite (bool_decide_false (a = null)) //. wp_auto. iApply "HΦ". iFrame.
  - iDestruct "Hb" as %->. iDestruct (typed_pointsto_not_null with "Ha") as %Ha.
    rewrite (bool_decide_false (a = null)) // (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". iFrame. done.
  - iDestruct "Ha" as %->. iDestruct (typed_pointsto_not_null with "Hb") as %Hb.
    rewrite (bool_decide_false (b = null)) // (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". iFrame. done.
  - iDestruct "Ha" as %->. iDestruct "Hb" as %->.
    rewrite (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". done.
Qed.

Lemma status_terminating_rep (sc : api_apps_v1.ReplicaSetStatus.t) (st : ReplicaSetStatusV.t) :
  ReplicaSetStatusV.deepown sc st DfracDiscarded ⊢
  opt_ptr_rep sc.(api_apps_v1.ReplicaSetStatus.TerminatingReplicas')
    st.(ReplicaSetStatusV.TerminatingReplicas') DfracDiscarded.
Proof.
  rewrite /ReplicaSetStatusV.deepown /opt_ptr_rep. iIntros "H". iNamed "H".
  destruct (st.(ReplicaSetStatusV.TerminatingReplicas')); first done.
  iPureIntro. by apply Hdeepown_terminatingreplicas_none.
Qed.

Lemma status_deepown_observed_generation (sc : api_apps_v1.ReplicaSetStatus.t)
    (st : ReplicaSetStatusV.t) (g : w64) dq :
  ReplicaSetStatusV.deepown sc st dq ⊢
  ReplicaSetStatusV.deepown (sc <| api_apps_v1.ReplicaSetStatus.ObservedGeneration' := g |>)
    (st <| ReplicaSetStatusV.ObservedGeneration' := g |>) dq.
Proof. rewrite /ReplicaSetStatusV.deepown. iIntros "H". iNamed "H". simpl. iFrame "∗ %". done. Qed.

Lemma replicaset_deepown_set_status (c : api_apps_v1.ReplicaSet.t) (v : ReplicaSetV.t)
    (sc : api_apps_v1.ReplicaSetStatus.t) (st : ReplicaSetStatusV.t) dq :
  ReplicaSetV.deepown c v dq -∗ ReplicaSetStatusV.deepown sc st dq -∗
  ReplicaSetV.deepown (c <| api_apps_v1.ReplicaSet.Status' := sc |>)
    (v <| ReplicaSetV.Status' := st |>) dq.
Proof.
  rewrite /ReplicaSetV.deepown. iIntros "H Hst". iNamed "H". simpl. iFrame "∗ %".
Qed.

Lemma meta_equiv_key_uid (m1 m2 : ObjectMetaV.t) :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  ReplicaSetV.meta_key m1 = ReplicaSetV.meta_key m2 ∧
  m1.(ObjectMetaV.UID') = m2.(ObjectMetaV.UID') ∧
  m1.(ObjectMetaV.Namespace') = m2.(ObjectMetaV.Namespace') ∧
  m1.(ObjectMetaV.Name') = m2.(ObjectMetaV.Name').
Proof.
  rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version.
  destruct m1, m2; simpl. intros Heq. inversion Heq; subst. done.
Qed.

Lemma meta_frag_equiv {γ k uid dq meta1 meta2} :
  ObjectMetaV.equiv_except_resource_version meta1 meta2 →
  own_meta_frag γ k uid dq meta2 -∗ own_meta_frag γ k uid dq meta1.
Proof.
  iIntros (Hmeta_eq) "Hown_meta".
  assert (kview.mk_meta_frag k uid dq meta1 = kview.mk_meta_frag k uid dq meta2) as Hfrag_eq.
  { rewrite /kview.mk_meta_frag /ObjectMetaV.equiv_except_resource_version in Hmeta_eq |- *.
    rewrite Hmeta_eq. done. }
  rewrite /own_meta_frag /kview.own_meta_frag Hfrag_eq. iExact "Hown_meta".
Qed.

(* [updateReplicaSetStatus] writes the requested status (with the observed
   generation set), retrying once after a GET. Every outcome keeps the stored
   metadata (up to resource version) and spec; the status fragment follows the
   stored status. *)
Lemma wp_updateReplicaSetStatus γ l c rs_l rs_phy rs status_c status dq :
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
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      ⌜ err ≠ interface.nil →
        ¬ ReplicaSetStatusV.valid (status <| ReplicaSetStatusV.ObservedGeneration' :=
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') |>) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (⌜ rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') =
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') ⌝)%I as %Hgen.
  { iNamed "Hrs". iNamed "Hdeepown_objectmeta". done. }
  iApply wp_fupd.
  iPoseProof (status_terminating_rep with "Hstatus") as "#Hnew_term".
  iAssert (opt_ptr_rep rs_phy.(v1.ReplicaSet.Status').(api_apps_v1.ReplicaSetStatus.TerminatingReplicas')
    rs.(ReplicaSetV.Status').(ReplicaSetStatusV.TerminatingReplicas') DfracDiscarded)%I as "#Hold_term".
  { iDestruct "Hrs" as "(_ & _ & _ & Hst)". iApply (status_terminating_rep with "Hst"). }
  Timeout 120 wp_auto.
  (* The no-op check evaluates to some boolean. *)
  wp_bind (if: _ then (let: "$a0" := _ in let: "$a1" := _ in
    FuncResolve goreflect.DeepEqual [] #() "$a0" "$a1") else #false)%E.
  iApply (wp_wand _ _ _ (λ v, ∃ b : bool, ⌜ v = #b ⌝ ∗
      "rs" ∷ rs_ptr ↦ rs_l ∗ "Hrs_l" ∷ rs_l ↦ rs_phy ∗
      "newStatus" ∷ newStatus_ptr ↦ status_c)%I with "[rs Hrs_l newStatus]").
  { Timeout 60 (repeat (split_bool; try wp_auto; try (iExists false; iFrame; done))).
    all: wp_apply (wp_ptr_Equal_int32 with "[]");
      [iSplitR; [iExact "Hold_term"|iExact "Hnew_term"]|].
    all: iIntros (r) "_".
    all: destruct r; try wp_auto; try (iExists false; iFrame; done).
    all: split_bool; try wp_auto; try (iExists false; iFrame; done).
    all: wp_apply wp_reflect_DeepEqual.
    all: iIntros (r) "_". all: iExists r; iFrame; done. }
  iIntros (v) "(%b & -> & rs & Hrs_l & newStatus)".
  destruct b.
  { (* already up to date: nothing is written *)
    wp_auto. iApply ("HΦ" $! rs_l interface.nil rs). iModIntro. iFrame. iPureIntro. split; [done|by intros]. }
  Timeout 120 wp_auto.
  iPoseProof (status_deepown_observed_generation _ _
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
  Timeout 60 wp_pures.
  wp_load. Timeout 60 wp_pures. wp_load. Timeout 60 wp_pures. wp_load.
  (* The current object with the requested status, read-only from now on. *)
  iPersist "Hcur_l".
  iAssert (ReplicaSetV.deepown cur_phy cur DfracDiscarded)%I
    with "[Hcur_spec_own]" as "Hcur".
  { rewrite /ReplicaSetV.deepown. iFrame "∗ # %". }
  iAssert (ReplicaSetV.deepown_l cur_l
    (cur <| ReplicaSetV.Status' := status <| ReplicaSetStatusV.ObservedGeneration' :=
      rs_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Generation') |> |>)
    DfracDiscarded)%I with "[Hcur]" as "Hinput".
  { iExists _. iFrame "Hcur_l". iApply (replicaset_deepown_set_status with "Hcur Hreq"). }
  destruct (meta_equiv_key_uid _ _ Hcur_meta) as (Hkey_meta & Huid_meta & Hns_meta & Hname_meta).
  assert (ReplicaSetV.key rs = ReplicaSetV.key cur) as Hkey_cur.
  { rewrite /ReplicaSetV.key Hkey_meta. done. }
  iEval (rewrite Hkey_cur -Huid_meta) in "Hmeta".
  iEval (rewrite Hkey_cur -Huid_meta -Hcur_spec) in "Hspec".
  iEval (rewrite Hkey_cur -Huid_meta) in "Hstatus_frag".
  wp_apply (wp_ReplicaSetInterface__UpdateStatus γ l c
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') _ _ cur_l cur _ dq DfracDiscarded
    with "[$Hinput $Hmeta $Hspec $Hstatus_frag]") --no-auto.
  { iFrame "#". iPureIntro. split; [by rewrite Hns_meta|done]. }
  iIntros (result_l rs' uerr') "(%Hchanged & _ & Hmeta & Hspec & Hstatus_frag & Hresult)".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hmeta".
  iEval (rewrite -Hkey_cur Huid_meta Hcur_spec) in "Hspec".
  iEval (rewrite -Hkey_cur Huid_meta) in "Hstatus_frag".
  destruct Hchanged as (_ & Hmeta_changed & Hspec_changed).
  iDestruct "Hresult" as "[(-> & _ & _ & _) | %Hfailed]".
  { (* success *)
    wp_auto. iApply wp_for_post_return. wp_auto.
    iApply ("HΦ" $! result_l interface.nil rs'). iModIntro. iFrame.
    iPureIntro. split_and!.
    - rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_changed Hcur_meta |- *.
      congruence.
    - congruence.
    - by intros. }
  destruct Hfailed as (Herr_ne & -> & -> & Hinvalid).
  rewrite Hgen in Hinvalid.
  destruct uerr' as [uerr_ok|]; [|done].
  Timeout 120 wp_auto.
  destruct Hi as [-> | ->].
  2: { (* the retry also failed: give up *)
    Timeout 120 wp_auto. iApply wp_for_post_break. Timeout 120 wp_auto.
    iApply ("HΦ" $! null (interface.ok uerr_ok) cur). iModIntro. iFrame. iPureIntro.
    split; [done|by intros]. }
  Timeout 120 wp_auto.
  wp_func_call. rewrite /context.TODOⁱᵐᵖˡ. wp_call.
  Timeout 60 wp_pures. wp_load. Timeout 60 wp_pures. wp_load.
  Timeout 60 wp_pures. wp_load. Timeout 60 wp_pures. wp_load.
  iAssert (⌜ cur_phy.(api_apps_v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') =
    cur.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝)%I as %Hname_phy.
  { iDestruct "Hcur_meta_own" as "Hcm". rewrite /named /ObjectMetaV.deepown.
    iDestruct "Hcm" as "(%Hn & _)". done. }
  wp_apply (wp_ReplicaSetInterface__Get γ l c rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') _ _
    (v1.ObjectMeta.Name' (v1.ReplicaSet.ObjectMeta' cur_phy))
    (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (DfracOwn 1)
    cur.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.Spec') cur.(ReplicaSetV.Status')
    with "[$Hmeta $Hspec $Hstatus_frag]") --no-auto.
  { iFrame "#". iPureIntro. rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hname_phy Hname_meta. done. }
  iIntros (rs2_l rs2) "H". iNamed "H".
  iDestruct "Hdeepown_l" as (rs2_phy) "[Hrs2_l Hrs2]".
  Timeout 120 wp_auto.
  iApply wp_for_post_do. Timeout 120 wp_auto.
  iAssert I with "[i current updatedRS updateErr getErr Hrs2_l Hrs2 Hown_meta_frag Hown_spec_frag
      Hown_status_frag]" as "Hloop".
  { iExists (word.add (W64 0) (W64 1)), rs2_l, rs2_phy, rs2, (DfracOwn 1), null, (interface.ok uerr_ok),
      interface.nil.
    iFrame "i current updatedRS updateErr getErr Hrs2_l Hrs2".
    simpl in Hvalid'.
    iSplit; first done.
    iSplit.
    { iPureIntro. rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_eq Hcur_meta |- *.
      congruence. }
    iSplit; first (iPureIntro; congruence).
    iSplitL "Hown_meta_frag"; first (iApply (meta_frag_equiv with "Hown_meta_frag"); done).
    iSplitL "Hown_spec_frag"; first done.
    iSplitL "Hown_status_frag"; first (rewrite Hstatus_eq; done).
    iPureIntro. right. word. }
  iFrame.
Qed.

End proof.
