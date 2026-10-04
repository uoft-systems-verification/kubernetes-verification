From New.proof Require Import prelude empty_ffi.
(* Imported before the controller's package so that [replicaset] below names
   controllers/replicaset, not the upstream package of the same name. *)
From New.proof.k8s_io.kubernetes.pkg.controller Require Import replicaset.
From New.proof.controllers.replicaset Require Export replicaset_init external_specs.
From New.proof.k8s_io.apimachinery.pkg Require Import labels_validated_set.
From New.proof.k8s_io.kubernetes.pkg.api.v1 Require Import pod.
From New.proof.kubernetes_types Require Export prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
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
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Local Set Default Proof Using "All".

(* Borrow the label set of an object's metadata as a [labels_set_rep]. *)
Lemma objectmeta_labels_rep (c : v1.ObjectMeta.t) (m : ObjectMetaV.t) dq :
  ObjectMetaV.deepown c m dq ⊢
    labels_set_rep c.(v1.ObjectMeta.Labels') m.(ObjectMetaV.Labels') dq ∗
    (labels_set_rep c.(v1.ObjectMeta.Labels') m.(ObjectMetaV.Labels') dq -∗
      ObjectMetaV.deepown c m dq).
Proof.
  rewrite /ObjectMetaV.deepown. iIntros "H". iNamed "H".
  iSplitL "Hdeepown_labels_some".
  - rewrite /labels_set_rep. iSplit; first done.
    destruct (m.(ObjectMetaV.Labels')); last done.
    iDestruct "Hdeepown_labels_some" as (cl) "[H ->]". iExact "H".
  - iIntros "[_ Hl]". iFrame "∗ %".
    destruct (m.(ObjectMetaV.Labels')); last done.
    iExists _. iFrame. done.
Qed.

(* The status returned by [calculateStatus]: the counts and terminating
   pointer are replaced, observed generation and conditions are kept. *)
Lemma status_deepown_counts (sc : api_apps_v1.ReplicaSetStatus.t) (st : ReplicaSetStatusV.t)
    r f rd av (tptr : loc) (topt : option w32) :
  ReplicaSetStatusV.deepown sc st DfracDiscarded -∗
  (match topt with Some n => tptr ↦□ n | None => ⌜ tptr = null ⌝ end) -∗
  ReplicaSetStatusV.deepown
    (api_apps_v1.ReplicaSetStatus.mk r f rd av tptr
      sc.(api_apps_v1.ReplicaSetStatus.ObservedGeneration')
      sc.(api_apps_v1.ReplicaSetStatus.Conditions'))
    (ReplicaSetStatusV.mk r f rd av topt
      st.(ReplicaSetStatusV.ObservedGeneration') st.(ReplicaSetStatusV.Conditions'))
    DfracDiscarded.
Proof.
  rewrite /ReplicaSetStatusV.deepown. iIntros "H Ht". iNamed "H". simpl.
  iFrame "# %". destruct topt as [n|]; simpl.
  - iDestruct (typed_pointsto_not_null with "Ht") as %Hnn.
    iFrame "Ht Hdeepown_conditions_some". iPureIntro.
    split_and!; done.
  - iDestruct "Ht" as %->. iFrame "Hdeepown_conditions_some". iPureIntro.
    split_and!; done.
Qed.

(* Contract for the management-success path used by the top-level proofs.
   Nested ownership becomes read-only because Go's status struct copy can share
   the old condition slice with the returned status. Keep exclusive ownership of
   the ReplicaSet struct so its Status field can subsequently be replaced.

   If both pod lists have fewer than 2^31 elements, the returned counts are
   valid once any non-negative observed generation is filled in (as
   updateReplicaSetStatus does). The bound is needed because calculateStatus
   converts the counts, which are Go ints, to int32, and a count of 2^31 or
   more would wrap to a negative value that the API server rejects. The
   nesting of the counts (available ≤ ready ≤ replicas, fully labeled ≤
   replicas) follows from the loop itself, whatever the readiness and
   availability helpers return. *)
Lemma wp_calculateStatus_no_manage_error rs_l rs_phy rs active_sl active_ptrs active_pods
    terminating_sl (terminating_ptrs : list loc) dq
    (controller_features : replicaset.ReplicaSetControllerFeatures.t) (now : time.Time.t) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      ⌜ ReplicaSetV.valid rs ⌝ ∗
      ⌜ Z.of_nat (size (default ∅
          rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))
          ≤ 2 ^ 63 - 1 ⌝ ∗
      rs_l ↦ rs_phy ∗
      ReplicaSetV.deepown rs_phy rs 1 ∗
      active_sl ↦* active_ptrs ∗
      ([∗ list] ptr;pod ∈ active_ptrs;active_pods, PodV.deepown_l ptr pod dq) ∗
      terminating_sl ↦* terminating_ptrs
  }}}
    @! replicaset.calculateStatus #rs_l #active_sl #terminating_sl #interface.nil #controller_features #now
  {{{ (status_c : api_apps_v1.ReplicaSetStatus.t) (status : ReplicaSetStatusV.t), RET #status_c;
      rs_l ↦ rs_phy ∗
      ReplicaSetV.deepown rs_phy rs DfracDiscarded ∗
      ReplicaSetStatusV.deepown status_c status DfracDiscarded ∗
      active_sl ↦* active_ptrs ∗
      ([∗ list] ptr;pod ∈ active_ptrs;active_pods, PodV.deepown_l ptr pod dq) ∗
      terminating_sl ↦* terminating_ptrs ∗
      ⌜ status.(ReplicaSetStatusV.Replicas') = W32 (length active_pods) ⌝ ∗
      ⌜ status.(ReplicaSetStatusV.ObservedGeneration') =
        rs.(ReplicaSetV.Status').(ReplicaSetStatusV.ObservedGeneration') ⌝ ∗
      ⌜ Z.of_nat (length active_pods) < 2 ^ 31 → Z.of_nat (length terminating_ptrs) < 2 ^ 31 →
        ∀ g : w64, 0 ≤ sint.Z g →
        ReplicaSetStatusV.valid (status <| ReplicaSetStatusV.ObservedGeneration' := g |>) ⌝
  }}}.
Proof.
  wp_start as "(%Hvalid & %Hbound & Hrs_l & Hrs & Hactive_sl & Hpods & Hterm_sl)".
  iDestruct (own_slice_len with "Hterm_sl") as %(Hterm_len1 & Hterm_len2).
  iApply wp_fupd.
  iMod (ReplicaSetV.deepown_persist with "Hrs") as "Hrs".
  rewrite {1}/ReplicaSetV.deepown. iNamed "Hrs".
  iNamedPrefix "Hdeepown_spec" "Hspec_".
  iRename "Hdeepown_objectmeta" into "Hrs_meta".
  iRename "Hdeepown_status" into "Hrs_status".
  iDestruct "Hrs_status" as "#Hrs_status".
  iDestruct "Hrs_meta" as "#Hrs_meta".
  iDestruct "Hspec_Hdeepown_template" as "#Htemplate".
  iAssert (labels_set_rep
      rs_phy.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Template').(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels')
      rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
      DfracDiscarded)%I as "#Htpl_labels".
  { iDestruct "Htemplate" as "[Htmeta _]".
    iDestruct (objectmeta_labels_rep with "Htmeta") as "[$ _]". }
  wp_auto.
  wp_apply (wp_Set__AsSelectorPreValidated _ _ _ Hbound with "[$Htpl_labels]").
  iIntros (selector) "[_ #Hselector]".
  wp_auto.
  iDestruct (own_slice_len with "Hactive_sl") as %(Hactive_len1 & Hactive_len2).
  iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
  set I := (∃ (i : w64) (p : loc) (fl rd av : w64),
    "i" ∷ i_ptr ↦ i ∗
    "pod" ∷ pod_ptr ↦ p ∗
    "fullyLabeledReplicasCount" ∷ fullyLabeledReplicasCount_ptr ↦ fl ∗
    "readyReplicasCount" ∷ readyReplicasCount_ptr ↦ rd ∗
    "availableReplicasCount" ∷ availableReplicasCount_ptr ↦ av ∗
    "Hactive_sl" ∷ active_sl ↦* active_ptrs ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ active_ptrs;active_pods, PodV.deepown_l ptr pod dq) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len active_sl) ⌝ ∗
    (* Each pod adds at most one to each count, and only ready pods count as
       available. *)
    "%Hcounts" ∷ ⌜ 0 ≤ sint.Z av ≤ sint.Z rd ∧ sint.Z rd ≤ sint.Z i ∧ 0 ≤ sint.Z fl ≤ sint.Z i ⌝)%I.
  iAssert I with "[i pod fullyLabeledReplicasCount readyReplicasCount availableReplicasCount
      Hactive_sl Hpods]" as "Hloop".
  { iExists (W64 0), null, _, _, _. iFrame. iPureIntro. split_and!; word. }
  wp_for "Hloop".
  wp_if_destruct.
  - list_elem active_ptrs (sint.Z i) as this_ptr.
    assert (∃ this_pod, active_pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod].
    { apply lookup_lt_is_Some_2. rewrite -Hpods_len.
      apply (lookup_lt_Some _ _ _ Hthis_ptr_lookup). }
    rewrite decide_True; first (pose proof (lookup_lt_Some _ _ _ Hthis_ptr_lookup); word).
    wp_apply (wp_load_slice_index with "[$Hactive_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hactive_sl". wp_auto.
    iDestruct (big_sepL2_lookup_acc with "Hpods") as "[Hthis Hpods]";
      [exact Hthis_ptr_lookup|exact Hthis_pod|].
    iDestruct "Hthis" as (pod_c) "[Hthis_l Hthis]".
    iNamedPrefix "Hthis" "Hp_".
    iDestruct (objectmeta_labels_rep with "Hp_Hdeepown_objectmeta") as "[Hpod_labels Hrestore]".
    wp_auto.
    wp_bind ((match selector with
      | interface.ok selector_i =>
          Val (#(methods selector_i.(interface.ty) "Matches" selector_i.(interface.v)))
      | interface.nil => Panic "nil interface"
      end)
      #(interface.ok (interface.mk labels.Set'
        #(v1.ObjectMeta.Labels' (v1.Pod.ObjectMeta' pod_c)))))%E.
    iApply (wp_Selector__Matches_resolved selector _
      (v1.ObjectMeta.Labels' (v1.Pod.ObjectMeta' pod_c))
      this_pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') dq
      with "[$Hselector $Hpod_labels]").
    iNext. iIntros (b) "(_ & Hpod_labels & _)".
    iDestruct ("Hrestore" with "Hpod_labels") as "Hp_Hdeepown_objectmeta".
    iAssert (PodV.deepown_l this_ptr this_pod dq)
      with "[Hthis_l Hp_Hdeepown_objectmeta Hp_Hdeepown_podspec Hp_Hdeepown_podstatus]" as "Hthis".
    { iExists pod_c. iFrame. rewrite /PodV.deepown. iFrame "∗ %". }
    wp_if_destruct; try wp_auto.
    all: wp_apply (wp_IsPodReady with "[$Hthis]").
    all: iIntros "Hthis".
    all: destruct (PodStatusV.ready this_pod.(PodV.Status')); try wp_auto.
    all: try (wp_apply (wp_IsPodAvailable with "[$Hthis]"); iIntros (avail) "Hthis";
      destruct avail; try wp_auto).
    all: iDestruct ("Hpods" with "Hthis") as "Hpods".
    all: iApply wp_for_post_do; wp_auto.
    all: iAssert I with "[i pod fullyLabeledReplicasCount readyReplicasCount availableReplicasCount
        Hactive_sl Hpods]" as "Hloop";
      [iExists (word.add i (W64 1)), this_ptr, _, _, _; iFrame; iPureIntro;
       pose proof (lookup_lt_Some _ _ _ Hthis_ptr_lookup); split_and!; word|].
    all: iFrame.
  - try wp_auto.
    wp_bind (MethodResolve featuregate.FeatureGate "Enabled"%go
      (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) _)%E.
    iApply wp_DefaultFeatureGate_Enabled; first done.
    iNext. iIntros (gate) "_".
    destruct gate; try wp_auto.
    all: destruct (replicaset.ReplicaSetControllerFeatures.EnableStatusTerminatingReplicas'
      controller_features) eqn:Hflag; try wp_auto.
    all: try (wp_func_call; rewrite /code.k8s_io.utils.ptr.ptr.Toⁱᵐᵖˡ; wp_call; wp_auto).
    all: wp_apply (wp_GetCondition with "[$Hrs_status]").
    all: iIntros (fc) "%Hfc".
    all: wp_auto.
    all: destruct (bool_decide (fc = null)) eqn:Hfc_null; simpl; try wp_auto.
    all: try (wp_apply (wp_RemoveCondition with "[$newStatus $Hrs_status]");
      iIntros (status_c') "[newStatus #Hrs_status']"; wp_auto).
    all: try iPersist "v".
    all: iModIntro.
    all: iAssert (ReplicaSetV.deepown rs_phy rs DfracDiscarded)
      with "[Hspec_Hdeepown_replicas_some Hspec_Hdeepown_selector_some]" as "Hrs".
    all: try (rewrite /ReplicaSetV.deepown /ReplicaSetSpecV.deepown; iFrame "∗ # %"; done).
    all: iApply "HΦ"; iFrame "Hrs_l Hrs Hactive_sl Hpods Hterm_sl".
    all: iSplitR; [first
      [ iApply (status_deepown_counts _ _ _ _ _ _ _ (Some _) with "Hrs_status' v")
      | iApply (status_deepown_counts _ _ _ _ _ _ _ (Some _) with "Hrs_status v")
      | iApply (status_deepown_counts _ _ _ _ _ _ _ None with "Hrs_status' []"); done
      | iApply (status_deepown_counts _ _ _ _ _ _ _ None with "Hrs_status []"); done ]|].
    all: iPureIntro; simpl.
    all: split_and!; [rewrite -Hpods_len Hactive_len1; word|done|].
    (* Every count fits in int32, so the conversions keep them non-negative and
       nested as the loop invariant states. *)
    all: intros Hactive_bound Hterm_bound g Hg.
    all: rewrite -Hpods_len Hactive_len1 in Hactive_bound; rewrite Hterm_len1 in Hterm_bound.
    all: rewrite /ReplicaSetStatusV.valid /=.
    all: split_and!; try done; word.
Qed.

End proof.
