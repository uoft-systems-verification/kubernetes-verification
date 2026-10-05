From New.proof Require Import prelude empty_ffi.
(* Imported before the controller's package so that [replicaset] below names
   controllers/replicaset, not the upstream package of the same name. *)
From New.proof.k8s_io.kubernetes.pkg.controller Require Import replicaset.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.k8s_io.apiserver.pkg.util Require Export feature.
From New.proof.k8s_io.apimachinery.pkg Require Import labels_validated_set.
From New.proof.k8s_io.utils Require Import ptr.
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
    (controller_features : upstreamrs.ReplicaSetControllerFeatures.t) (now : time.Time.t) :
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
  (* Arguments and [newStatus := rs.Status]. *)
  wp_alloc now_ptr as "now". wp_pures.
  wp_alloc controllerFeatures_ptr as "controllerFeatures". wp_pures.
  wp_alloc manageReplicasErr_ptr as "manageReplicasErr". wp_pures.
  wp_alloc terminatingPods_ptr as "terminatingPods". wp_pures.
  wp_alloc activePods_ptr as "activePods". wp_pures.
  wp_alloc rs_ptr as "rs". wp_pures.
  wp_alloc newStatus_ptr as "newStatus". wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures.
  (* The three counters start at zero. *)
  wp_alloc fullyLabeledReplicasCount_ptr as "fullyLabeledReplicasCount". wp_pures.
  wp_store. wp_pures.
  wp_alloc readyReplicasCount_ptr as "readyReplicasCount". wp_pures.
  wp_store. wp_pures.
  wp_alloc availableReplicasCount_ptr as "availableReplicasCount". wp_pures.
  wp_store. wp_pures.
  (* templateLabel := labels.Set(rs.Spec.Template.Labels).AsSelectorPreValidated() *)
  wp_alloc templateLabel_ptr as "templateLabel". wp_pures.
  wp_load. wp_pures. wp_load. wp_pures.
  wp_apply (wp_Set__AsSelectorPreValidated _ _ _ Hbound with "[$Htpl_labels]").
  iIntros (selector) "[_ #Hselector]".
  wp_pures. wp_store. wp_pures.
  (* for _, pod := range activePods *)
  wp_load. wp_pures. wp_alloc pod_ptr as "pod". wp_pures.
  wp_alloc i_ptr as "i". wp_pures.
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
  loop.wp_for_core. iNamed "Hloop".
  wp_pures. wp_load. wp_pures.
  destruct (bool_decide_reflect (sint.Z i < sint.Z (slice.len active_sl))) as [Hlt|Hge].
  - rewrite decide_True //.
    wp_pures. wp_load. wp_pures.
    list_elem active_ptrs (sint.Z i) as this_ptr.
    assert (∃ this_pod, active_pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod].
    { apply lookup_lt_is_Some_2. rewrite -Hpods_len.
      apply (lookup_lt_Some _ _ _ Hthis_ptr_lookup). }
    rewrite decide_True; first (pose proof (lookup_lt_Some _ _ _ Hthis_ptr_lookup); word).
    wp_apply (wp_load_slice_index with "[$Hactive_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hactive_sl". wp_pures. wp_load. wp_pures.
    (* pod := activePods[i] *)
    wp_store. wp_pures.
    iDestruct (big_sepL2_lookup_acc with "Hpods") as "[Hthis Hpods]";
      [exact Hthis_ptr_lookup|exact Hthis_pod|].
    iDestruct "Hthis" as (pod_c) "[Hthis_l Hthis]".
    iNamedPrefix "Hthis" "Hp_".
    iDestruct (objectmeta_labels_rep with "Hp_Hdeepown_objectmeta") as "[Hpod_labels Hrestore]".
    (* if templateLabel.Matches(labels.Set(pod.Labels)) { fullyLabeledReplicasCount++ } *)
    wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures.
    wp_bind ((match selector with
      | interface.ok selector_i =>
          Val (#(methods selector_i.(interface.ty) "Matches" selector_i.(interface.v)))
      | interface.nil => Panic "nil interface"
      end)
      #(interface.ok (interface.mk labels.Set'
        #(v1.ObjectMeta.Labels' (v1.Pod.ObjectMeta' pod_c)))))%E.
    iApply (wp_Selector__Matches_resolved selector
      (LabelSelectorV.match_labels (Some (default ∅
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels'))))
      (v1.ObjectMeta.Labels' (v1.Pod.ObjectMeta' pod_c))
      this_pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') dq
      with "[$Hselector $Hpod_labels]").
    iNext. iIntros (b) "(_ & Hpod_labels & _)".
    iDestruct ("Hrestore" with "Hpod_labels") as "Hp_Hdeepown_objectmeta".
    iAssert (PodV.deepown_l this_ptr this_pod dq)
      with "[Hthis_l Hp_Hdeepown_objectmeta Hp_Hdeepown_podspec Hp_Hdeepown_podstatus]" as "Hthis".
    { iExists pod_c. iFrame. rewrite /PodV.deepown. iFrame "∗ %". }
    wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ ∃ fl' : w64,
        "fullyLabeledReplicasCount" ∷ fullyLabeledReplicasCount_ptr ↦ fl' ∗
        ⌜ fl' = fl ∨ fl' = word.add fl (W64 1) ⌝)%I with "[fullyLabeledReplicasCount]").
    { destruct b; wp_pures.
      - wp_load. wp_pures. wp_store. wp_pures. iFrame. iPureIntro. split; first done. by right.
      - iFrame. iPureIntro. split; first done. by left. }
    iIntros (v_fl) "(-> & %fl' & fullyLabeledReplicasCount & %Hfl')".
    wp_pures.
    (* if IsPodReady(pod) { readyReplicasCount++; if IsPodAvailable(...) { availableReplicasCount++ } } *)
    wp_load. wp_pures.
    wp_apply (wp_IsPodReady with "[$Hthis]"). iIntros "Hthis".
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ ∃ rd' av' : w64,
        "readyReplicasCount" ∷ readyReplicasCount_ptr ↦ rd' ∗
        "availableReplicasCount" ∷ availableReplicasCount_ptr ↦ av' ∗
        "Hthis" ∷ PodV.deepown_l this_ptr this_pod dq ∗
        "pod" ∷ pod_ptr ↦ this_ptr ∗ "rs" ∷ rs_ptr ↦ rs_l ∗ "now" ∷ now_ptr ↦ now ∗
        "Hrs_l" ∷ rs_l ↦ rs_phy ∗
        ⌜ (rd' = rd ∧ av' = av) ∨
          (rd' = word.add rd (W64 1) ∧ (av' = av ∨ av' = word.add av (W64 1))) ⌝)%I
      with "[readyReplicasCount availableReplicasCount Hthis pod rs now Hrs_l]").
    { destruct (PodStatusV.ready this_pod.(PodV.Status')); wp_pures.
      - wp_load. wp_pures. wp_store. wp_pures.
        wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures.
        wp_apply (wp_IsPodAvailable with "[$Hthis]"). iIntros (avail) "Hthis".
        destruct avail; wp_pures.
        + wp_load. wp_pures. wp_store. wp_pures. iFrame. iPureIntro.
          split; first done. right. split; first done. by right.
        + iFrame. iPureIntro. split; first done. right. split; first done. by left.
      - iFrame. iPureIntro. split; first done. by left. }
    iIntros (v_rd) "(-> & %rd' & %av' & readyReplicasCount & availableReplicasCount & Hthis &
      pod & rs & now & Hrs_l & %Hrd')".
    wp_pures.
    iDestruct ("Hpods" with "Hthis") as "Hpods".
    (* i++ *)
    iApply wp_for_post_do. wp_pures. wp_load. wp_pures. wp_store. wp_pures.
    iAssert I with "[i pod fullyLabeledReplicasCount readyReplicasCount availableReplicasCount
        Hactive_sl Hpods]" as "Hloop".
    { iExists (word.add i (W64 1)), this_ptr, fl', rd', av'. iFrame.
      pose proof (lookup_lt_Some _ _ _ Hthis_ptr_lookup) as Hthis_lt.
      iPureIntro. split; first word.
      destruct Hcounts as (Hav & Hrd & Hfl).
      destruct Hfl' as [-> | ->]; destruct Hrd' as [[-> ->] | [-> [-> | ->]]]; split_and!; word. }
    iFrame.
  - rewrite decide_False //. rewrite decide_True //. wp_pures.
    (* terminatingReplicasCount: nil, or a pointer to len(terminatingPods) when the
       feature gate and the controller flag are both enabled. *)
    wp_alloc terminatingReplicasCount_ptr as "terminatingReplicasCount". wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ ∃ (tptr : loc) (topt : option w32),
        "terminatingReplicasCount" ∷ terminatingReplicasCount_ptr ↦ tptr ∗
        "#Htptr" ∷ opt_ptr_rep tptr topt DfracDiscarded ∗
        "%Htopt" ∷ ⌜ topt = None ∨ topt = Some (W32 (sint.Z terminating_sl.(slice.len))) ⌝)%I
      with "[terminatingReplicasCount controllerFeatures terminatingPods]").
    { wp_bind (MethodResolve featuregate.FeatureGate "Enabled"%go
        (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) _)%E.
      iApply wp_DefaultFeatureGate_Enabled; first iPkgInit.
      iNext. iIntros (gate) "_".
      destruct gate; wp_pures.
      - wp_load. wp_pures.
        destruct (upstreamrs.ReplicaSetControllerFeatures.EnableStatusTerminatingReplicas'
          controller_features); wp_pures.
        + wp_load. wp_pures.
          wp_func_call. rewrite /code.k8s_io.utils.ptr.ptr.Toⁱᵐᵖˡ. wp_call.
          wp_alloc tptr as "Ht". iPersist "Ht". wp_pures. wp_store. wp_pures.
          iFrame. iSplit; first done.
          iExists (Some _). iFrame "Ht". iPureIntro. by right.
        + iFrame. iSplit; first done. iExists None. iPureIntro. split; [done|by left].
      - iFrame. iSplit; first done. iExists None. iPureIntro. split; [done|by left]. }
    iIntros (v_t) "(-> & %tptr & %topt & terminatingReplicasCount & #Htptr & %Htopt)".
    wp_pures.
    (* failureCond := GetCondition(rs.Status, ReplicaSetReplicaFailure) *)
    wp_alloc failureCond_ptr as "failureCond". wp_pures.
    wp_load. wp_pures. wp_load. wp_pures.
    wp_apply (wp_GetCondition with "[$Hrs_status]"). iIntros (fc) "%Hfc".
    wp_pures. wp_store. wp_pures.
    (* manageReplicasErr is nil: only the RemoveCondition branch can run. *)
    wp_load. wp_pures.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
        ∃ (sc : api_apps_v1.ReplicaSetStatus.t) (st : ReplicaSetStatusV.t),
        "newStatus" ∷ newStatus_ptr ↦ sc ∗
        "#Hst" ∷ ReplicaSetStatusV.deepown sc st DfracDiscarded ∗
        "%Hst_og" ∷ ⌜ st.(ReplicaSetStatusV.ObservedGeneration') =
          rs.(ReplicaSetV.Status').(ReplicaSetStatusV.ObservedGeneration') ⌝)%I
      with "[newStatus manageReplicasErr failureCond]").
    { wp_load. wp_pures. wp_load. wp_pures.
      destruct (bool_decide (fc = null)); wp_pures.
      - iFrame. iSplit; first done. iExists _. iFrame "Hrs_status". done.
      - wp_apply (wp_RemoveCondition with "[$newStatus $Hrs_status]").
        iIntros (status_c') "[newStatus #Hrs_status']".
        wp_pures. iFrame. iSplit; first done. iExists _. iFrame "Hrs_status'". done. }
    iIntros (v_c) "(-> & %sc & %st & newStatus & #Hst & %Hst_og)".
    wp_pures.
    (* newStatus.Replicas, .FullyLabeledReplicas, .ReadyReplicas, .AvailableReplicas,
       .TerminatingReplicas; return newStatus *)
    wp_load. wp_pures. wp_store. wp_pures.
    wp_load. wp_pures. wp_store. wp_pures.
    wp_load. wp_pures. wp_store. wp_pures.
    wp_load. wp_pures. wp_store. wp_pures.
    wp_load. wp_pures. wp_store. wp_pures.
    wp_load. wp_pures.
    iModIntro.
    iAssert (ReplicaSetV.deepown rs_phy rs DfracDiscarded)
      with "[Hspec_Hdeepown_replicas_some Hspec_Hdeepown_selector_some]" as "Hrs".
    { rewrite /ReplicaSetV.deepown /ReplicaSetSpecV.deepown. iFrame "∗ # %". }
    iApply "HΦ". iFrame "Hrs_l Hrs Hactive_sl Hpods Hterm_sl".
    iSplitR; first iApply (ReplicaSetStatusV.deepown_set_counts with "Hst Htptr").
    iPureIntro. simpl.
    split_and!.
    + rewrite -Hpods_len Hactive_len1. word.
    + exact Hst_og.
    + (* Every count fits in int32, so the conversions keep them non-negative and
         nested as the loop invariant states. *)
      intros Hactive_bound Hterm_bound g Hg.
      rewrite -Hpods_len Hactive_len1 in Hactive_bound. rewrite Hterm_len1 in Hterm_bound.
      destruct Hcounts as (Hav & Hrd & Hfl).
      rewrite /ReplicaSetStatusV.valid /=.
      (* Keep only the arithmetic facts, so [word] works in a small context. *)
      clear - Hi Hge Hav Hrd Hfl Hactive_bound Hterm_bound Hg Hterm_len2 Hactive_len2 Htopt.
      destruct Htopt as [-> | ->]; split_and!; word.
Qed.

End proof.
