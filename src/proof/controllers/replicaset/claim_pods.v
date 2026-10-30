From New.proof Require Import wp_keep.
From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export manage_replicas.

(* Specifications of the claim step of [syncReplicaSet]: [claimPods] and the
   filter for terminating pods. *)

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
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* The selector reads only labels, which erasing the resource version keeps. *)
Lemma Forall_rs_selects_erased_meta_perm rs pods1 pods2 :
  ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2) →
  Forall (rs_selects rs) pods2 → Forall (rs_selects rs) pods1.
Proof.
  set Q := λ m : ObjectMetaV.t, match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') with
    | Some selector => LabelSelectorV.matches selector m.(ObjectMetaV.Labels')
    | None => False
    end.
  assert (∀ pods, Forall (rs_selects rs) pods ↔
      Forall Q (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))) as Hiff.
  { intros pods. rewrite !Forall_fmap. apply Forall_iff. intros pod. done. }
  intros Hperm H2. apply Hiff. apply Hiff in H2.
  eapply Permutation_Forall; [symmetry; exact Hperm|exact H2].
Qed.

(* A property of metadata that ignores the resource version holds of pods with
   the same storage views. *)
Lemma Forall_storage_view_perm (P : ObjectMetaV.t → Prop) pods1 pods2 :
  (∀ m, P (ObjectMetaV.without_resource_version m) ↔ P m) →
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  Forall (λ pod, P pod.(PodV.ObjectMeta')) pods2 → Forall (λ pod, P pod.(PodV.ObjectMeta')) pods1.
Proof.
  intros HP.
  assert (∀ pods, Forall (λ pod, P pod.(PodV.ObjectMeta')) pods ↔
      Forall (λ view, P view.1) (pod_storage_view <$> pods)) as Hiff.
  { intros pods. rewrite Forall_fmap. apply Forall_iff. intros pod.
    rewrite /pod_storage_view /= HP. done. }
  intros Hperm H2. apply Hiff. apply Hiff in H2.
  eapply Permutation_Forall; [symmetry; exact Hperm|exact H2].
Qed.

(* Filtering by a property of metadata that ignores the resource version keeps
   the erased metadata of two lists a permutation. *)
Lemma filter_erased_meta_perm (Q : ObjectMetaV.t → Prop) `{!∀ m, Decision (Q m)} pods1 pods2 :
  (∀ m, Q (ObjectMetaV.without_resource_version m) ↔ Q m) →
  ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2) →
  ObjectMetaV.without_resource_version <$>
      (PodV.ObjectMeta' <$> filter (λ pod, Q pod.(PodV.ObjectMeta')) pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$>
      (PodV.ObjectMeta' <$> filter (λ pod, Q pod.(PodV.ObjectMeta')) pods2).
Proof.
  intros HQ Hperm.
  assert (∀ pods : list PodV.t, ObjectMetaV.without_resource_version <$>
      (PodV.ObjectMeta' <$> filter (λ pod, Q pod.(PodV.ObjectMeta')) pods) =
    filter Q (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))) as Hcomm.
  { induction pods as [|pod pods IH]; [done|].
    destruct (decide (Q pod.(PodV.ObjectMeta'))) as [Hq|Hq].
    - assert (Q (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))) as Hq' by (by apply HQ).
      rewrite filter_cons decide_True // !fmap_cons filter_cons decide_True // IH //.
    - assert (¬ Q (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))) as Hq'.
      { intros Hq'. apply Hq. by apply HQ. }
      rewrite filter_cons decide_False // !fmap_cons filter_cons decide_False //. }
  rewrite !Hcomm. by rewrite Hperm.
Qed.

Lemma filter_length_eq_all {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list A) :
  length (filter P l) = length l → ∀ x, x ∈ l → P x.
Proof.
  intros Hlen x Hx. destruct (decide (P x)) as [|HP]; [done|].
  pose proof (length_filter_lt P l x Hx HP). lia.
Qed.

(* [FilterTerminatingPods] on shared pods: it keeps a sublist of them. *)
Lemma wp_FilterTerminatingPods_kept sl dq_sl ptrs pods :
  {{{ is_pkg_init controller ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "#Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod DfracDiscarded)
  }}}
    @! controller.FilterTerminatingPods #sl
  {{{ sl' ptrs' pods', RET #sl';
      sl' ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';pods', PodV.deepown_l ptr pod DfracDiscarded) ∗
      ⌜ pods' `sublist_of` pods ⌝ ∗
      sl ↦*{dq_sl} ptrs
  }}}.
Proof.
  (* TODO: prove, following wp_FilterTerminatingPods. *)
Admitted.

(* [FilterClaimedPods] with the ReplicaSet as the controller keeps a sublist of
   its input whose controller has the ReplicaSet's UID ([IsControlledBy] checks
   only the UID). Only the length matters to [calculateStatus]. *)
Lemma wp_FilterClaimedPods_rs rs_l rs selector P `{!∀ ls, Decision (P ls)} sl ptrs pods :
  {{{ is_pkg_init controller ∗
      "#Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs DfracDiscarded ∗
      "#Hselector" ∷ is_selector selector P ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "#Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod DfracDiscarded)
  }}}
    @! controller.FilterClaimedPods
      #(interface.mk_ok (go.PointerType code.k8s_io.api.apps.v1.v1.ReplicaSet) #rs_l) #selector #sl
  {{{ sl' (ptrs' : list loc) pods', RET #sl';
      sl' ↦* ptrs' ∗
      ⌜ length ptrs' = length pods' ⌝ ∗
      ⌜ pods' `sublist_of` pods ⌝ ∗
      ⌜ Forall (λ pod, ∃ parent_key, meta_parent_ref pod.(PodV.ObjectMeta') =
        Some (parent_key, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID'))) pods' ⌝ ∗
      sl ↦* ptrs
  }}}.
Proof.
  (* TODO: prove; needs specs for IsControlledBy on a ReplicaSet. *)
Admitted.

(* [claimPods] on the ReplicaSet's alive pods [owned] and the namespace's living
   orphans [orphans], the in-memory copies of [orphan_pods]. Under these
   resources no write fails: the ReplicaSet releases the pods the selector does
   not match, which become orphans [released], adopts every selected orphan and
   leaves the other orphans alone. The returned copies are the ones it was
   given, so an adopted pod's copy lacks its new controller reference;
   [adopted] are the adopted pods as stored. *)
Lemma wp_claimPods γ l (ctx : context.Context.t) (kube_client : loc) rs_l rs sel selector
    sl ptrs owned orphans orphan_pods rs_dq rs_status_dq :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs DfracDiscarded ∗
      "%Hrs_selector" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') = Some sel ⌝ ∗
      "#Hselector" ∷ is_selector selector (LabelSelectorV.matches sel) ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "#Hdeepown_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;owned ++ orphans, PodV.deepown_l ptr pod DfracDiscarded) ∗
      "%Howned" ∷ ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') =
        Some (ReplicaSetV.key rs, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) ∧ is_pod_alive pod) owned ⌝ ∗
      "%Horphans" ∷ ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') = None ∧ is_pod_alive pod ∧
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) orphans ⌝ ∗
      "%Horphans_perm" ∷ ⌜ pod_storage_view <$> orphans ≡ₚ pod_storage_view <$> orphan_pods ⌝ ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hown_rs_status_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_status_dq
        (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')) ∗
      "Hown_owned_frags" ∷ ([∗ list] pod ∈ owned,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_orphan_pod_frags" ∷ ([∗ list] pod ∈ orphan_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "#Hown_orphan_unreserved_key_frags" ∷
        ([∗ list] pod ∈ filter (rs_selects rs) orphan_pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ (PodV.kind, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) 1
        (list_to_set (PodV.key <$> orphan_pods)) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> owned))
  }}}
    @! replicaset.claimPods #ctx #kube_client #rs_l #selector #sl
  {{{ claimed_sl claimed_ptrs released adopted, RET (#claimed_sl, #interface.nil);
      "Hclaimed_sl" ∷ claimed_sl ↦* claimed_ptrs ∗
      "#Hclaimed_deepown_pods" ∷ ([∗ list] ptr;pod ∈ claimed_ptrs;
        filter (rs_selects rs) owned ++ filter (rs_selects rs) orphans, PodV.deepown_l ptr pod DfracDiscarded) ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "%Hreleased" ∷ ⌜ Forall2 (λ pod pod',
        PodV.key pod' = PodV.key pod ∧
        pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') = pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∧
        pod'.(PodV.ObjectMeta').(ObjectMetaV.Labels') = pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') ∧
        pod'.(PodV.Spec') = pod.(PodV.Spec') ∧
        is_pod_alive pod' ∧
        meta_parent_ref pod'.(PodV.ObjectMeta') = None)
        (filter (λ pod, ¬ rs_selects rs pod) owned) released ⌝ ∗
      "%Hadopted" ∷ ⌜ Forall2 (λ orphan pod,
        PodV.key pod = PodV.key orphan ∧
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') = orphan.(PodV.ObjectMeta').(ObjectMetaV.UID') ∧
        pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') = orphan.(PodV.ObjectMeta').(ObjectMetaV.Labels') ∧
        pod.(PodV.Spec') = orphan.(PodV.Spec') ∧
        is_pod_alive pod ∧
        meta_parent_ref pod.(PodV.ObjectMeta') =
          Some (ReplicaSetV.key rs, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')))
        (filter (rs_selects rs) orphans) adopted ⌝ ∗
      "%Hadopted_len" ∷ ⌜ length adopted = length (filter (rs_selects rs) orphan_pods) ⌝ ∗
      "#Hadopted_unreserved_key_frags" ∷ ([∗ list] pod ∈ adopted, own_unreserved_key_frag γ (PodV.key pod)) ∗
      "Hown_claimed_frags" ∷ ([∗ list] pod ∈ filter (rs_selects rs) owned ++ adopted,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_orphan_pod_frags" ∷ ([∗ list] pod ∈ filter (λ pod, ¬ rs_selects rs pod)%type orphan_pods ++ released,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ (PodV.kind, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) 1
        (list_to_set (PodV.key <$> filter (λ pod, ¬ rs_selects rs pod)%type orphan_pods ++ released)) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> filter (rs_selects rs) owned ++ adopted)) ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hown_rs_status_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_status_dq
        (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}.
Proof.
  (* TODO: prove; needs the adoption spec for PodUpdateTx, the release spec, and
     specs for the ref manager (NewAggregate, CanAdopt over sync.Once,
     ClaimObject). *)
Admitted.

(* [claimPods] when no orphan is selected: it writes nothing and claims exactly
   the ReplicaSet's pods. *)
Lemma wp_claimPods_no_adoption (ctx : context.Context.t) (kube_client : loc) rs_l rs sel selector
    sl ptrs owned orphans :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs DfracDiscarded ∗
      "%Hrs_selector" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') = Some sel ⌝ ∗
      "#Hselector" ∷ is_selector selector (LabelSelectorV.matches sel) ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "#Hdeepown_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;owned ++ orphans, PodV.deepown_l ptr pod DfracDiscarded) ∗
      "%Howned_controlled" ∷ ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') =
        Some (ReplicaSetV.key rs, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID'))) owned ⌝ ∗
      "%Howned_selected" ∷ ⌜ Forall (rs_selects rs) owned ⌝ ∗
      "%Horphans" ∷ ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') = None ∧ ¬ rs_selects rs pod) orphans ⌝
  }}}
    @! replicaset.claimPods #ctx #kube_client #rs_l #selector #sl
  {{{ claimed_sl claimed_ptrs, RET (#claimed_sl, #interface.nil);
      claimed_sl ↦* claimed_ptrs ∗
      ([∗ list] ptr;pod ∈ claimed_ptrs;owned, PodV.deepown_l ptr pod DfracDiscarded) ∗
      sl ↦* ptrs
  }}}.
Proof.
  (* TODO: prove with wp_claimPods's helper specs; no adoption is attempted. *)
Admitted.

End proof.
