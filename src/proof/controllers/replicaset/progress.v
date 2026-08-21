From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.replicaset Require Export get_indirectly_related_pods get_pods_to_delete top_level.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
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

Lemma list_to_set_app_singleton_kkey (x : KKey.t) (l1 l2 l3 : list KKey.t) :
  list_to_set (C:=gset KKey.t) (l1 ++ ((l2 ++ [x]) ++ l3)) =
  list_to_set (C:=gset KKey.t) ((x :: l1) ++ l2 ++ l3).
Proof.
  apply set_eq. intros k.
  rewrite !elem_of_list_to_set.
  rewrite !elem_of_app !list_elem_of_singleton !elem_of_cons.
  split.
  - intros [Hl1 | [[Hl2 | Hx] | Hl3]].
    + left. right. exact Hl1.
    + right. left. exact Hl2.
    + subst k. left. left. done.
    + right. right. exact Hl3.
  - intros [[Hx | Hl1] | [Hl2 | Hl3]].
    + subst k. right. left. right. done.
    + left. exact Hl1.
    + right. left. left. exact Hl2.
    + right. right. exact Hl3.
Qed.

Lemma list_to_set_cons_difference_kkey (x : KKey.t) (l : list KKey.t) :
  x ∉ l →
  list_to_set (C:=gset KKey.t) l =
  list_to_set (C:=gset KKey.t) (x :: l) ∖ {[x]}.
Proof.
  intros Hnotin.
  apply set_eq. intros k.
  rewrite elem_of_difference !elem_of_list_to_set elem_of_singleton elem_of_cons.
  split.
  - intros Hk. split.
    + right. exact Hk.
    + intros ->. exact (Hnotin Hk).
  - intros [[-> | Hk] Hneq].
    + exfalso. apply Hneq. done.
    + exact Hk.
Qed.

Lemma pod_key_not_in_delete_remainder
    active_pods inactive_pods inactive_pods' this_pod i :
  NoDup (PodV.key <$> (active_pods ++ inactive_pods)) →
  active_pods !! i = Some this_pod →
  (∀ key, key ∈ PodV.key <$> inactive_pods' → key ∈ PodV.key <$> take i active_pods) →
  PodV.key this_pod ∉
    PodV.key <$> (drop (S i) active_pods ++ inactive_pods' ++ inactive_pods).
Proof.
  intros Hnodup Hlookup Hincluded Hcontra.
  rewrite !fmap_app !elem_of_app in Hcontra.
  assert ((active_pods ++ inactive_pods) !! i = Some this_pod) as Hlookup_this.
  { apply lookup_app_l_Some. exact Hlookup. }
  assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! i = Some (PodV.key this_pod))
    as Hlookup_key_this.
  { rewrite list_lookup_fmap Hlookup_this. done. }
  destruct Hcontra as [Hdrop | [Hinactive' | Hinactive]].
  - apply list_elem_of_lookup_1 in Hdrop as (j & Hlookup_drop_key).
    rewrite list_lookup_fmap in Hlookup_drop_key.
    destruct (drop (S i) active_pods !! j) as [pod_j|] eqn:Hlookup_drop; simpl in Hlookup_drop_key; [|done].
    assert ((active_pods ++ inactive_pods) !! (S i + j)%nat = Some pod_j) as Hlookup_j.
    { apply lookup_app_l_Some. rewrite lookup_drop in Hlookup_drop. exact Hlookup_drop. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! (S i + j)%nat = Some (PodV.key this_pod))
      as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_drop_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    lia.
  - pose proof (Hincluded _ Hinactive') as Hkey_take.
    apply list_elem_of_lookup_1 in Hkey_take as (j & Hlookup_take_key).
    rewrite list_lookup_fmap in Hlookup_take_key.
    destruct (take i active_pods !! j) as [pod_j|] eqn:Hlookup_take; simpl in Hlookup_take_key; [|done].
    apply lookup_take_Some in Hlookup_take as (Hlookup_active_j & Hj_lt).
    assert ((active_pods ++ inactive_pods) !! j = Some pod_j) as Hlookup_j.
    { apply lookup_app_l_Some. exact Hlookup_active_j. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! j = Some (PodV.key this_pod))
      as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_take_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    lia.
  - apply list_elem_of_lookup_1 in Hinactive as (j & Hlookup_inactive_key).
    rewrite list_lookup_fmap in Hlookup_inactive_key.
    destruct (inactive_pods !! j) as [pod_j|] eqn:Hlookup_inactive; simpl in Hlookup_inactive_key; [|done].
    assert ((active_pods ++ inactive_pods) !! (length active_pods + j)%nat = Some pod_j) as Hlookup_j.
    { rewrite lookup_app.
      assert (active_pods !! (length active_pods + j)%nat = None) as Hactive_none.
      { apply lookup_ge_None_2. apply Nat.le_add_r. }
      rewrite Hactive_none.
      replace (length active_pods + j - length active_pods)%nat with j by lia.
      exact Hlookup_inactive. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! (length active_pods + j)%nat =
        Some (PodV.key this_pod)) as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_inactive_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    apply lookup_lt_Some in Hlookup.
    lia.
Qed.

Lemma list_to_set_pod_key_filter_partition pods :
  list_to_set (C:=gset KKey.t)
    (PodV.key <$> (filter is_pod_alive pods ++ filter (λ pod, not (is_pod_alive pod)) pods)) =
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods).
Proof.
  apply set_eq. intros key.
  rewrite fmap_app !elem_of_list_to_set elem_of_app !list_elem_of_fmap.
  split.
  - intros [(pod & -> & Hin)|(pod & -> & Hin)].
    + apply list_elem_of_filter in Hin as [_ Hin].
      exists pod. split; done.
    + apply list_elem_of_filter in Hin as [_ Hin].
      exists pod. split; done.
  - intros (pod & -> & Hin).
    destruct (decide (is_pod_alive pod)) as [Halive|Hnot_alive].
    + left. exists pod. split; [done|apply list_elem_of_filter; split; done].
    + right. exists pod. split; [done|apply list_elem_of_filter; split; done].
Qed.

Lemma pod_key_filter_partition_perm pods :
  PodV.key <$> (filter is_pod_alive pods ++ filter (λ pod, not (is_pod_alive pod)) pods) ≡ₚ
  PodV.key <$> pods.
Proof.
  apply Permutation_map.
  apply filter_partition_perm.
Qed.

Lemma pod_key_meta_perm pods1 pods2 :
  ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2) →
  PodV.key <$> pods1 ≡ₚ PodV.key <$> pods2.
Proof.
  intros Hperm.
  assert (PodV.key <$> pods1 =
      PodV.meta_key <$> (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1))) as ->.
  { rewrite -!list_fmap_compose.
    apply list_fmap_ext. intros i pod Hlookup.
    unfold compose, PodV.key, PodV.meta_key, ObjectMetaV.without_resource_version. destruct pod; done. }
  assert (PodV.key <$> pods2 =
      PodV.meta_key <$> (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2))) as ->.
  { rewrite -!list_fmap_compose.
    apply list_fmap_ext. intros i pod Hlookup.
    unfold compose, PodV.key, PodV.meta_key, ObjectMetaV.without_resource_version. destruct pod; done. }
  apply Permutation_map. exact Hperm.
Qed.

Lemma own_unreserved_key_frag_list_as_keys γ pods :
  ([∗ list] pod ∈ pods, own_unreserved_key_frag γ (PodV.key pod)) ⊣⊢
  ([∗ list] key ∈ PodV.key <$> pods, own_unreserved_key_frag γ key).
Proof. rewrite big_sepL_fmap. done. Qed.

Lemma wp_manageReplicas γ l sl rs_l ptrs active_pods inactive_pods rs n phase dq1 dq2 :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_active_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "Hown_active_pod_meta_frags" ∷ ([∗ list] pod ∈ active_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "#Hown_active_pod_unreserved_key_frags" ∷
        ([∗ list] pod ∈ active_pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> (active_pods ++ inactive_pods))) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "%Hrs_meta_valid" ∷ ⌜ ObjectMetaV.valid ReplicaSetV.kind rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hrs_spec_valid" ∷ ⌜ ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec') ⌝ ∗
      "%Hactive_pods" ∷ ⌜ ∀ pod, pod ∈ active_pods → is_pod_alive pod ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hrs_template_finalizers_valid" ∷ ⌜ valid_finalizers
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (PodV.key <$> (active_pods ++ inactive_pods)) ⌝
  }}}
    @! replicaset.manageReplicas #sl #rs_l
  {{{ pods', RET #interface.nil;
      ⌜ length (filter is_pod_alive pods') = sint.nat n ⌝ ∗
      (∃ phase', own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase') ∗
      ReplicaSetV.deepown_l rs_l rs dq2 ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      ([∗ list] pod ∈ pods', own_unreserved_key_frag γ (PodV.key pod)) ∗
      own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> (pods' ++ inactive_pods)))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iDestruct "Hdeepown_s_l_rs" as "(%rs_spec_c & Hrs_spec_l & Hdeepown_rs_spec)".
  iNamedPrefix "Hdeepown_rs_spec" "Hrs_".
  iAssert ((rs_spec_c.(v1.ReplicaSetSpec.Replicas') ↦{dq2} n)%I) with "[Hrs_Hdeepown_replicas_some]"
    as "Hrs_Hdeepown_replicas".
  { rewrite Hreplicas_eq. iDestruct "Hrs_Hdeepown_replicas_some" as "(%replicas & Hreplicas & ->)". done. }
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_l_active_pods") as %Hlen.
  assert (0 ≤ sint.Z n) as Hn.
  { pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (i & Hi_eq & Hi).
    rewrite Hi_eq in Hreplicas_eq. congruence. }
  assert ((sint.Z (word.sub (slice.len sl) (W64 (sint.Z n)))) = (sint.Z (slice.len sl)) - (sint.Z n)) as -> by word.
  assert ((sint.Z (W64 0)) = 0) as -> by word.
  wp_if_destruct.
  - iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr rs_l)
        rs.(ReplicaSetV.Spec') dq2)%I
      with "[Hrs_spec_l Hrs_Hdeepown_replicas Hrs_Hdeepown_selector_some
        Hrs_Hdeepown_template]" as "Hdeepown_s_l_rs".
    { iExists rs_spec_c. iSplitL "Hrs_spec_l"; first iExact "Hrs_spec_l".
      iSplit; first done.
      rewrite Hreplicas_eq.
      iSplitL "Hrs_Hdeepown_replicas".
      { iExists n. iSplitL; first iExact "Hrs_Hdeepown_replicas". done. }
      iSplit; first done. iSplit; first done.
      iFrame "Hrs_Hdeepown_selector_some Hrs_Hdeepown_template". }
    set I := (∃ (i: w64) (active_pods': list PodV.t) (phase' : terminating_children.phase),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ active_pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "#Hown_pod_unreserved_key_frags" ∷
        ([∗ list] pod ∈ active_pods', own_unreserved_key_frag γ (PodV.key pod)) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> (active_pods' ++ inactive_pods))) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase' ∗
      "%Hlen_active_pods'" ∷ ⌜ length active_pods' = Z.to_nat ((sint.Z (slice.len sl)) + sint.Z i) ⌝ ∗
      "%Hall_active" ∷ ⌜ ∀ pod, pod ∈ active_pods' → is_pod_alive pod ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (word.mul (word.sub (slice.len sl) (W64 (sint.Z n))) (W64 (-1))) ⌝
    )%I.
    iAssert (I) with
      "[i Hown_active_pod_meta_frags Hown_active_pod_unreserved_key_frags Hown_children_frag
        Hown_terminating_children_frag]"
      as "Hloop_inv".
    { iExists (W64 0), active_pods, phase. iFrame. iFrame "#".
      iPureIntro. split_and!. all: try word. done. }
    wp_for "Hloop_inv". wp_if_destruct.
	  + wp_bind ((global_addr apps_v1.SchemeGroupVersion) @! (go.PointerType schema.GroupVersion) @! "WithKind" #"ReplicaSet"%go)%E.
	    iDestruct (is_pkg_init_unfold_deps with "Hpkg") as
	      "(_ & _ & _ & #Happs_v1_init & _)".
	    wp_apply (New.proof.k8s_io.api.apps.v1.wp_SchemeGroupVersion__WithKind
	      (schema_sem := @code.k8s_io.api.apps.v1.v1.import_schema_Assumption
	        _ _ _ _ object_apps_v1_sem) "ReplicaSet"%go with
	      "[$Happs_v1_init]").
	    iIntros (gvk) "%Hgvk". wp_auto.
	    destruct Hgvk as (Hgvk_g & Hgvk_v & Hgvk_k).
	    wp_bind (@! replicaset.meta_v1.NewControllerRef
	      #(interface.mk_ok (go.PointerType apps_v1.ReplicaSet) (#rs_l)) #gvk)%E.
	    change (replicaset.meta_v1.NewControllerRef) with v1.NewControllerRef.
	    wp_apply (v1.wp_NewControllerRef_ReplicaSet with "[Hdeepown_m_l_rs]").
	    { iFrame "Hdeepown_m_l_rs". iPureIntro. done. }
	    iIntros (controller_ref_l controller_ref)
	      "(Hdeepown_l_controller_ref & %Hcontroller_ref_valid & %Hcontroller_ref_wf & Hdeepown_m_l_rs)".
	    wp_auto. rewrite Hgvk_k in Hcontroller_ref_valid.
	    iDestruct "Hdeepown_s_l_rs" as (rs_spec_c') "[Hrs_spec_l Hdeepown_rs_spec]".
	    iNamedPrefix "Hdeepown_rs_spec" "Hrs_".
	    iDestruct (struct_fields_split with "Hrs_spec_l") as "[H %Hrs_spec_l_not_null]". iNamedPrefix "H" "Hrs_".
	    change ((rs_l.[apps_v1.ReplicaSet.t, "Spec"]).[apps_v1.ReplicaSetSpec.t, "Template"]) with
	      ((ReplicaSetV.spec_ptr rs_l).[v1.ReplicaSetSpec.t, "Template"]).
	    pose proof (ObjectMetaV.valid_name_of_valid _ Hrs_meta_valid) as Hrs_name_valid.
	    unfold valid_name, ReplicaSetV.kind in Hrs_name_valid.
	    destruct Hrs_name_valid as [[Hkind _]|[[Hkind|[Hkind|Hkind]] Hrs_name_valid]];
	      try discriminate.
	    wp_apply (controller.wp_GetPodFromTemplate
	      ((ReplicaSetV.spec_ptr rs_l).[v1.ReplicaSetSpec.t, "Template"])
	      (interface.mk (go.PointerType apps_v1.ReplicaSet) #rs_l)
	      controller_ref_l dq2 dq2
	      (ReplicaSetSpecV.Template' (ReplicaSetV.Spec' rs)) rs_l
	      (KObjectV.ReplicaSet rs) (Some controller_ref) with
	      "[Hrs_Template Hrs_Hdeepown_template Hdeepown_m_l_rs Hdeepown_l_controller_ref]").
	    { iFrame "# Hdeepown_m_l_rs Hdeepown_l_controller_ref".
	      iSplitL "Hrs_Template Hrs_Hdeepown_template".
	      { iExists rs_spec_c'.(v1.ReplicaSetSpec.Template'). iFrame. }
	      iPureIntro. split; [done|exact Hrs_name_valid]. }
	    iIntros (pod_l) "(Hdeepown_l_pod & Htemplate & Hdeepown_m_l_rs)".
	    iDestruct "Htemplate" as (template_c) "[Hrs_Template Hrs_Hdeepown_template]".
	    set rs_spec_c'' :=
	      rs_spec_c' <| v1.ReplicaSetSpec.Template' := template_c |>.
	    iAssert (((ReplicaSetV.spec_ptr rs_l) ↦{dq2} rs_spec_c'')%I)
	      with "[Hrs_Replicas Hrs_MinReadySeconds Hrs_Selector Hrs_Template]" as "Hrs_spec_l".
	    { iApply (struct_fields_combine (V:=v1.ReplicaSetSpec.t) _ _ _
	        Hrs_spec_l_not_null).
	      unfold rs_spec_c''. simpl. iFrame. }
	    iAssert (ReplicaSetSpecV.deepown rs_spec_c'' rs.(ReplicaSetV.Spec') dq2)
	      with "[Hrs_Hdeepown_replicas_some Hrs_Hdeepown_selector_some
	        Hrs_Hdeepown_template]" as "Hdeepown_rs_spec".
	    { rewrite /ReplicaSetSpecV.deepown /rs_spec_c''. simpl. iFrame.
	      iPureIntro. done. }
	    iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr rs_l)
	        rs.(ReplicaSetV.Spec') dq2)
	      with "[Hrs_spec_l Hdeepown_rs_spec]" as "Hdeepown_s_l_rs".
	    { iExists rs_spec_c''. iFrame. }
	    set pod := controller.generated_pod
	      rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')
	      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') (Some [controller_ref]).
	    assert (obj_parent_ref_is (KObjectV.Pod pod) "ReplicaSet"%go
	        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name')
	        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Hpr.
	    { apply controller.generated_pod_parent_ref. exact Hcontroller_ref_valid. }
	    assert (KObjectV.valid_nameless_create "Pod"%go
	        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') (KObjectV.Pod pod)) as Hvalid.
	    { apply controller.generated_pod_valid_nameless_create; try done.
	      apply ReplicaSetSpecV.valid_template. exact Hrs_spec_valid. }
	    wp_auto.
	    wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_rs]") as "Hdeepown_m_l_rs".
	    wp_apply (wp_State__PodCreate_nameless γ l
	      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') pod_l pod
	      (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
	      (list_to_set (PodV.key <$> (active_pods' ++ inactive_pods)))
	      with "[Hdeepown_l_pod Hown_children_frag]").
	    { iFrame "#".
	      iSplit; [iPureIntro; exact Hvalid|].
	      iSplit; [iPureIntro; eapply ObjectMetaV.valid_namespace_nonempty_of_valid; exact Hrs_meta_valid|].
	      iSplit; [iPureIntro; eapply ObjectMetaV.valid_namespace_of_valid; exact Hrs_meta_valid|].
	      iSplit; [iPureIntro; rewrite /ReplicaSetV.key /ReplicaSetV.meta_key /=; done|].
	      iSplit; [iPureIntro; exact Hpr|].
	      iSplitL "Hdeepown_l_pod".
	      { unfold object_core_v1_sem. iExact "Hdeepown_l_pod". }
	      iExact "Hown_children_frag". }
      iIntros (pod_l' pod' key uid) "H". iNamedPrefix "H" "Hcreate_". subst key. subst uid. wp_auto.
	      iApply wp_for_post_do. wp_auto.
      iAssert (I) with
        "[Hi_ptr Hown_pod_meta_frags Hcreate_Hown_meta_frag Hown_pod_unreserved_key_frags
          Hcreate_Hown_unreserved_key_frag Hcreate_Hown_children_frag Hown_terminating_children_frag]"
        as "loop_inv".
      { iExists (word.add i (W64 1)), (active_pods' ++ [pod']), phase'. iFrame "Hi_ptr".
        iSplitL "Hown_pod_meta_frags Hcreate_Hown_meta_frag".
        - rewrite big_sepL_app. simpl. iFrame.
        - iSplit.
          { rewrite big_sepL_app big_sepL_singleton. iFrame "#". }
          iSplitL "Hcreate_Hown_children_frag".
	            + assert (list_to_set (PodV.key <$> (active_pods' ++ inactive_pods)) ∪ {[PodV.key pod']} =
                list_to_set (PodV.key <$> ((active_pods' ++ [pod']) ++ inactive_pods)))
                as ->.
	              { rewrite !fmap_app. simpl. Timeout 10 set_solver. }
	              done.
	            + iFrame "Hown_terminating_children_frag".
	              iSplit.
              { iPureIntro. rewrite length_app /= Hlen_active_pods'.
                word. }
              iSplit.
              { iPureIntro. intros pod0 Hpod0.
                apply elem_of_app in Hpod0 as [Hpod0|Hpod0].
                - apply Hall_active. done.
                - rewrite list_elem_of_singleton in Hpod0. subst pod0.
                  unfold is_pod_alive.
                  unfold ObjectMetaV.nameless_created in Hcreate_Hmeta_created.
	                  Timeout 5 naive_solver. }
              { iPureIntro. word. }
      }
	      iFrame.
    + iApply ("HΦ" $! active_pods').
      iSplit.
      { iPureIntro.
        rewrite (filter_all is_pod_alive active_pods' Hall_active) Hlen_active_pods'. word. }
      iSplitL "Hown_terminating_children_frag".
      { iExists phase'. iFrame "Hown_terminating_children_frag". }
	      iFrame "Hown_pod_meta_frags
	        Hown_pod_unreserved_key_frags Hown_children_frag".
	      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null).
	      iFrame.
  - wp_if_destruct.
    2 : { iApply ("HΦ" $! active_pods).
      iSplit.
      { iPureIntro.
        rewrite (filter_all is_pod_alive active_pods Hactive_pods).
        rewrite -Hlen Hsl_len1. word. }
      iSplitL "Hown_terminating_children_frag".
      { iExists phase. iFrame "Hown_terminating_children_frag". }
	      iFrame "Hown_active_pod_meta_frags
	        Hown_active_pod_unreserved_key_frags Hown_children_frag".
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null).
      iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
    }
	  assert (Hdelete_count :
	    sint.Z (word.sub (slice.len sl) (W64 (sint.Z n))) =
	    sint.Z (slice.len sl) - sint.Z n) by word.
	  iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr rs_l)
	      rs.(ReplicaSetV.Spec') dq2)%I
	    with "[Hrs_spec_l Hrs_Hdeepown_replicas Hrs_Hdeepown_selector_some
	      Hrs_Hdeepown_template]" as "Hdeepown_s_l_rs".
	  { iExists rs_spec_c. iSplitL "Hrs_spec_l"; first iExact "Hrs_spec_l".
	    iSplit; first done.
	    rewrite Hreplicas_eq.
	    iSplitL "Hrs_Hdeepown_replicas".
	    { iExists n. iSplitL; first iExact "Hrs_Hdeepown_replicas". done. }
	    iSplit; first done. iSplit; first done.
	    iFrame "Hrs_Hdeepown_selector_some Hrs_Hdeepown_template". }
	  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null with
	    "[$Hdeepown_t_l_rs $Hdeepown_m_l_rs $Hdeepown_s_l_rs $Hdeepown_st_l_rs]") as
	    "Hdeepown_l_rs".
	  wp_bind (@! replicaset.getIndirectlyRelatedPods #rs_l)%E.
	  wp_apply (wp_getIndirectlyRelatedPods γ l rs_l rs dq2 with "[$Hdeepown_l_rs]").
	  { iFrame "#". }
	  iIntros (related_sl related_ptrs related_pods related_dq)
	    "(Hrelated_sl & Hrelated_pods & Hdeepown_l_rs)".
	  wp_auto.
	  wp_bind (@! replicaset.getPodsToDelete #sl #related_sl
	    #(word.sub (slice.len sl) (W64 (sint.Z n))))%E.
	  wp_apply (wp_getPodsToDelete sl ptrs active_pods related_sl related_ptrs related_pods
	    (word.sub (slice.len sl) (W64 (sint.Z n))) dq1 related_dq with
	    "[$Hsl $Hdeepown_l_active_pods $Hrelated_sl $Hrelated_pods]").
	  { iFrame "#". iPureIntro. rewrite Hdelete_count. word. }
	  iIntros (sorted_ptrs sorted_pods)
	    "(Hbefore_slice & Hslice & Hafter_slice & Hdeepown_l_sorted_pods &
	      %Hptrs_perm & %Hpods_perm)".
	  wp_auto.
	  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
	    "(_ & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
	  iAssert (([∗ list] pod ∈ sorted_pods,
	      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
	        pod.(PodV.ObjectMeta')))%I
	    with "[Hown_active_pod_meta_frags]" as "Hown_active_pod_meta_frags".
	  { rewrite (big_sepL_permutation
	      (λ pod, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
	        pod.(PodV.ObjectMeta')) sorted_pods active_pods (Permutation_sym Hpods_perm)).
	    iExact "Hown_active_pod_meta_frags". }
	  iAssert (([∗ list] pod ∈ sorted_pods, own_unreserved_key_frag γ (PodV.key pod)))%I
	    with "[Hown_active_pod_unreserved_key_frags]" as "#Hown_sorted_pod_unreserved_key_frags".
	  { rewrite (big_sepL_permutation (λ pod, own_unreserved_key_frag γ (PodV.key pod))
	      sorted_pods active_pods (Permutation_sym Hpods_perm)).
	    iExact "Hown_active_pod_unreserved_key_frags". }
	  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> (sorted_pods ++ inactive_pods)) =
	      list_to_set (C:=gset KKey.t) (PodV.key <$> (active_pods ++ inactive_pods))) as Hchildren_perm.
	  { rewrite Hpods_perm. done. }
	  iEval (rewrite -Hchildren_perm) in "Hown_children_frag".
	  assert (∀ pod, pod ∈ sorted_pods → is_pod_alive pod) as Hsorted_pods.
	  { intros pod Hpod. apply Hactive_pods. rewrite Hpods_perm. exact Hpod. }
	  assert (NoDup (PodV.key <$> (sorted_pods ++ inactive_pods))) as Hsorted_nodup.
	  { rewrite Hpods_perm in Hnodup. exact Hnodup. }
	  clear Hactive_pods Hnodup.
	  rename active_pods into original_active_pods.
	  rename ptrs into original_ptrs.
	  rename sorted_pods into active_pods.
	  rename sorted_ptrs into ptrs.
	  rename Hsorted_pods into Hactive_pods.
	  rename Hsorted_nodup into Hnodup.
	  iRename "Hdeepown_l_sorted_pods" into "Hdeepown_l_active_pods".
	  assert (length ptrs = sint.nat (slice.len sl)) as Hsl_len1_sorted.
	  { rewrite -(Permutation_length Hptrs_perm). exact Hsl_len1. }
	  assert (length ptrs = length active_pods) as Hlen_sorted.
	  { apply Permutation_length in Hptrs_perm.
	    apply Permutation_length in Hpods_perm. lia. }
	  clear Hlen Hsl_len1. rename Hlen_sorted into Hlen.
	  rename Hsl_len1_sorted into Hsl_len1.
    iDestruct (own_slice_len with "Hslice") as %(Hslice_len1 & Hslice_len2).
    set I := (∃ (i: w64) (pod_l: loc) (inactive_pods': list PodV.t) (phase' : terminating_children.phase),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod_l ∗
      "Hown_active_pod_meta_frags" ∷ ([∗ list] pod ∈ drop (sint.nat i) active_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_inactive_pod_meta_frags" ∷ ([∗ list] pod ∈ inactive_pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "#Hown_pod_unreserved_key_frags" ∷ ([∗ list] pod ∈
        drop (sint.nat i) active_pods ++ inactive_pods', own_unreserved_key_frag γ (PodV.key pod)) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> ((drop (sint.nat i) active_pods) ++ inactive_pods' ++ inactive_pods))) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase' ∗
      "%Hinactive" ∷ ⌜ ∀ pod, pod ∈ inactive_pods' → ¬ is_pod_alive pod ⌝ ∗
      "%Hincluded" ∷ ⌜ ∀ key, key ∈ PodV.key <$> inactive_pods' → key ∈ PodV.key <$> take (sint.nat i) active_pods ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len (slice.slice sl loc (W64 0) (word.sub (slice.len sl) (W64 (sint.Z n))))) ⌝
    )%I.
    iAssert (I) with
	      "[i pod Hown_active_pod_meta_frags Hown_sorted_pod_unreserved_key_frags Hown_children_frag
	        Hown_terminating_children_frag]"
      as "Hloop_inv".
    { iExists (W64 0), (zero_val loc), [], phase.
      rewrite drop_0 big_sepL_nil app_nil_r.
      iFrame. iFrame "#".
      iPureIntro. split.
      - intros pod0 Hpod0. inversion Hpod0.
      - split.
        + intros key Hkey. inversion Hkey.
        + word.
	  }
	  wp_for "Hloop_inv". wp_if_destruct.
	  + rewrite decide_True; [word|].
	    set sliced_ptrs := (subslice (sint.nat (W64 0)) (sint.nat (word.sub (slice.len sl) (W64 (sint.Z n)))) ptrs).
	    list_elem sliced_ptrs (sint.Z i) as this_ptr.
      { rewrite Hslice_len1 /slice.slice /=. word. }
      wp_apply (wp_load_slice_index with "[$Hslice]"); [word|eauto|].
      iIntros "Hslice". wp_auto.
      assert (ptrs !! sint.nat i = Some this_ptr) as Hlookup_ptrs.
      { eapply lookup_take_Some in Hthis_ptr_lookup. intuition. }
	      assert (∃ this_pod, active_pods !! sint.nat i = Some this_pod) as [this_pod Hlookup_active_pods].
	      { apply lookup_lt_is_Some_2. rewrite <-Hlen.
	        eapply lookup_lt_Some. exact Hlookup_ptrs. }
      iDestruct (big_sepL2_lookup_acc with "Hdeepown_l_active_pods") as "[Hdeepown_l_this Hdeepown_l_others]".
      { apply Hlookup_ptrs. }
      { apply Hlookup_active_pods. }
      iPoseProof (PodV.deepown_l_split with "Hdeepown_l_this") as
        "(%Hthis_ptr_not_null & Hdeepown_t_l_pod & Hdeepown_m_l_pod & Hdeepown_s_l_pod & Hdeepown_st_l_pod)".
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
	      wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
	      wp_apply (common.wp_NewDeleteOptionsWithUID). iIntros (do_c) "(Hdeepown_do & %Hvalid_do)". wp_auto.
	      assert (drop (sint.nat i) active_pods = this_pod :: drop (S (sint.nat i)) active_pods)
        as Hdrop_active_pods.
      { apply drop_S. exact Hlookup_active_pods. }
      iEval (rewrite Hdrop_active_pods) in "Hown_active_pod_meta_frags".
      iDestruct "Hown_active_pod_meta_frags" as
        "[Hown_pod_meta_frag_this Hown_active_pod_meta_frags_tail]".
	    iEval (rewrite Hdrop_active_pods /=) in "Hown_pod_unreserved_key_frags".
	    iDestruct "Hown_pod_unreserved_key_frags" as
	      "[#Hown_unreserved_key_frag #Hown_pod_unreserved_key_frags_tail]".
	      wp_apply (wp_State__PodDelete γ l (PodV.key this_pod)
	        this_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
	        this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') do_c
	        (delete_options_with_uid this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
	        this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
	        this_pod.(PodV.ObjectMeta') (ReplicaSetV.key rs)
	        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
		        (list_to_set (PodV.key <$>
		          ((drop (sint.nat i) active_pods) ++ inactive_pods' ++ inactive_pods)))
		        phase'
		        with "[Hdeepown_do Hown_pod_meta_frag_this Hown_children_frag
              Hown_unreserved_key_frag Hown_terminating_children_frag]").
	      { iFrame "#".
	        iSplitL "Hdeepown_do"; [iExact "Hdeepown_do"|].
	        iSplit; [iPureIntro; rewrite /PodV.key /PodV.meta_key /=; done|].
	        iSplit.
	        { iPureIntro.
	          rewrite elem_of_list_to_set.
	          apply list_elem_of_fmap_2.
	          rewrite elem_of_app. left.
	          rewrite Hdrop_active_pods. left. }
	        iSplit; [iPureIntro; rewrite /delete_preconditions_match /delete_options_with_uid /=; done|].
		        iSplit; [iPureIntro; rewrite /delete_options_preconditions_resource_version_none /delete_options_with_uid /=; done|].
		        iSplitL "Hown_pod_meta_frag_this"; [iExact "Hown_pod_meta_frag_this"|].
		        iFrame "#". iFrame. }
		      iIntros "H". wp_auto.
		      iApply wp_for_post_do. wp_auto.
		      iNamedPrefix "H" "Hdelete_".
		      iAssert (I) with "[Hi_ptr Hpod_ptr Hdelete_Hown_children_frag
		        Hdelete_Hown_terminating_children_frag Hown_active_pod_meta_frags_tail
            Hown_inactive_pod_meta_frags]" as "loop_inv".
		      { iExists (word.add i (W64 1)), this_ptr, inactive_pods', Mutable.
	        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc by word.
	        rewrite Hsucc.
	        iFrame "Hi_ptr Hpod_ptr Hown_active_pod_meta_frags_tail Hown_inactive_pod_meta_frags".
	        iFrame "Hown_pod_unreserved_key_frags_tail".
	        iSplitL "Hdelete_Hown_children_frag".
	        { assert (list_to_set (C:=gset KKey.t) (PodV.key <$>
                (drop (S (sint.nat i)) active_pods ++ inactive_pods' ++ inactive_pods)) =
	            list_to_set (C:=gset KKey.t) (PodV.key <$>
                (drop (sint.nat i) active_pods ++ inactive_pods' ++ inactive_pods)) ∖
                  {[PodV.key this_pod]}) as Hchildren_eq.
		          { rewrite Hdrop_active_pods !fmap_app /=.
		            apply list_to_set_cons_difference_kkey.
		            rewrite -!fmap_app.
		            apply (pod_key_not_in_delete_remainder active_pods inactive_pods inactive_pods'
		              this_pod (sint.nat i)); done. }
		          rewrite Hchildren_eq. iFrame. }
		        iFrame "Hdelete_Hown_terminating_children_frag".
		        iPureIntro. split.
	        - exact Hinactive.
	        - split.
	          + intros key Hkey.
	            rewrite (take_S_r active_pods (sint.nat i) this_pod Hlookup_active_pods).
	            rewrite fmap_app. apply elem_of_app. left.
		            apply Hincluded. done.
		          + rewrite /slice.slice /=. word. }
		      iFrame. iApply "Hdeepown_l_others".
		      iApply (PodV.deepown_l_restore _ _ _ Hthis_ptr_not_null). iFrame.
	  +
	    iAssert (([∗ list] pod ∈ drop (sint.nat i) active_pods ++ inactive_pods',
	      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
	        pod.(PodV.ObjectMeta')))%I
	      with "[Hown_active_pod_meta_frags Hown_inactive_pod_meta_frags]" as "Hown_pod_meta_frags_ret".
	    { rewrite big_sepL_app. iFrame. }
	    iAssert (own_children_frag γ (ReplicaSetV.key rs)
	      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
	      (list_to_set (PodV.key <$> ((drop (sint.nat i) active_pods ++ inactive_pods') ++ inactive_pods))))%I
	      with "[Hown_children_frag]" as "Hown_children_frag_ret".
		    { rewrite app_assoc. iFrame. }
		    iApply ("HΦ" $! (drop (sint.nat i) active_pods ++ inactive_pods')).
		    iSplit.
		    { iPureIntro.
	      rewrite list.filter_app.
	      assert (filter is_pod_alive (drop (sint.nat i) active_pods) =
	          drop (sint.nat i) active_pods) as Hfilter_active.
	      { apply filter_all. intros pod Hpod.
	        apply Hactive_pods.
	        apply list_elem_of_lookup_1 in Hpod as (j & Hlookup_pod).
	        apply (list_elem_of_lookup_2 active_pods (sint.nat i + j)%nat).
	        rewrite lookup_drop in Hlookup_pod. exact Hlookup_pod. }
	      rewrite Hfilter_active.
	      assert (filter is_pod_alive inactive_pods' = []) as Hfilter_inactive.
	      { apply filter_none. exact Hinactive. }
	      rewrite Hfilter_inactive app_nil_r.
	      assert (sint.Z i = sint.Z (word.sub (slice.len sl) (W64 (sint.Z n)))) as Hi_Z.
	      { rewrite /slice.slice /= in Hi. word. }
	      assert (sint.nat i = sint.nat (word.sub (slice.len sl) (W64 (sint.Z n)))) as Hi_eq by word.
	      rewrite length_drop -Hlen Hsl_len1 Hi_eq.
	      word. }
		    iSplitL "Hown_terminating_children_frag".
		    { iExists phase'. iFrame. }
	    iFrame "Hown_pod_meta_frags_ret Hown_pod_unreserved_key_frags
	      Hown_children_frag_ret".
		    iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null). iFrame.
Qed.

Lemma wp_syncReplicaSet_progress γ l namespace name rs dq pods :
  ⊢ progress_spec γ l namespace name rs dq pods.
Proof.
  unfold progress_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_pod_meta_frags
    Hown_children_frag Hown_terminating_children_frag".
  unfold input_requirement in Hinput_requirement.
  destruct Hinput_requirement as [Hrs_name_short Hrs_template_finalizers_valid].
  wp_auto.
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__ReplicaSetGet with "[$Hown_rs_meta_frag $Hown_rs_spec_frag]").
  { iFrame "#".
    iPureIntro.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hnamespace_eq Hname_eq.
    done. }
  iIntros (rs_l rs_get) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hdeepown_l_rs".
  iRename "Hget_Hown_meta_frag" into "Hown_rs_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_rs_spec_frag".
  assert (ReplicaSetSpecV.valid rs_get.(ReplicaSetV.Spec')) as Hrs_get_spec_valid.
  { destruct Hget_Hvalid' as (_ & _ & _ & Hrs_get_spec_valid & _).
    exact Hrs_get_spec_valid. }
  assert (ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec')) as Hrs_spec_valid.
  { rewrite Hget_Hspec_eq. exact Hrs_get_spec_valid. }
  wp_auto.
  wp_apply (wp_IsNotFound interface.nil with "[]").
  replace (bool_decide (not_found_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact not_found_error_nil).
  wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iPoseProof (kview.own_meta_valid with "Hown_rs_meta_frag") as "%Hrs_meta_frag_valid".
  destruct Hrs_meta_frag_valid as (_ & _ & _ & Hrs_meta_valid & Hdeletion_timestamp_eq).
  assert (ObjectMetaV.valid ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta')) as Hrs_get_meta_valid.
  { eapply ObjectMetaV.equiv_except_resource_version_valid.
    - apply ObjectMetaV.equiv_except_resource_version_sym. exact Hget_Hmeta_eq.
    - exact Hrs_meta_valid. }
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as (_ & Hrs_kind_valid & _).
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  pose proof (ObjectMetaV.valid_namespace_of_valid _ Hrs_get_meta_valid) as Hrs_namespace_valid.
  pose proof (ObjectMetaV.valid_name_of_valid _ Hrs_get_meta_valid) as Hrs_name_valid.
  pose proof (ObjectMetaV.valid_uid_of_valid _ Hrs_get_meta_valid) as Hrs_uid_valid.
  pose proof (valid_namespace_slash_free _ Hrs_namespace_valid) as Hrs_namespace_slash_free.
  pose proof (valid_name_slash_free _ Hrs_name_valid) as Hrs_name_slash_free.
  pose proof (valid_uid_slash_free _ Hrs_uid_valid) as Hrs_uid_slash_free.
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key.
    rewrite elem_of_filter.
    split.
    - intros Hkey_in. split; [|done].
      apply elem_of_list_to_set in Hkey_in.
      apply list_elem_of_fmap_1 in Hkey_in as (pod & Hkey_eq & _).
      subst key.
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey_in]. done. }
  assert (ReplicaSetV.key rs = ReplicaSetV.key rs_get) as Hrs_key_eq.
  { exact Hget_Hkey_eq. }
  assert (rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Hrs_uid_eq.
  { symmetry. apply ObjectMetaV.equiv_except_resource_version_uid. exact Hget_Hmeta_eq. }
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_terminating_children_frag".
  wp_apply (common.wp_FilterPodsByOwner_uniform with
    "[$Hdeepown_m_l_rs $Hown_pod_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done. }
  iIntros (all_sl all_ptrs all_pods dq') "(Hall_sl & Hall_deepown_pods & %Hall_meta_perm & %Hall_valid & %Hall_nodup &
    Hdeepown_m_l_rs & Hall_meta_frags & Hown_children_frag & Hown_terminating_children_frag)".
  wp_auto.
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & Hactive_deepown_pods)".
  wp_auto.
  iDestruct (big_sepL_filter_partition is_pod_alive
    (λ pod, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
      pod.(PodV.ObjectMeta')) all_pods with "Hall_meta_frags")
    as "[Hactive_meta_frags Hinactive_meta_frags]".
  assert (PodV.key <$> all_pods ≡ₚ PodV.key <$> pods) as Hall_key_perm.
  { apply pod_key_meta_perm. exact Hall_meta_perm. }
  iAssert (([∗ list] pod ∈ all_pods, own_unreserved_key_frag γ (PodV.key pod)))%I
    with "[Hown_pod_unreserved_key_frags]" as "#Hall_unreserved_key_frags".
  { rewrite (own_unreserved_key_frag_list_as_keys γ all_pods).
    rewrite (big_sepL_permutation (own_unreserved_key_frag γ)
      (PodV.key <$> all_pods) (PodV.key <$> pods) Hall_key_perm).
    iEval (rewrite (own_unreserved_key_frag_list_as_keys γ pods))
      in "Hown_pod_unreserved_key_frags".
    iExact "Hown_pod_unreserved_key_frags". }
  iDestruct (big_sepL_filter_partition is_pod_alive
    (λ pod, own_unreserved_key_frag γ (PodV.key pod)) all_pods with "Hall_unreserved_key_frags")
    as "[#Hactive_unreserved_key_frags #Hinactive_unreserved_key_frags]".
  assert (list_to_set (C:=gset KKey.t)
      (PodV.key <$> (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods)) =
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods)) as Hchildren_keys_eq.
  { rewrite list_to_set_pod_key_filter_partition.
    rewrite Hall_key_perm. done. }
  iAssert (own_children_frag γ (ReplicaSetV.key rs_get)
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (C:=gset KKey.t)
        (PodV.key <$> (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods))))%I
    with "[Hown_children_frag]" as "Hown_children_frag".
  { rewrite Hchildren_keys_eq.
    iExact "Hown_children_frag". }
  iDestruct "Hdeepown_m_l_rs" as (rs_meta_c) "[Hrs_meta_l Hdeepown_m_rs]".
  iNamedPrefix "Hdeepown_m_rs" "Hrs_meta_".
  assert (rs_meta_c.(v1.ObjectMeta.DeletionTimestamp') = null) as Hrs_deletion_timestamp_null.
  { apply Hrs_meta_Hdeepown_deletiontimestamp_none.
    rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  assert (rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None)
    as Hdeletion_timestamp_eq_get.
  { rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  wp_auto.
  rewrite Hrs_deletion_timestamp_null.
  wp_auto.
  iEval (rewrite Hdeletion_timestamp_eq_get) in "Hrs_meta_Hdeepown_deletiontimestamp_some".
  iAssert (ObjectMetaV.deepown rs_meta_c rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_Hdeepown_creationtimestamp
      Hrs_meta_Hdeepown_deletiongraceperiodseconds_some
      Hrs_meta_Hdeepown_labels_some Hrs_meta_Hdeepown_annotations_some
      Hrs_meta_Hdeepown_ownerreferences_some Hrs_meta_Hdeepown_finalizers_some
      Hrs_meta_Hdeepown_managedfields_some]" as "Hdeepown_m_rs".
  { rewrite /ObjectMetaV.deepown Hdeletion_timestamp_eq_get.
    iFrame "%". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_l Hdeepown_m_rs]" as "Hdeepown_m_l_rs".
  { iExists rs_meta_c. iFrame. }
  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null with
    "[$Hdeepown_t_l_rs $Hdeepown_m_l_rs $Hdeepown_s_l_rs $Hdeepown_st_l_rs]") as
    "Hdeepown_l_rs".
  pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (n & Hreplicas_eq & _).
  assert (rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n) as Hreplicas_eq_get.
  { rewrite <-Hget_Hspec_eq. exact Hreplicas_eq. }
  assert (length rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58) as Hrs_get_name_short.
  { rewrite (ObjectMetaV.equiv_except_resource_version_name _ _ Hget_Hmeta_eq).
    exact Hrs_name_short. }
  assert (valid_finalizers
      rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    as Hrs_get_template_finalizers_valid.
  { rewrite <-Hget_Hspec_eq. exact Hrs_template_finalizers_valid. }
  assert (NoDup (PodV.key <$>
      (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods))) as Hpartition_nodup.
  { rewrite pod_key_filter_partition_perm. exact Hall_nodup. }
  wp_apply (wp_manageReplicas γ l active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) (filter (λ pod, not (is_pod_alive pod)) all_pods)
    rs_get n Quiescent dq' 1 with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs $Hactive_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done.
    intros pod Hpod.
    apply list_elem_of_filter in Hpod as [Halive _].
    exact Halive. }
  iIntros (pods_managed) "(%Hmanaged_len & Hphase & Hdeepown_l_rs &
    Hmanaged_meta_frags & #Hmanaged_unreserved_key_frags &
    Hown_children_frag)".
  iDestruct "Hphase" as (phase') "Hown_terminating_children_frag".
  wp_auto.
  iAssert (([∗ list] pod ∈ pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta')))%I
    with "[Hmanaged_meta_frags Hinactive_meta_frags]" as "Hpod_meta_frags_post".
  { rewrite big_sepL_app. iFrame. }
  iAssert (([∗ list] pod ∈ pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods,
      own_unreserved_key_frag γ (PodV.key pod)))%I
    with "[Hmanaged_unreserved_key_frags Hinactive_unreserved_key_frags]" as "#Hpod_unreserved_key_frags_post".
  { rewrite big_sepL_app. iFrame "#". }
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_terminating_children_frag".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hpod_meta_frags_post") as "%Hpods'_nodup".
  iAssert (∃ phase, own_terminating_children_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase)%I
    with "[Hown_terminating_children_frag]" as "Hown_terminating_children_frag".
  { iExists phase'. iFrame. }
  iApply ("HΦ" $! (pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods)).
  rewrite /owned_resources /=.
  iFrame "Hown_rs_meta_frag Hown_rs_spec_frag Hpod_meta_frags_post
    Hpod_unreserved_key_frags_post Hown_children_frag Hown_terminating_children_frag".
  iPureIntro. split; first exact Hpods'_nodup.
  left.
  {
    unfold current_state_matches.
    rewrite Hreplicas_eq.
    simpl.
    rewrite list.filter_app.
    assert (filter is_pod_alive (filter (λ pod, not (is_pod_alive pod)) all_pods) = []) as Hfilter_inactive.
    { apply filter_none. intros pod Hpod.
      apply list_elem_of_filter in Hpod as [Hnot_alive _].
      exact Hnot_alive. }
    rewrite Hfilter_inactive app_nil_r.
    exact Hmanaged_len. }
Qed.

End proof.
