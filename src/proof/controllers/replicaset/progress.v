From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get by_index_pod_controller create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.replicaset Require Export get_indirectly_related_pods get_pods_to_delete top_level.
From New.proof.controllers.replicaset Require Export slow_start_batch delete_batch.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Module client_apps_v1 := code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module client_core_v1 := code.k8s_io.client_go.kubernetes.typed.core.v1.v1.
Module client_gentype := code.k8s_io.client_go.gentype.gentype.
Module generic_listers := code.k8s_io.client_go.listers.listers.
Module k8s_api_apps_v1 := code.k8s_io.api.apps.v1.v1.
Module trusted_client_apps_v1 := trusted_code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module trusted_client_core_v1 := trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.
Module trusted_client_gentype := trusted_code.k8s_io.client_go.gentype.gentype.
Module trusted_app_listers := trusted_code.k8s_io.client_go.listers.apps.v1.v1.
Module trusted_generic_listers := trusted_code.k8s_io.client_go.listers.listers.
(* TODO: Remove this workaround once Goose lets a trusted implementation reuse
   the generated named-type token from its own package. The generated gentype
   module imports the trusted Create shim, so the shim cannot import that module
   back without a cycle and instead reconstructs Client with [go.Named]. Goose
   marks generated [Client] opaque, which prevents proof automation from reducing
   type checks in the shim; exposing it makes both spellings normalize alike. *)
Transparent client_gentype.Client.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance clientset_sem : kubernetes.Assumptions :=
  code.controllers.replicaset.replicaset.import_kubernetes_Assumption.
#[local] Instance client_core_v1_sem : client_core_v1.Assumptions :=
  kubernetes.import_core_v1_Assumption.
#[local] Instance client_apps_v1_sem : client_apps_v1.Assumptions :=
  kubernetes.import_apps_v1_Assumption.
#[local] Instance client_gentype_sem : client_gentype.Assumptions :=
  client_core_v1.import_gentype_Assumption.
#[local] Instance app_listers_sem : app_listers.Assumptions :=
  code.controllers.replicaset.replicaset.import_listers_apps_v1_Assumption.
#[local] Instance generic_listers_sem : generic_listers.Assumptions :=
  app_listers.import_listers_Assumption.
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

Context `{!KObjectV.ObjectInterfaceAssumptions}.

Lemma wp_manageReplicas γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    sl rs_l ptrs active_pods inactive_pods rs n has_terminating_children dq1 dq2 :
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
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') has_terminating_children ∗
      "%Hrs_meta_valid" ∷ ⌜ ObjectMetaV.valid ReplicaSetV.kind rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hrs_spec_valid" ∷ ⌜ ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec') ⌝ ∗
      "%Hactive_pods" ∷ ⌜ ∀ pod, pod ∈ active_pods → is_pod_alive pod ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hrs_template_finalizers_valid" ∷ ⌜ valid_finalizers
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝ ∗
      "%Hburst" ∷ ⌜ 0 < sint.Z burst < 2^31 ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (PodV.key <$> (active_pods ++ inactive_pods)) ⌝
  }}}
    @! replicaset.manageReplicas #ctx #kube_client #burst #sl #rs_l
  {{{ pods', RET #interface.nil;
      ⌜ length pods' = capped_replica_count (length active_pods) (sint.nat n) (sint.nat burst) ⌝ ∗
      ⌜ ∀ pod, pod ∈ pods' → is_pod_alive pod ⌝ ∗
      (∃ has_terminating_children', own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') has_terminating_children') ∗
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
  - (* too few replicas: create [diff] pods concurrently through slowStartBatch *)
    (* the burst cap: [d] is the number of pods to create this sync *)
    try wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
      (∃ d : w64, "diff" ∷ diff_ptr ↦ d ∗
        "%Hd" ∷ ⌜ sint.Z d = Z.min (sint.Z n - sint.Z (slice.len sl)) (sint.Z burst) ⌝) ∗ _)%I
      with "[-]").
    { wp_if_destruct.
      - try wp_auto. iSplitR; first done. iSplitL "diff".
        { iExists burst. iFrame "diff". iPureIntro. rewrite Z.min_r; word. }
        iNamedAccu.
      - try wp_auto. iSplitR; first done. iSplitL "diff".
        { iExists _. iFrame "diff". iPureIntro. rewrite Z.min_l; word. }
        iNamedAccu. }
    iIntros (?) "(-> & Hdiff & H)". iNamed "H". iDestruct "Hdiff" as (d) "[diff %Hd]".
    assert (0 < sint.Z d ≤ sint.Z burst) as [Hd_pos Hd_le_burst] by lia.
    assert (sint.Z d ≤ sint.Z n - sint.Z (slice.len sl)) as Hd_le_diff by lia.
    (* The pod-creating closure runs in forked goroutines, which share the
       ReplicaSet's metadata and template read-only. *)
    iPersist "rs ctx kubeClient".
    (* Only the ReplicaSet's scalar metadata is shared with the goroutines:
       [NewControllerRef] reads its name and UID, [GetPodFromTemplate] its name,
       and the create call its namespace.  The rest of the metadata stays out of
       the closure, which is what lets this be discarded without assuming
       anything about the opaque timestamp and managed-field predicates. *)
    iDestruct (ObjectMetaV.deepown_l_own_scalars with "Hdeepown_m_l_rs")
      as (rs_meta_c) "[Hown_scalars_rs _]".
    iMod (objectmeta_own_scalars_persist with "Hown_scalars_rs")
      as "#Hown_scalars_rs".
    iDestruct (struct_fields_split with "Hrs_spec_l") as "[H %Hrs_spec_l_not_null]".
    iNamedPrefix "H" "Hrs_".
    iAssert (PodTemplateSpecV.deepown_l
        ((ReplicaSetV.spec_ptr rs_l).[v1.ReplicaSetSpec.t, "Template"])
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template') dq2)%I
      with "[Hrs_Template Hrs_Hdeepown_template]" as "Htemplate".
    { iExists _. iFrame. }
    iDestruct (PodTemplateSpecV.deepown_l_own_template with "Htemplate")
      as (template_c) "[Htemplate _]".
    iMod (pod_template_spec_own_template_persist with "Htemplate")
      as "#Htemplate".
    assert (valid_name ReplicaSetV.kind
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name')) as Hrs_name_valid.
    { unfold ObjectMetaV.valid in Hrs_meta_valid. tauto. }
    unfold valid_name, ReplicaSetV.kind in Hrs_name_valid.
    destruct Hrs_name_valid as [[Hkind _]|[[Hkind|[Hkind|Hkind]] Hrs_name_valid]];
      try discriminate.
    iAssert (is_pkg_init code.k8s_io.api.apps.v1.pkg_id.v1) as "#Happs_v1_init".
    { iPkgInit. }
    try wp_auto.
    rename err_ptr into err_outer_ptr.
    wp_apply (wp_slowStartBatch γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
      (list_to_set (PodV.key <$> (active_pods ++ inactive_pods)))
      with "[$Hown_children_frag]").
    { iFrame "#".
      iSplit; last (iPureIntro; split; [lia|word]).
      (* the closure creates one pod per call *)
      iIntros "!>" (Φ') "Hau".
      wp_pures. wp_auto.
      wp_bind ((global_addr k8s_api_apps_v1.SchemeGroupVersion) @! (go.PointerType schema.GroupVersion) @! "WithKind" #"ReplicaSet"%go)%E.
      wp_apply (New.proof.k8s_io.api.apps.v1.wp_SchemeGroupVersion__WithKind
        (schema_sem := @code.k8s_io.api.apps.v1.v1.import_schema_Assumption
          _ _ _ _ object_apps_v1_sem) "ReplicaSet"%go with
        "[$Happs_v1_init]").
      iIntros (gvk) "%Hgvk". wp_auto.
      destruct Hgvk as (Hgvk_g & Hgvk_v & Hgvk_k).
      wp_bind (@! replicaset.apis_meta_v1.NewControllerRef
        #(interface.mk_ok (go.PointerType k8s_api_apps_v1.ReplicaSet) (#rs_l)) #gvk)%E.
      change (replicaset.apis_meta_v1.NewControllerRef) with v1.NewControllerRef.
      wp_apply (v1.wp_NewControllerRef_ReplicaSet with "[]").
      { iFrame "#". iPureIntro. split_and!; done. }
      iIntros (controller_ref_l controller_ref)
        "(Hdeepown_l_controller_ref & %Hcontroller_ref_valid & %Hcontroller_ref_wf & _)".
      wp_auto. rewrite Hgvk_k in Hcontroller_ref_valid.
      change ((rs_l.[k8s_api_apps_v1.ReplicaSet.t, "Spec"]).[k8s_api_apps_v1.ReplicaSetSpec.t, "Template"]) with
        ((ReplicaSetV.spec_ptr rs_l).[v1.ReplicaSetSpec.t, "Template"]).
      wp_apply (controller.wp_GetPodFromTemplate
        ((ReplicaSetV.spec_ptr rs_l).[v1.ReplicaSetSpec.t, "Template"])
        (interface.mk (go.PointerType k8s_api_apps_v1.ReplicaSet) #rs_l)
        controller_ref_l DfracDiscarded DfracDiscarded
        (ReplicaSetSpecV.Template' (ReplicaSetV.Spec' rs)) rs_l
        (KObjectV.ReplicaSet rs) (Some controller_ref) template_c rs_meta_c with
        "[Hdeepown_l_controller_ref]").
      { iFrame "#". iFrame "Hdeepown_l_controller_ref".
        iPureIntro. split;
          [apply KObjectV.valid_interface_ReplicaSet|exact Hrs_name_valid]. }
      iIntros (pod_l) "(Hdeepown_l_pod & _ & _)".
      set pod := controller.generated_pod
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') (Some [controller_ref]).
      assert (obj_parent_ref_is (KObjectV.Pod pod) "ReplicaSet"%go
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name')
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Hpr.
      { apply controller.generated_pod_parent_ref. exact Hcontroller_ref_valid. }
      assert (KObjectV.valid_create "Pod"%go
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') (KObjectV.Pod pod)) as Hvalid.
      { apply controller.generated_pod_valid_create.
        - apply ReplicaSetSpecV.valid_template. exact Hrs_spec_valid.
        - exact Hrs_name_valid.
        - exact Hrs_name_short.
        - exact Hrs_template_finalizers_valid.
        - exact Hcontroller_ref_wf.
        - unfold ObjectMetaV.valid in Hrs_meta_valid. tauto.
        - unfold ObjectMetaV.valid in Hrs_meta_valid. tauto. }
      wp_auto.
      wp_apply (v1.wp_GetNamespace_scalars with "[$Hown_scalars_rs]") as "_".
      wp_method_call. rewrite /kubernetes.Clientset__CoreV1ⁱᵐᵖˡ. wp_call.
      try wp_auto.
      wp_method_call. rewrite /trusted_client_core_v1.CoreV1Client__Podsⁱᵐᵖˡ. wp_call. wp_auto.
      wp_method_call. rewrite /trusted_client_gentype.Client__Createⁱᵐᵖˡ decide_True; try reflexivity.
      rewrite /trusted_client_gentype.clientCreate. wp_call.
      rewrite /trusted_client_gentype.clientType. wp_auto.
      change (go.PointerType
        trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.api_core_v1.Pod)
        with (go.PointerType code.k8s_io.api.core.v1.v1.Pod).
      change (go.PointerType trusted_code.k8s_io.client_go.gentype.api_core_v1.Pod)
        with (go.PointerType code.k8s_io.api.core.v1.v1.Pod).
      rewrite !decide_True; try reflexivity.
      wp_auto.
      wp_bind.
      iApply (wp_State__PodCreate_nameless_au γ l
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') pod_l pod
        (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')).
      iFrame "#".
      iSplit; [iPureIntro; exact Hvalid|].
      iSplit; [iPureIntro; unfold pod, controller.generated_pod, controller.generated_pod_meta; done|].
      iSplit; [iPureIntro; rewrite /ReplicaSetV.key /ReplicaSetV.meta_key /=; done|].
      iSplit; [iPureIntro; exact Hpr|].
      iSplitL "Hdeepown_l_pod".
      { unfold object_core_v1_sem. iExact "Hdeepown_l_pod". }
      rewrite /create_pod_au.
      iMod "Hau" as (children) "[Hown_children_frag Hclose]".
      iModIntro. iExists children. iFrame "Hown_children_frag".
      iIntros (pod_l' pod' key uid)
        "(%Hvalid' & %Hcreated' & %Hkey_eq & %Hkey_fresh & %Huid_eq & Hdeepown_l' &
          Hmeta & Hspec & Hstatus & #Hunres & Hfrag & Hgrand)".
      subst key uid.
      iMod ("Hclose" $! pod' with "[$Hfrag $Hmeta $Hunres]") as "HΦ'".
      { iPureIntro. split_and!; [exact Hvalid'| |exact Hkey_fresh].
        unfold is_pod_alive.
        unfold PodV.created in Hcreated'.
        destruct Hcreated' as (_ & Hmeta_created & _ & _).
        unfold ObjectMetaV.created in Hmeta_created.
        simpl in Hmeta_created.
        destruct Hmeta_created as (_ & _ & _ & Hdeletion & _).
        exact Hdeletion. }
      iModIntro. iNext.
      wp_auto. rewrite decide_True; try reflexivity. wp_auto.
      iApply "HΦ'". }
    iIntros (successes created) "(%Hcreated_len & Hres)". iNamed "Hres".
    wp_auto.
    iApply ("HΦ" $! (active_pods ++ created)).
    iSplit.
    { iPureIntro.
      assert (length active_pods < sint.nat n)%nat as Hlt by (rewrite -Hlen Hsl_len1; word).
      assert (Z.of_nat (sint.nat d) = sint.Z d) as Hd_Z by word.
      assert (Z.of_nat (sint.nat n) = sint.Z n) as Hn_Z by word.
      assert (Z.of_nat (sint.nat burst) = sint.Z burst) as Hburst_Z by word.
      assert (Z.of_nat (length active_pods) = sint.Z (slice.len sl)) as Hactive_Z by (rewrite -Hlen Hsl_len1; word).
      unfold capped_replica_count. rewrite (decide_True _ _ Hlt).
      rewrite length_app Hcreated_len. lia. }
    iSplit.
    { iPureIntro. intros pod Hpod. apply elem_of_app in Hpod as [Hin|Hin].
      - apply Hactive_pods. exact Hin.
      - apply Hcreated_alive. exact Hin. }
    iSplitL "Hown_terminating_children_frag".
    { iExists has_terminating_children. iFrame "Hown_terminating_children_frag". }
    iSplitL "Hown_active_pod_meta_frags Hcreated_meta_frags".
    { rewrite big_sepL_app. iFrame. }
    iSplit.
    { rewrite big_sepL_app. iFrame "#". }
    iExactEq "Hown_children_frag". f_equal.
    rewrite !fmap_app. Timeout 10 set_solver.
  - wp_if_destruct.
    2 : { iApply ("HΦ" $! active_pods).
      iSplit.
      { iPureIntro.
        assert (length active_pods = sint.nat n) as Heq by (rewrite -Hlen Hsl_len1; word).
        unfold capped_replica_count. destruct (decide _); lia. }
      iSplit; first (iPureIntro; exact Hactive_pods).
      iSplitL "Hown_terminating_children_frag".
      { iExists has_terminating_children. iFrame "Hown_terminating_children_frag". }
	      iFrame "Hown_active_pod_meta_frags
	        Hown_active_pod_unreserved_key_frags Hown_children_frag".
    }
    (* the burst cap: [d] is the number of pods to delete this sync *)
    assert (0 < sint.Z (slice.len sl) - sint.Z n) as Hdiff_pos by word.
    try wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
      (∃ d : w64, "diff" ∷ diff_ptr ↦ d ∗
        "%Hdelete_count" ∷ ⌜ sint.Z d = Z.min (sint.Z (slice.len sl) - sint.Z n) (sint.Z burst) ⌝) ∗ _)%I
      with "[-]").
    { wp_if_destruct.
      - try wp_auto. iSplitR; first done. iSplitL "diff".
        { iExists burst. iFrame "diff". iPureIntro. rewrite Z.min_r; word. }
        iNamedAccu.
      - try wp_auto. iSplitR; first done. iSplitL "diff".
        { iExists _. iFrame "diff". iPureIntro. rewrite Z.min_l; word. }
        iNamedAccu. }
    iIntros (?) "(-> & Hdiff & H)". iNamed "H". iDestruct "Hdiff" as (d) "[diff %Hdelete_count]".
    assert (0 < sint.Z d ≤ sint.Z burst) as [Hd_pos Hd_le_burst] by lia.
    assert (sint.Z d ≤ sint.Z (slice.len sl) - sint.Z n) as Hd_le_diff by lia.
    assert (Z.of_nat (sint.nat d) = sint.Z d) as Hd_Z by word.
    assert (Z.of_nat (sint.nat n) = sint.Z n) as Hn_Z by word.
    assert (Z.of_nat (sint.nat burst) = sint.Z burst) as Hburst_Z by word.
    try wp_auto.
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
	  wp_bind (@! replicaset.getPodsToDelete #sl #related_sl #d)%E.
	  wp_apply (wp_getPodsToDelete sl ptrs active_pods related_sl related_ptrs related_pods
	    d dq1 related_dq with
	    "[$Hsl $Hdeepown_l_active_pods $Hrelated_sl $Hrelated_pods]").
	  { iFrame "#". iPureIntro. word. }
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
    (* the pods targeted for deletion are the first [d] sorted pods *)
    set targeted := take (sint.nat d) active_pods.
    set tptrs := take (sint.nat d) ptrs.
    set rest := (list_to_set (C:=gset KKey.t) (PodV.key <$> (drop (sint.nat d) active_pods ++ inactive_pods))).
    assert (sint.nat d ≤ length active_pods) as Hd_le.
    { rewrite -Hlen Hsl_len1. lia. }
    assert (length targeted = sint.nat d) as Htargeted_len.
    { subst targeted. rewrite length_take. lia. }
    assert (length tptrs = sint.nat d) as Htptrs_len.
    { subst tptrs. rewrite length_take. lia. }
    assert (NoDup (PodV.key <$> (active_pods ++ inactive_pods))) as Hnodup_all by exact Hnodup.
    assert (NoDup (PodV.key <$> targeted)) as Htargeted_nodup.
    { rewrite -(take_drop (sint.nat d) active_pods) -app_assoc fmap_app in Hnodup_all.
      apply list.NoDup_app in Hnodup_all as (Hnd & _ & _). exact Hnd. }
    assert (list_to_set (C:=gset KKey.t) (PodV.key <$> targeted) ## rest) as Hdisjoint.
    { rewrite -(take_drop (sint.nat d) active_pods) -app_assoc fmap_app in Hnodup_all.
      apply list.NoDup_app in Hnodup_all as (_ & Hdisj & _).
      rewrite elem_of_disjoint. intros key Hk1 Hk2.
      rewrite elem_of_list_to_set in Hk1. rewrite elem_of_list_to_set in Hk2.
      exact (Hdisj key Hk1 Hk2). }
    assert (list_to_set (C:=gset KKey.t) (PodV.key <$> (active_pods ++ inactive_pods)) =
        rest ∪ list_to_set (C:=gset KKey.t) (PodV.key <$> targeted)) as Hchildren_split.
    { subst rest targeted. rewrite -{1}(take_drop (sint.nat d) active_pods) -app_assoc !fmap_app.
      Timeout 10 set_solver. }
    iEval (rewrite Hchildren_split) in "Hown_children_frag".
    (* split the per-pod resources between targeted and remaining pods *)
    iEval (rewrite -{1}(take_drop (sint.nat d) active_pods) big_sepL_app) in "Hown_active_pod_meta_frags".
    iDestruct "Hown_active_pod_meta_frags" as "[Hmeta_targeted Hmeta_rest]".
    iEval (rewrite -{1}(take_drop (sint.nat d) active_pods) big_sepL_app) in "Hown_sorted_pod_unreserved_key_frags".
    iDestruct "Hown_sorted_pod_unreserved_key_frags" as "[#Hunres_targeted #Hunres_rest]".
    iEval (rewrite -{1}(take_drop (sint.nat d) ptrs) -{1}(take_drop (sint.nat d) active_pods)) in "Hdeepown_l_active_pods".
    iDestruct (big_sepL2_app_inv with "Hdeepown_l_active_pods") as "[Hdeepown_targeted _]".
    { left. rewrite !length_take. lia. }
    fold targeted tptrs.
    iPersist "ctx kubeClient".
    (* errCh := make(chan error, diff) *)
    wp_apply chan.wp_make2; first word.
    iIntros (ch γch) "(#His_chan & _ & Hoc)".
    assert (d ≠ W64 0) as Hd_nz.
    { intros Hd0. rewrite Hd0 in Hd_pos. word. }
    iEval (rewrite (decide_False _ _ Hd_nz)) in "Hoc".
    try wp_auto.
    iMod (init_WaitGroup delete_wgN with "wg") as (γwg) "(#His_wg & Hwg_ctr & Hwg_waiters)".
    wp_apply (wp_WaitGroup__Add with "[$His_wg]"). try iPkgInit.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    assert (sint.Z (slice.len sl) = Z.of_nat (length active_pods)) as Hsl_Z.
    { rewrite -Hlen Hsl_len1. word. }
    assert (sint.Z d < 2^31) as Hd_bound by lia.
    iExists (W32 0). iFrame "Hwg_ctr". iSplit; [word|].
    iRight. iFrame "Hwg_waiters". iIntros "Hwg_waiters Hwg_ctr".
    iMod "Hmask" as "_". iModIntro.
    try wp_auto.
    (* ghost state for the batch *)
    iMod own_tok_auth_alloc as (γd) "Hauth_d".
    iMod (own_tok_auth_add (sint.nat d) with "Hauth_d") as "[Hauth_d Hdone_pool]".
    iPersist "Hauth_d".
    iMod (ghost_var_alloc false) as (γdr) "[Hdrained Hdrained_inv]".
    iMod (alloc_pending_markers targeted Htargeted_nodup) as (γm) "[Hpending_auth Hpending_elems]".
    iMod (inv_alloc delete_batchN _
      (delete_batch_inv_body γ γwg γd γm γdr d (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rest)
      with "[Hwg_ctr Hdone_pool Hdrained_inv Hpending_auth Hown_children_frag
            Hown_terminating_children_frag]") as "#Hbinv".
    { iNext. iExists _, 0%nat, 0%nat, false, (list_to_set (PodV.key <$> targeted)).
      iFrame "Hwg_ctr Hpending_auth".
      rewrite Nat.sub_0_r Nat.add_0_r. iFrame "Hdone_pool Hdrained_inv".
      iSplitR; [iPureIntro; rewrite Z.sub_0_r; word|].
      iSplitR.
      { iPureIntro. rewrite (size_list_to_set _ Htargeted_nodup) length_fmap. lia. }
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iPureIntro; done|].
      iSplitR; [iPureIntro; discriminate|].
      iRight. iSplit; [done|]. iFrame "Hown_children_frag". iExists _. iFrame. }
    (* fork one goroutine per targeted pod *)
    iAssert (∃ (i : w64) (pod_l : loc),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod_l ∗
      "Hdeepown_targeted" ∷ ([∗ list] ptr;pod ∈ drop (sint.nat i) tptrs; drop (sint.nat i) targeted,
        PodV.deepown_l ptr pod dq1) ∗
      "Hmeta_targeted" ∷ ([∗ list] pod ∈ drop (sint.nat i) targeted,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hpending_elems" ∷ ([∗ list] pod ∈ drop (sint.nat i) targeted, PodV.key pod ↪[γm] ()) ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len (slice.slice sl loc (W64 0) d)) ⌝)%I
      with "[i pod Hdeepown_targeted Hmeta_targeted Hpending_elems]" as "Hloop_inv".
    { iExists (W64 0), (zero_val loc). rewrite !drop_0. iFrame. iPureIntro. rewrite /slice.slice /=. word. }
    wp_for "Hloop_inv". wp_if_destruct.
    + rewrite decide_True; [word|].
      list_elem tptrs (sint.Z i) as this_ptr.
      wp_apply (wp_load_slice_index with "[$Hslice]"); [word|eauto|].
      iIntros "Hslice". wp_auto.
      assert (tptrs !! sint.nat i = Some this_ptr) as Hlookup_tptrs by exact Hthis_ptr_lookup.
      assert (∃ this_pod, targeted !! sint.nat i = Some this_pod) as [this_pod Hlookup_targeted].
      { apply lookup_lt_is_Some_2. rewrite Htargeted_len -Htptrs_len.
        eapply lookup_lt_Some. exact Hlookup_tptrs. }
      assert (this_pod ∈ active_pods) as Hthis_pod_in.
      { subst targeted. apply lookup_take_Some in Hlookup_targeted as [Hlookup _].
        eapply list_elem_of_lookup_2. exact Hlookup. }
      assert (drop (sint.nat i) tptrs = this_ptr :: drop (S (sint.nat i)) tptrs) as Hdrop_tptrs.
      { apply drop_S. exact Hlookup_tptrs. }
      assert (drop (sint.nat i) targeted = this_pod :: drop (S (sint.nat i)) targeted) as Hdrop_targeted.
      { apply drop_S. exact Hlookup_targeted. }
      iEval (rewrite Hdrop_tptrs Hdrop_targeted big_sepL2_cons) in "Hdeepown_targeted".
      iDestruct "Hdeepown_targeted" as "[Hdeepown_this Hdeepown_targeted]".
      iEval (rewrite Hdrop_targeted big_sepL_cons) in "Hmeta_targeted".
      iDestruct "Hmeta_targeted" as "[Hmeta_this Hmeta_targeted]".
      iEval (rewrite Hdrop_targeted big_sepL_cons) in "Hpending_elems".
      iDestruct "Hpending_elems" as "[Helem_this Hpending_elems]".
      iDestruct (big_sepL_elem_of _ _ this_pod with "Hunres_targeted") as "#Hunres_this".
      { subst targeted. eapply list_elem_of_lookup_2. exact Hlookup_targeted. }
      wp_apply (wp_fork with "[Hdeepown_this Hmeta_this Helem_this]").
      { (* the goroutine deleting [this_pod] *)
        wp_pures.
        wp_apply wp_with_defer as "%defer defer". simpl subst.
        wp_auto.
        iPoseProof (PodV.deepown_l_split with "Hdeepown_this") as
          "(%Hthis_ptr_not_null & Hdeepown_t_l_pod & Hdeepown_m_l_pod & Hdeepown_s_l_pod & Hdeepown_st_l_pod)".
        wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
        wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
        wp_apply (common.wp_NewDeleteOptionsWithUID). iIntros (do_c) "(Hdeepown_do & %Hvalid_do)". wp_auto.
        wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
        wp_method_call. rewrite /kubernetes.Clientset__CoreV1ⁱᵐᵖˡ. wp_call.
        try wp_auto.
        wp_method_call. rewrite /trusted_client_core_v1.CoreV1Client__Podsⁱᵐᵖˡ. wp_call. wp_auto.
        wp_method_call. rewrite /trusted_client_gentype.Client__Deleteⁱᵐᵖˡ decide_True; try reflexivity.
        rewrite /trusted_client_gentype.clientDelete. wp_call.
        rewrite /trusted_client_gentype.clientType. wp_auto.
        wp_bind.
        iApply (wp_State__PodDelete_au γ l (PodV.key this_pod)
          this_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
          this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') do_c
          (delete_options_with_uid this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
          this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') this_pod.(PodV.ObjectMeta')
          (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')).
        iFrame "#".
        iSplitL "Hdeepown_do"; [iExact "Hdeepown_do"|].
        iSplit; [iPureIntro; rewrite /PodV.key /PodV.meta_key /=; done|].
        iSplit; [iPureIntro; rewrite /delete_preconditions_match /delete_options_with_uid /=; done|].
        iSplit; [iPureIntro; rewrite /delete_options_preconditions_resource_version_none /delete_options_with_uid /=; done|].
        iSplitL "Hmeta_this"; [iExact "Hmeta_this"|].
        (* the linearization point: open the batch invariant *)
        iInv "Hbinv" as ">Hi" "Hclose_inv".
        iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask".
        iNamedSuffix "Hi" "_inv".
        iDestruct (ghost_map_lookup with "Hpending_auth_inv Helem_this") as %Hlookup_pending.
        apply lookup_gset_to_gmap_Some in Hlookup_pending as [Hin_pending _].
        pose proof (pending_size_pos _ _ Hin_pending) as Hpending_pos.
        iDestruct "Hres_inv" as "[%Hdr|[%Hdr Hres_inv]]".
        { exfalso. specialize (Hdrained_inv Hdr). lia. }
        subst drained.
        iDestruct "Hres_inv" as "[Hown_children_frag_inv Hterm_inv]".
        iDestruct "Hterm_inv" as (htc) "Hterm_inv".
        iExists _, _. iFrame "Hown_children_frag_inv Hterm_inv".
        iSplit; [iPureIntro; apply elem_of_union_r; done|].
        iIntros "(Hown_children_frag & _ & Hterm)".
        iMod "Hmask" as "_".
        iMod (ghost_map_delete with "Hpending_auth_inv Helem_this") as "Hpending_auth_inv".
        rewrite -gset_to_gmap_difference_singleton.
        replace (sint.nat d - ndeleted + ndone)%nat
          with ((sint.nat d - (ndeleted + 1) + ndone) + 1)%nat by lia.
        iDestruct (own_toks_add with "Hdone_pool_inv") as "[Hdone_pool_inv Htok_d]".
        iEval (rewrite (union_pending_delete rest pending (PodV.key this_pod) Hin_pending Hpending_rest_inv))
          in "Hown_children_frag".
        iMod ("Hclose_inv" with
          "[Hwg_ctr_inv Hpending_auth_inv Hdone_pool_inv Hdrained_var_inv Hown_children_frag Hterm]") as "_".
        { iNext. iExists ctr, (ndeleted + 1)%nat, ndone, false, (pending ∖ {[PodV.key this_pod]}).
          iFrame "Hwg_ctr_inv Hpending_auth_inv Hdone_pool_inv Hdrained_var_inv".
          iSplitR; [iPureIntro; done|].
          iSplitR; [iPureIntro; rewrite (pending_size_delete _ _ Hin_pending); lia|].
          iSplitR; [iPureIntro; lia|].
          iSplitR.
          { iPureIntro. apply disjoint_difference_l2. exact Hpending_rest_inv. }
          iSplitR; [iPureIntro; discriminate|].
          iRight. iSplit; [done|]. iFrame "Hown_children_frag". iExists _. iFrame "Hterm". }
        iModIntro. iNext.
        wp_auto.
        (* the deferred wg.Done() *)
        wp_apply (wp_WaitGroup__Done with "[$His_wg]"). try iPkgInit.
        iInv "Hbinv" as ">Hi" "Hclose_inv".
        iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
        iNamedSuffix "Hi" "_wg".
        iCombine "Hdone_pool_wg Htok_d" as "Hdone_pool_wg".
        iCombine "Hauth_d Hdone_pool_wg" gives %Hdone_le.
        assert (Z.of_nat (sint.nat d) = sint.Z d) as Hd_nat by word.
        iExists _. iFrame "Hwg_ctr_wg".
        iSplit; [iPureIntro; word|].
        iIntros "Hwg_ctr_wg".
        iMod "Hmask" as "_".
        iEval (rewrite -Nat.add_assoc) in "Hdone_pool_wg".
        iMod ("Hclose_inv" with
          "[Hwg_ctr_wg Hpending_auth_wg Hdone_pool_wg Hdrained_var_wg Hres_wg]") as "_".
        { iNext. iExists _, _, (_ + 1)%nat, _, _.
          iFrame "Hwg_ctr_wg Hpending_auth_wg Hdone_pool_wg Hdrained_var_wg Hres_wg".
          iPureIntro. split_and!.
          all: try word.
          all: try lia.
          all: try done.
          all: intros Hdr; exfalso; specialize (Hdrained_wg Hdr); lia. }
        iModIntro. wp_auto. done. }
      wp_for_post. iFrame.
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc.
      { rewrite /slice.slice /= in Hi. word. }
      rewrite Hsucc. iFrame. iPureIntro. rewrite /slice.slice /=. rewrite /slice.slice /= in Hi. word.
    + (* all goroutines forked: wait, then inspect the (empty) error channel *)
      try wp_auto.
      iApply fupd_wp.
      iMod fupd_mask_subseteq as "Hmask";
        last iMod (alloc_wait_token _ _ _ 0 with "His_wg Hwg_waiters") as "[Hwg_waiters Hwait_tok]".
      { solve_ndisj. }
      { word. }
      iMod "Hmask" as "_". iModIntro.
      wp_apply (wp_WaitGroup__Wait with "[$His_wg $Hwait_tok]"). try iPkgInit.
      iInv "Hbinv" as ">Hi" "Hclose_inv".
      iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
      iNamedSuffix "Hi" "_inv".
      iExists _. iFrame "Hwg_ctr_inv".
      iIntros "%Hctr_zero Hwg_ctr_inv".
      iDestruct (ghost_var_agree with "Hdrained Hdrained_var_inv") as %<-.
      iDestruct "Hres_inv" as "[%Hdr|[_ Hres_inv]]"; first discriminate.
      iDestruct "Hres_inv" as "[Hown_children_frag Hterm]".
      iCombine "Hauth_d Hdone_pool_inv" gives %Hpool_le.
      assert (Z.of_nat (sint.nat d) = sint.Z d) as Hd_nat by word.
      assert (pending = ∅) as Hpending_empty.
      { apply leibniz_equiv, size_empty_inv. lia. }
      subst pending. iEval (rewrite right_id_L) in "Hown_children_frag".
      iMod (ghost_var_update_halves true with "Hdrained Hdrained_var_inv")
        as "[Hdrained Hdrained_var_inv]".
      iMod "Hmask" as "_".
      iMod ("Hclose_inv" with
        "[Hwg_ctr_inv Hpending_auth_inv Hdone_pool_inv Hdrained_var_inv]") as "_".
      { iNext. iExists _, ndeleted, ndone, true, ∅.
        iFrame "Hwg_ctr_inv Hpending_auth_inv Hdone_pool_inv Hdrained_var_inv".
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; intros _; lia|].
        iLeft. done. }
      iModIntro. iIntros "Hwait_tok".
      try wp_auto.
      wp_apply chan.wp_select_nonblocking. simpl.
      iSplit.
      { (* the receive case never fires: the channel is empty *)
        iSplit; last done.
        iExists interface.t, ch, γch, _, _, _.
        iSplitR; first done. iFrame "His_chan".
        iSplit; last done.
        iApply fupd_mask_intro; [solve_ndisj|]. iIntros "_". iNext.
        iExists (chanstate.Buffered []). by iFrame "Hoc". }
      try wp_auto.
      iDestruct "Hterm" as (htc) "Hterm".
      iApply ("HΦ" $! (drop (sint.nat d) active_pods)).
      iSplit.
      { iPureIntro.
        assert (sint.nat n < length active_pods)%nat as Hgt by (rewrite -Hlen Hsl_len1; word).
        assert (Z.of_nat (length active_pods) = sint.Z (slice.len sl)) as Hactive_Z by (rewrite -Hlen Hsl_len1; word).
        pose proof (Permutation_length Hpods_perm) as Hlen_perm.
        unfold capped_replica_count.
        destruct (decide (length original_active_pods < sint.nat n)%nat) as [Hlt|_]; first lia.
        rewrite length_drop. lia. }
      iSplit.
      { iPureIntro. intros pod Hpod. apply Hactive_pods.
        apply list_elem_of_lookup_1 in Hpod as (j & Hlookup_pod).
        apply (list_elem_of_lookup_2 active_pods (sint.nat d + j)%nat).
        rewrite lookup_drop in Hlookup_pod. exact Hlookup_pod. }
      iSplitL "Hterm".
      { iExists htc. iFrame "Hterm". }
      iFrame "Hmeta_rest Hunres_rest Hown_children_frag".
Qed.

Lemma wp_syncReplicaSet_progress γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64) namespace name rs dq
    pods :
  ⊢ progress_spec γ l ctx kube_client burst namespace name rs dq pods.
Proof.
  unfold progress_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_pod_meta_frags
    Hown_children_frag Hown_terminating_children_frag".
  unfold input_requirement in Hinput_requirement.
  destruct Hinput_requirement as [Hrs_name_short Hrs_template_finalizers_valid].
  wp_pures.
  wp_alloc_auto.
  rewrite exception_do_unseal /exception_do_def.
  wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  wp_alloc_auto. wp_pures.
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_load. wp_pure. wp_pure.
  wp_load. wp_pure. wp_pure.
  wp_load. wp_pure.
  wp_bind (null @! (go.PointerType app_listers.replicaSetLister) @! "ReplicaSets" #namespace)%E.
  wp_method_call. rewrite /trusted_app_listers.replicaSetLister__ReplicaSetsⁱᵐᵖˡ. wp_call. wp_auto.
  wp_method_call. rewrite /trusted_generic_listers.ResourceIndexer__Getⁱᵐᵖˡ decide_True; try reflexivity.
  rewrite /trusted_generic_listers.resourceIndexerGet. wp_pures.
  wp_auto.
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
  rewrite decide_True; try reflexivity.
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
  { destruct Hget_Hvalid' as (_ & _ & Hvalid_meta & _). exact Hvalid_meta. }
  pose proof Hget_Hmeta_eq as Hget_Hmeta_fields.
  rewrite /ObjectMetaV.equiv_except_resource_version
    /ObjectMetaV.without_resource_version in Hget_Hmeta_fields.
  pose proof (f_equal ObjectMetaV.Name' Hget_Hmeta_fields) as Hget_Hname_eq.
  pose proof (f_equal ObjectMetaV.UID' Hget_Hmeta_fields) as Hget_Huid_eq.
  pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hget_Hmeta_fields)
    as Hget_Hdeletion_timestamp_eq.
  simpl in Hget_Hname_eq, Hget_Huid_eq, Hget_Hdeletion_timestamp_eq.
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as (_ & Hrs_kind_valid & _).
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  assert (valid_namespace rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace'))
    as Hrs_namespace_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_name ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name'))
    as Hrs_name_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_uid rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID'))
    as Hrs_uid_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
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
  { symmetry. exact Hget_Huid_eq. }
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
    rewrite Hget_Hdeletion_timestamp_eq.
    exact Hdeletion_timestamp_eq. }
  assert (rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None)
    as Hdeletion_timestamp_eq_get.
  { rewrite Hget_Hdeletion_timestamp_eq.
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
  { rewrite Hget_Hname_eq.
    exact Hrs_name_short. }
  assert (valid_finalizers
      rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    as Hrs_get_template_finalizers_valid.
  { rewrite <-Hget_Hspec_eq. exact Hrs_template_finalizers_valid. }
  assert (NoDup (PodV.key <$>
      (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods))) as Hpartition_nodup.
  { rewrite pod_key_filter_partition_perm. exact Hall_nodup. }
  wp_apply (wp_manageReplicas γ l ctx kube_client burst active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) (filter (λ pod, not (is_pod_alive pod)) all_pods)
    rs_get n terminating_children.No dq' 1 with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs $Hactive_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done.
    all: try (intros pod Hpod; apply list_elem_of_filter in Hpod as [Halive _]; exact Halive).
    all: try lia. }
  iIntros (pods_managed) "(%Hmanaged_len & %Hmanaged_alive & Hhas_terminating_children &
    Hmanaged_meta_frags & #Hmanaged_unreserved_key_frags &
    Hown_children_frag)".
  iDestruct "Hhas_terminating_children" as (has_terminating_children') "Hown_terminating_children_frag".
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
  iAssert (∃ has_terminating_children, own_terminating_children_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') has_terminating_children)%I
    with "[Hown_terminating_children_frag]" as "Hown_terminating_children_frag".
  { iExists has_terminating_children'. iFrame. }
  rewrite return_val_unseal /return_val_def. wp_auto.
  iApply ("HΦ" $! (pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods)).
  rewrite /owned_resources /=.
  iFrame "Hown_rs_meta_frag Hown_rs_spec_frag Hpod_meta_frags_post
    Hpod_unreserved_key_frags_post Hown_children_frag Hown_terminating_children_frag".
  iPureIntro. split; first exact Hpods'_nodup.
  (* replica arithmetic of this sync: the live count moved toward the desired
     count by [min distance burst], so either it now matches or the distance
     strictly decreased and the pod set changed *)
  assert (length (filter is_pod_alive pods) = length (filter is_pod_alive all_pods)) as Hpods_active_len.
  { symmetry. apply active_pod_count_erased_meta_perm. exact Hall_meta_perm. }
  assert (length (filter is_pod_alive (pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods)) =
      length pods_managed) as Hfinal_active_len.
  { rewrite list.filter_app (filter_all is_pod_alive pods_managed Hmanaged_alive).
    assert (filter is_pod_alive (filter (λ pod, not (is_pod_alive pod)) all_pods) = []) as Hfilter_inactive.
    { apply filter_none. intros pod Hpod.
      apply list_elem_of_filter in Hpod as [Hnot_alive _].
      exact Hnot_alive. }
    rewrite Hfilter_inactive app_nil_r. done. }
  pose proof (capped_replica_count_distance (length (filter is_pod_alive all_pods)) (sint.nat n) (sint.nat burst))
    as Hcap.
  rewrite -Hmanaged_len in Hcap.
  assert (0 < sint.nat burst)%nat as Hburst_pos by word.
  destruct (decide (length pods_managed = sint.nat n)) as [Hmatch|Hnomatch].
  - left.
    unfold current_state_matches. rewrite Hreplicas_eq Hfinal_active_len. exact Hmatch.
  - right. split.
    + (* the set of pod keys changed: the two key lists have no duplicates and different lengths *)
      left. intros Hkeys_eq.
      apply (f_equal size) in Hkeys_eq.
      rewrite (size_list_to_set _ Hpods_nodup) (size_list_to_set _ Hpods'_nodup) in Hkeys_eq.
      rewrite !length_fmap length_app in Hkeys_eq.
      pose proof (Permutation_length Hall_key_perm) as Hlen_perm.
      rewrite !length_fmap in Hlen_perm.
      pose proof (Permutation_length (filter_partition_perm is_pod_alive all_pods)) as Hpartition_len.
      rewrite length_app in Hpartition_len.
      unfold replica_distance in Hcap. lia.
    + rewrite !(match_distance_replica_distance _ _ n Hreplicas_eq).
      rewrite Hfinal_active_len Hpods_active_len.
      unfold replica_distance in Hcap |- *. lia.
Qed.

End proof.
