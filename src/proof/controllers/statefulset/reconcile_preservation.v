From New.proof.controllers.statefulset Require Export reconcile_progress.
From New.proof.controllers.statefulset Require Import create_pod create_pvc
  update_pod condemned delete_pod common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
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

Definition pod_key_not_reserved (reserved : list PodV.t) (pod : PodV.t) : Prop :=
  PodV.key pod ∉ PodV.key <$> reserved.

Definition unreserved_pods (reserved pods : list PodV.t) : list PodV.t :=
  filter (pod_key_not_reserved reserved) pods.

Definition own_unreserved_pods γ (reserved pods : list PodV.t) : iProp Σ :=
  ([∗ list] pod ∈ unreserved_pods reserved pods,
    own_meta_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
      pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
      (ObjectSpecV.PodSpec pod.(PodV.Spec')) ∗
    own_occupied_reserved_frag γ 1 (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))%I.

Lemma unreserved_pods_nil pods :
  unreserved_pods [] pods = pods.
Proof.
  unfold unreserved_pods. apply filter_all.
  intros pod _. unfold pod_key_not_reserved. intros Hin. inversion Hin.
Qed.

Lemma pending_pod_not_reserved reserved pod :
  Forall (λ reserved_pod, ¬ is_pod_alive reserved_pod) reserved →
  NoDup (PodV.key <$> (pod :: reserved)) →
  is_pod_alive pod →
  pod_key_not_reserved reserved pod.
Proof.
  intros Hreserved Hnodup Halive Hin.
  apply list_elem_of_fmap_1 in Hin as (reserved_pod & Hkey & Hin).
  rewrite Forall_forall in Hreserved.
  pose proof (Hreserved reserved_pod ltac:(by rewrite -list_elem_of_In))
    as Hnot_alive.
  inversion Hnodup as [|? ? Hnotin _].
  apply Hnotin. rewrite Hkey. by apply list_elem_of_fmap_2.
Qed.

Lemma filter_replace_reserved reserved before pod pod' after :
  pod_key_not_reserved reserved pod →
  PodV.key pod' = PodV.key pod →
  filter (pod_key_not_reserved reserved) (before ++ pod' :: after) =
    filter (pod_key_not_reserved reserved) before ++
      pod' :: filter (pod_key_not_reserved reserved) after.
Proof.
  intros Hpod Hkey.
  assert (pod_key_not_reserved reserved pod') as Hpod'.
  { unfold pod_key_not_reserved in *. by rewrite Hkey. }
  rewrite list.filter_app. f_equal.
  exact (filter_cons_True _ pod' after Hpod').
Qed.

Lemma filter_remove_reserved reserved before pod after :
  pod_key_not_reserved reserved pod →
  filter (pod_key_not_reserved reserved) (before ++ pod :: after) =
    filter (pod_key_not_reserved reserved) before ++
      pod :: filter (pod_key_not_reserved reserved) after.
Proof.
  intros Hpod. rewrite list.filter_app. f_equal.
  exact (filter_cons_True _ pod after Hpod).
Qed.

Lemma reserved_subset_replace reserved before pod pod' after :
  reserved ⊆ before ++ pod :: after →
  pod_key_not_reserved reserved pod →
  reserved ⊆ before ++ pod' :: after.
Proof.
  intros Hsubset Hnotin.
  unfold pod_key_not_reserved in Hnotin.
  Timeout 10 set_solver.
Qed.

Lemma reserved_subset_remove reserved before pod after :
  reserved ⊆ before ++ pod :: after →
  pod_key_not_reserved reserved pod →
  reserved ⊆ before ++ after.
Proof.
  intros Hsubset Hnotin.
  unfold pod_key_not_reserved in Hnotin.
  Timeout 10 set_solver.
Qed.

Lemma own_pvc_map_subset γ (small large :
    gmap KKey.t PersistentVolumeClaimV.t) :
  small ⊆ large →
  own_pvc_map γ large -∗ own_pvc_map γ small.
Proof.
  intros Hsubset. rewrite /own_pvc_map.
  by iApply big_sepM_subseteq.
Qed.

Lemma wp_reconcileDesiredPods_preservation γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods reserved : list PodV.t)
    (pvcs : list PersistentVolumeClaimV.t) dq_set dq_pods :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_occupied_reserved_frag γ 1 (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods)) ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set pvcs,
        own_available_reserved_frag γ 1 key) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hreserved_eq" ∷
        ⌜ reserved = filter (pending_pod set) pods ⌝ ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement set ⌝
  }}}
    @! statefulset.reconcileDesiredPods #set_l #pods_sl
  {{{ (continue : bool) (pods' : list PodV.t)
      (pvc_map' : gmap KKey.t PersistentVolumeClaimV.t),
      RET (#continue, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods' ∗
      "Hown_pvcs" ∷ own_pvc_map γ pvc_map' ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods')) ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods'),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set (pvc_list_of_map pvc_map'),
        own_available_reserved_frag γ 1 key) ∗
      "%Hpvc_wf" ∷ ⌜ ∀ key claim,
        pvc_map' !! key = Some claim →
        PersistentVolumeClaimV.key claim = key ⌝ ∗
      "%Hdistance" ∷ ⌜
        match_distance set pods' (pvc_list_of_map pvc_map') ≤
          match_distance set pods pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      "%Hreserved_subset" ∷ ⌜ reserved ⊆ pods' ⌝ ∗
      ( (⌜ continue = true ⌝ ∗
          ⌜ local_pods_match_stored pods pods' ⌝ ∗
          ⌜ desired_objects_reconciled set pods'
              (pvc_list_of_map pvc_map') ⌝)
        ∨ ⌜ continue = false ⌝)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hset_valid as
    (Hset_typemeta_valid & Hset_rv_valid & Hset_meta_valid &
      Hset_spec_valid & Hset_status_valid).
  pose proof (statefulset_replicas_le_go_int32_max set)
    as Hreplicas_bound.
  assert (Forall (λ pod,
      pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods)
    as Hpod_name_members.
  { eapply Forall_impl; last exact Hpods_members.
    intros pod Hmember. exact (proj2 Hmember). }
  assert (∀ pod, pod ∈ pods →
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
    as Hpod_name_len.
  { intros pod Hpod. rewrite Forall_forall in Hpods_valid.
    apply pod_name_length_le_go_int_max_of_valid.
    apply Hpods_valid. by rewrite -list_elem_of_In. }
  iEval (rewrite big_sepL_sep) in "Hown_pvcs".
  iDestruct "Hown_pvcs" as "[Hown_pvc_meta Hoccupied_pvcs]".
  iPoseProof (kview.own_meta_list_no_dup
    PersistentVolumeClaimV.key PersistentVolumeClaimV.ObjectMeta'
    with "Hown_pvc_meta") as "%Hpvc_keys_nodup".
  iCombine "Hown_pvc_meta Hoccupied_pvcs" as "Hown_pvcs".
  iEval (rewrite -big_sepL_sep) in "Hown_pvcs".
  set initial_pvc_map := pvc_map_of_list pvcs.
  iEval (rewrite (own_pvc_list_as_map γ pvcs Hpvc_keys_nodup))
    in "Hown_pvcs".
  assert (∀ key claim, initial_pvc_map !! key = Some claim →
      PersistentVolumeClaimV.key claim = key) as Hinitial_pvc_wf.
  { exact (pvc_map_of_list_wf pvcs). }
  set required_pvcs :=
    list_to_set (C:=gset KKey.t) (desired_pvc_keys set).
  assert (NoDup (missing_pvc_keys set pvcs))
    as Hinitial_reserved_pvcs_nodup.
  { unfold missing_pvc_keys. apply list.NoDup_filter.
    unfold desired_pvc_keys. apply NoDup_elements. }
  assert (∀ key, key ∈ required_pvcs →
      key ∈ dom initial_pvc_map ∨
      key ∈ missing_pvc_keys set pvcs) as Hinitial_pvc_coverage.
  { intros key Hrequired.
    destruct (decide
      (key ∈ PersistentVolumeClaimV.key <$> pvcs)) as [Hin|Hnotin].
    - left. rewrite /initial_pvc_map pvc_map_of_list_dom
        elem_of_list_to_set. exact Hin.
    - right. unfold missing_pvc_keys.
      apply list_elem_of_filter. split; first exact Hnotin.
      unfold required_pvcs in Hrequired.
      by rewrite elem_of_list_to_set in Hrequired. }
  wp_apply (wp_endOrdinalOf set_l set dq_set with "[$Hset //]").
  iIntros (end_ordinal) "[%Hend_ordinal Hset]". wp_auto.
  set I := (∃ (ordinal : w64) (current_pods : list PodV.t)
      (pvc_map : gmap KKey.t PersistentVolumeClaimV.t)
      (reserved_pvcs : list KKey.t),
    "Hordinal_ptr" ∷ ordinal_ptr ↦ ordinal ∗
    "Hend_ptr" ∷ end_ptr ↦ end_ordinal ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hpods_ptr" ∷ pods_ptr ↦ pods_sl ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_pods" ∷ own_unreserved_pods γ reserved current_pods ∗
    "Hown_pvcs" ∷ own_pvc_map γ pvc_map ∗
    "Hown_children" ∷ own_children_frag γ
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> unreserved_pods reserved current_pods)) ∗
    "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved current_pods),
      own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
    "Hreserved_pvcs" ∷ ([∗ list] key ∈ reserved_pvcs,
      own_available_reserved_frag γ 1 key) ∗
    "%Hordinal_range" ∷ ⌜ 0 ≤ sint.Z ordinal ∧
      sint.Z ordinal ≤ Z.of_nat (statefulset_replicas set) ⌝ ∗
    "%Hpvc_wf" ∷ ⌜ ∀ key claim, pvc_map !! key = Some claim →
      PersistentVolumeClaimV.key claim = key ⌝ ∗
    "%Hreserved_pvcs_nodup" ∷ ⌜ NoDup reserved_pvcs ⌝ ∗
    "%Hpvc_coverage" ∷ ⌜ ∀ key, key ∈ required_pvcs →
      key ∈ dom pvc_map ∨ key ∈ reserved_pvcs ⌝ ∗
    "%Hlocal_stored" ∷ ⌜ local_pods_match_stored pods current_pods ⌝ ∗
    "%Hunprocessed" ∷ ⌜ unprocessed_pods_unchanged set
      (sint.nat ordinal) pods current_pods ⌝ ∗
    "%Hprefix" ∷ ⌜ desired_prefix_reconciled set
      (sint.nat ordinal) current_pods pvc_map ⌝ ∗
    "%Hcurrent_valid" ∷ ⌜ Forall PodV.valid current_pods ⌝ ∗
    "%Hcurrent_members" ∷ ⌜ Forall
      (pod_has_int32_member_key set) current_pods ⌝ ∗
    "%Hcurrent_nodup" ∷ ⌜ NoDup (PodV.key <$> current_pods) ⌝ ∗
    "%Hreserved_subset" ∷ ⌜ reserved ⊆ current_pods ⌝ ∗
    "%Hdistance" ∷ ⌜ match_distance set current_pods
      (pvc_list_of_map pvc_map) ≤
      match_distance set pods pvcs ⌝)%I.
  iAssert I with "[Hset Hpods_sl Hpods Hown_pods Hown_pvcs
      Hown_children Hreserved_pods Hreserved_pvcs ordinal end set pods]"
    as "Hloop".
  { iExists (W64 0), pods, initial_pvc_map,
      (missing_pvc_keys set pvcs).
    iFrame. iPureIntro. split_and!.
    - word.
    - word.
    - exact Hinitial_pvc_wf.
    - exact Hinitial_reserved_pvcs_nodup.
    - exact Hinitial_pvc_coverage.
    - apply local_pods_match_stored_refl.
    - apply unprocessed_pods_unchanged_refl.
    - apply desired_prefix_reconciled_zero.
    - exact Hpods_valid.
    - exact Hpods_members.
    - exact Hpods_nodup.
    - intros pod Hpod.
      rewrite Hreserved_eq in Hpod.
      apply list_elem_of_filter in Hpod as [_ Hpod]. exact Hpod.
    - assert (PersistentVolumeClaimV.key <$>
          pvc_list_of_map initial_pvc_map ≡ₚ
        PersistentVolumeClaimV.key <$> pvcs) as Hkeys_perm.
      { rewrite (pvc_list_of_map_keys _ Hinitial_pvc_wf).
        unfold initial_pvc_map, pvc_map_of_list.
        assert (NoDup
            (((λ pvc, (PersistentVolumeClaimV.key pvc, pvc)) <$> pvcs).*1))
          as Hpair_keys_nodup.
        { rewrite -list_fmap_compose. exact Hpvc_keys_nodup. }
        pose proof (Permutation_map fst
          (map_to_list_to_map
            ((λ pvc, (PersistentVolumeClaimV.key pvc, pvc)) <$> pvcs)
            Hpair_keys_nodup)) as Hkeys_perm'.
        assert (∀ xs : list PersistentVolumeClaimV.t,
            map fst
              ((λ pvc, (PersistentVolumeClaimV.key pvc, pvc)) <$> xs) =
            PersistentVolumeClaimV.key <$> xs) as Hmap_keys.
        { intros xs. induction xs as [|p ps IH].
          - done.
          - simpl. f_equal. exact IH. }
        rewrite Hmap_keys in Hkeys_perm'. exact Hkeys_perm'. }
      unfold match_distance, pvc_distance, missing_pvc_keys.
      assert (∀ key,
          key ∉ PersistentVolumeClaimV.key <$>
              pvc_list_of_map initial_pvc_map ↔
          key ∉ PersistentVolumeClaimV.key <$> pvcs) as Hfilter_iff.
      { intros key. split; intros Hnot Hin; apply Hnot.
        - rewrite list_elem_of_In.
          eapply Permutation_in; first exact (Permutation_sym Hkeys_perm).
          by rewrite -list_elem_of_In.
        - rewrite list_elem_of_In.
          eapply Permutation_in; first exact Hkeys_perm.
          by rewrite -list_elem_of_In. }
      rewrite (list_filter_iff
        (λ key,
          key ∉ PersistentVolumeClaimV.key <$>
            pvc_list_of_map initial_pvc_map)
        (λ key, key ∉ PersistentVolumeClaimV.key <$> pvcs)
        (desired_pvc_keys set) Hfilter_iff).
      done. }
  wp_for "Hloop". wp_if_destruct.
  - match goal with
    | H : (sint.Z ordinal ≤ sint.Z end_ordinal)%Z |- _ =>
        rename H into Hordinal_end
    end.
    assert (0 ≤ sint.Z ordinal) as Hordinal_nonnegative.
    { exact (proj1 Hordinal_range). }
    assert ((sint.nat ordinal < statefulset_replicas set)%nat)
      as Hordinal_lt.
    { eapply reconcile_loop_ordinal_lt; done. }
    assert ((sint.nat ordinal ≤ go_int32_max_nat)%nat)
      as Hordinal_int32.
    { eapply reconcile_loop_ordinal_int32; done. }
    wp_apply (wp_findPodByOrdinal set_l pods_sl set ptrs pods ordinal
      dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
    { iPureIntro. split_and!; done. }
    iIntros (pod_l) "(Hset & Hpods_sl & Hpods & %Hfind)".
    destruct (find_pod_by_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (sint.nat ordinal) pods) as [[pod_idx local_pod]|]
      eqn:Hfind_pod.
    + simpl in Hfind.
      apply list_find_Some in Hfind_pod as
        (Hlocal_lookup & Hlocal_name & _).
      pose proof (local_pods_match_stored_lookup
        pods current_pods pod_idx local_pod Hlocal_stored Hlocal_lookup)
        as (stored_pod & Hstored_lookup & Hlocal_stored_pod).
      assert (pod_has_int32_member_key set local_pod) as Hlocal_member.
      { rewrite Forall_forall in Hpods_members. apply Hpods_members.
        apply list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      assert (PodV.key local_pod =
          desired_pod_key set (sint.nat ordinal)) as Hlocal_key.
      { apply pod_int32_member_key.
        - exact (proj1 Hlocal_member).
        - exact Hlocal_name. }
      assert (stored_pod = local_pod) as ->.
      { eapply unprocessed_pods_unchanged_lookup
          with (ordinal := sint.nat ordinal);
          [exact Hunprocessed|exact Hlocal_lookup|exact Hstored_lookup|
           exact (Nat.le_refl _)|].
        exact Hlocal_key. }
      iDestruct (big_sepL2_lookup_acc with "Hpods") as
        "[Hlocal_pod Hlocal_pod_restore]";
        [exact Hfind|exact Hlocal_lookup|].
      iPoseProof (PodV.deepown_l_split with "Hlocal_pod") as
        "(%Hpod_l_not_null & Hlocal_typemeta & Hlocal_meta &
          Hlocal_spec & Hlocal_status)".
      iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
        with "[$Hlocal_typemeta $Hlocal_meta $Hlocal_spec $Hlocal_status]")
        as "Hlocal_pod".
      wp_auto. wp_if_destruct; first contradiction.
      wp_apply (wp_isTerminating pod_l local_pod dq_pods
        with "Hlocal_pod").
      iIntros (terminating) "[%Hterminating Hlocal_pod]".
      destruct terminating.
      { iSpecialize ("Hlocal_pod_restore" with "Hlocal_pod").
        iPoseProof (own_reserved_pvcs_finish γ set pvc_map reserved_pvcs
          Hpvc_wf Hreserved_pvcs_nodup Hpvc_coverage with "Hreserved_pvcs") as "Hreserved_pvcs".
        wp_auto. iApply wp_for_post_return. wp_auto.
        iApply ("HΦ" $! false current_pods pvc_map).
        iFrame. iPureIntro. split_and!; try done.
        right. done. }
      assert (is_pod_alive local_pod) as Hlocal_alive.
      { apply Classical_Prop.NNPP. intros Hnot_alive.
        pose proof (proj2 Hterminating Hnot_alive) as Hfalse. done. }
      assert (pod_key_not_reserved (filter (pending_pod set) pods) local_pod)
        as Hlocal_unreserved.
      { intros Hreserved_key.
        apply list_elem_of_fmap_1 in Hreserved_key as
          (pending & Hpending_key & Hpending_in).
        assert (pending ∈ pods) as Hpending_pods.
        { apply list_elem_of_filter in Hpending_in as [_ Hpending].
          exact Hpending. }
        assert (local_pod = pending) as ->.
        { eapply NoDup_fmap_inj_on; try exact Hpods_nodup.
          - apply list_elem_of_lookup_2 in Hlocal_lookup. exact Hlocal_lookup.
          - exact Hpending_pods.
          - exact Hpending_key. }
        apply list_elem_of_filter in Hpending_in as [Hpending _].
        exact (proj1 Hpending Hlocal_alive). }
      wp_auto.
      destruct Hinput_requirement as
        (Hgenerated_names & Htemplate_finalizers & Hclaim_valid).
      assert (∀ name claim_template,
          persistent_volume_claim_templates_by_name
            (StatefulSetSpecV.volume_claim_templates_list
              set.(StatefulSetV.Spec')) !! name =
              Some claim_template →
          PersistentVolumeClaimV.valid_named_create
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (new_persistent_volume_claim set claim_template
              (sint.nat ordinal))) as Hclaim_valid_lookup.
      { intros name claim_template Hlookup.
        pose proof (persistent_volume_claim_template_lookup_elem
          _ _ _ Hlookup) as [Hclaim_template _].
        rewrite Forall_forall in Hclaim_valid.
        apply (Hclaim_valid claim_template
          ltac:(by rewrite -list_elem_of_In) (sint.nat ordinal)).
        exact Hordinal_lt. }
      iDestruct (prepare_pvc_states γ set (sint.nat ordinal)
        (persistent_volume_claim_templates_by_name
          (StatefulSetSpecV.volume_claim_templates_list
            set.(StatefulSetV.Spec')))
        pvc_map reserved_pvcs required_pvcs Hpvc_wf
        Hreserved_pvcs_nodup Hpvc_coverage
        ltac:(intros name claim_template Hlookup;
          unfold required_pvcs; rewrite elem_of_list_to_set;
          by eapply desired_pvc_key_of_template_is_desired)
        ltac:(intros; by eapply desired_pvc_key_name_inj)
        Hclaim_valid_lookup with "Hown_pvcs Hreserved_pvcs")
        as "[Hpvc_states Hpvc_finish]".
      wp_apply (wp_createPersistentVolumeClaims γ model_l set_l pod_l
        set local_pod (sint.nat ordinal) dq_set dq_pods
        with "[$Hset $Hlocal_pod $Hpvc_states]").
      { iFrame "#". iPureIntro.
        destruct Hset_meta_valid as
          (_ & _ & _ & Hnamespace_nonempty & Hnamespace_valid & _).
        split_and!; try done.
        apply pod_name_length_le_go_int_max_of_valid.
        rewrite Forall_forall in Hpods_valid. apply Hpods_valid.
        apply list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      iIntros "(Hset & Hlocal_pod & Hpvc_states)".
      iEval (rewrite /pvc_done) in "Hpvc_states".
      iEval (rewrite persistent_volume_claim_templates_by_name_dom
        /pvc_claim_template_names) in "Hpvc_finish".
      iDestruct ("Hpvc_finish" with "Hpvc_states") as
        (pvc_map' reserved_pvcs')
        "(Hown_pvcs & Hreserved_pvcs & %Hpvc_result)".
      destruct Hpvc_result as
        (Hpvc_wf' & Hreserved_pvcs_nodup' & Hpvc_coverage' &
          Hpvc_dom_mono & Hordinal_pvcs).
      set current_before := take pod_idx current_pods.
      set current_after := drop (S pod_idx) current_pods.
      assert (current_pods = current_before ++ local_pod :: current_after)
        as Hcurrent_decomp.
      { unfold current_before, current_after. symmetry.
        by apply take_drop_middle. }
      iEval (rewrite /own_unreserved_pods /unreserved_pods Hcurrent_decomp
        (filter_remove_reserved _ _ _ _ Hlocal_unreserved)
        !big_sepL_sep !big_sepL_app !big_sepL_cons) in "Hown_pods".
      iDestruct "Hown_pods" as
        "[[Hmeta_before [Hlocal_meta Hmeta_after]]
          [[Hspec_before [Hlocal_spec Hspec_after]]
           [Hoccupied_before [Hlocal_occupied Hoccupied_after]]]]".
      wp_auto.
      wp_apply (wp_updateStatefulPod γ model_l set_l pod_l set local_pod
        (sint.nat ordinal) dq_set dq_pods
        with "[$Hset $Hlocal_pod $Hlocal_meta $Hlocal_spec]").
      { iFrame "#". iPureIntro. split_and!.
        - rewrite Forall_forall in Hpods_valid. apply Hpods_valid.
          apply list_elem_of_In.
          by apply list_elem_of_lookup_2 in Hlocal_lookup.
        - exact Hlocal_key.
        - rewrite Hlocal_name. apply Hgenerated_names. exact Hordinal_lt.
        - exact Hordinal_int32.
        - unfold is_pod_alive in Hlocal_alive. exact Hlocal_alive. }
      iIntros (stored_pod') "Hupdate".
      iNamedPrefix "Hupdate" "Hupdate_".
      iAssert (⌜ pod_identity_matches set stored_pod' ∧
          local_pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') =
            stored_pod'.(PodV.ObjectMeta').(
              ObjectMetaV.DeletionTimestamp') ⌝)%I
        with "[Hupdate]" as "%Hstored_common".
      { iDestruct "Hupdate" as "[Hnoop|Hchanged]".
        - iNamed "Hnoop". destruct Hnoop as [Hidentity ->]. done.
        - iNamed "Hchanged". iPureIntro. split.
          + apply (pod_identity_matches_meta_updated set
              (update_identity set local_pod (sint.nat ordinal))
              stored_pod').
            * apply update_identity_identity_matches. exact Hordinal_int32.
            * rewrite Hupdate_Hpod_key.
              unfold update_identity, PodV.key, PodV.meta_key. simpl.
              apply (f_equal KKey.Name') in Hlocal_key
                as Hlocal_name_key.
              apply (f_equal KKey.Namespace') in Hlocal_key
                as Hlocal_namespace_key.
              simpl in Hlocal_name_key, Hlocal_namespace_key.
              rewrite Hlocal_name_key Hlocal_namespace_key. done.
            * exact Hmeta_updated.
          + destruct Hmeta_updated as
              (_ & _ & _ & _ & _ & _ & Hdeletion & _).
            simpl in Hdeletion. unfold update_identity in Hdeletion.
            simpl in Hdeletion. symmetry. exact Hdeletion. }
      destruct Hstored_common as [Hstored_identity Hstored_deletion].
      assert (local_pod_matches_stored local_pod stored_pod')
        as Hlocal_stored_pod'.
      { split_and!.
        - symmetry. exact Hupdate_Hpod_key.
        - symmetry. exact Hupdate_Hpod_uid.
        - exact Hstored_deletion.
        - symmetry. exact Hupdate_Hpod_spec. }
      iSpecialize ("Hlocal_pod_restore" with "Hupdate_Hpod").
      iRename "Hlocal_pod_restore" into "Hpods".
      iAssert (own_unreserved_pods γ (filter (pending_pod set) pods)
          (current_before ++ stored_pod' :: current_after))%I
        with "[Hmeta_before Hupdate_Hown_meta Hmeta_after
          Hspec_before Hupdate_Hown_spec Hspec_after
          Hoccupied_before Hlocal_occupied Hoccupied_after]" as "Hown_pods".
      { rewrite /own_unreserved_pods /unreserved_pods
          (filter_replace_reserved _ _ _ _ _ Hlocal_unreserved
            Hupdate_Hpod_key)
          !big_sepL_sep !big_sepL_app !big_sepL_cons.
        rewrite Hupdate_Hpod_key Hupdate_Hpod_uid. iFrame. }
      iAssert (own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (list_to_set (PodV.key <$> unreserved_pods
            (filter (pending_pod set) pods)
            (current_before ++ stored_pod' :: current_after))))
        with "[Hown_children]" as "Hown_children".
      { unfold unreserved_pods.
        rewrite (filter_replace_reserved _ _ _ _ _ Hlocal_unreserved
          Hupdate_Hpod_key).
        iEval (rewrite /unreserved_pods Hcurrent_decomp
          (filter_remove_reserved _ _ _ _ Hlocal_unreserved))
          in "Hown_children".
        rewrite !fmap_app /= Hupdate_Hpod_key.
        iExact "Hown_children". }
      set current_pods' :=
        current_before ++ stored_pod' :: current_after.
      assert (current_pods' = <[pod_idx:=stored_pod']> current_pods)
        as Hcurrent_insert.
      { unfold current_pods', current_before, current_after.
        symmetry. apply insert_take_drop.
        by eapply lookup_lt_Some. }
      pose proof (reconcile_loop_ordinal_next ordinal
        (statefulset_replicas set) Hordinal_nonnegative Hordinal_lt
        Hreplicas_bound)
        as (Hnext_nonnegative & Hnext_upper & Hnext_nat).
      assert (PodV.key <$> (<[pod_idx:=stored_pod']> current_pods) =
          PodV.key <$> current_pods) as Hcurrent_keys.
      { rewrite list_fmap_insert Hupdate_Hpod_key.
        apply list_insert_id.
        by rewrite list_lookup_fmap Hstored_lookup. }
      assert (local_pods_match_stored pods current_pods')
        as Hlocal_stored'.
      { rewrite Hcurrent_insert.
        eapply local_pods_match_stored_insert; done. }
      assert (unprocessed_pods_unchanged set
          (S (sint.nat ordinal)) pods current_pods')
        as Hunprocessed'.
      { rewrite Hcurrent_insert.
        eapply unprocessed_pods_unchanged_insert; done. }
      assert (desired_prefix_reconciled set
          (S (sint.nat ordinal)) current_pods' pvc_map')
        as Hprefix'.
      { rewrite Hcurrent_insert.
        eapply desired_prefix_reconciled_step;
          [exact Hprefix|exact Hstored_lookup|exact Hcurrent_nodup|
           exact Hlocal_key|exact Hupdate_Hpod_key| |exact Hstored_identity|
           exact Hpvc_dom_mono|].
        - unfold is_pod_alive in *. by rewrite -Hstored_deletion.
        - intros name Hname. apply Hordinal_pvcs.
          rewrite -persistent_volume_claim_templates_by_name_dom.
          exact Hname. }
      assert (Forall PodV.valid current_pods') as Hcurrent_valid'.
      { rewrite Hcurrent_insert. apply Forall_insert; done. }
      assert (Forall (pod_has_int32_member_key set) current_pods')
        as Hcurrent_members'.
      { rewrite Hcurrent_insert. apply Forall_insert; first done.
        eapply pod_has_int32_member_key_of_key_eq;
          [symmetry; exact Hupdate_Hpod_key|exact Hlocal_member]. }
      assert (NoDup (PodV.key <$> current_pods')) as Hcurrent_nodup'.
      { rewrite Hcurrent_insert Hcurrent_keys. exact Hcurrent_nodup. }
      assert (PodV.key <$> unreserved_pods (filter (pending_pod set) pods) current_pods =
          PodV.key <$> unreserved_pods (filter (pending_pod set) pods) current_pods') as Hunreserved_keys.
      { unfold unreserved_pods, current_pods'. rewrite Hcurrent_decomp
          (filter_remove_reserved _ _ _ _ Hlocal_unreserved)
          (filter_replace_reserved _ _ _ _ _ Hlocal_unreserved Hupdate_Hpod_key).
        rewrite !fmap_app /= Hupdate_Hpod_key. done. }
      assert (missing_pod_keys set (unreserved_pods (filter (pending_pod set) pods) current_pods) =
          missing_pod_keys set (unreserved_pods (filter (pending_pod set) pods) current_pods')) as Hmissing.
      { by apply missing_pod_key_fmap_eq. }
      iEval (rewrite Hmissing) in "Hreserved_pods".
      assert (filter (pending_pod set) pods ⊆ current_pods')
        as Hreserved_subset'.
      { unfold current_pods'.
        eapply (reserved_subset_replace _ _ local_pod stored_pod' _).
        - rewrite -Hcurrent_decomp. exact Hreserved_subset.
        - exact Hlocal_unreserved. }
      assert (match_distance set current_pods'
          (pvc_list_of_map pvc_map') ≤
        match_distance set current_pods (pvc_list_of_map pvc_map))
        as Hdistance_step.
      { rewrite Hcurrent_insert.
        eapply match_distance_reconcile_desired_step;
          [exact Hstored_lookup|exact Hcurrent_members|exact Hlocal_key|
           exact Hupdate_Hpod_key|exact Hstored_deletion|
           exact Hupdate_Hpod_spec|exact Hstored_identity|exact Hpvc_wf|
           exact Hpvc_wf'|exact Hpvc_dom_mono]. }
      wp_auto. iApply wp_for_post_do. wp_auto. iFrame "HΦ".
      iExists (word.add ordinal (W64 1)), current_pods', pvc_map',
        reserved_pvcs'.
      iFrame. rewrite Hnext_nat. iPureIntro. split_and!.
      * exact Hnext_nonnegative.
      * exact Hnext_upper.
      * exact Hpvc_wf'.
      * exact Hreserved_pvcs_nodup'.
      * exact Hpvc_coverage'.
      * exact Hlocal_stored'.
      * exact Hunprocessed'.
      * exact Hprefix'.
      * exact Hcurrent_valid'.
      * exact Hcurrent_members'.
      * exact Hcurrent_nodup'.
      * exact Hreserved_subset'.
      * etrans; [exact Hdistance_step|exact Hdistance].
    + simpl in Hfind. subst pod_l.
      pose proof Hinput_requirement as Hinput_requirement'.
      destruct Hinput_requirement as
        (Hgenerated_names & Htemplate_finalizers & Hclaim_valid).
      assert (StatefulSetV.valid set) as Hset_valid'.
      { split_and!; done. }
      pose proof (Hgenerated_names (sint.nat ordinal) Hordinal_lt)
        as Hgenerated_name_valid.
      wp_auto.
      wp_apply (wp_newStatefulSetPod set_l set ordinal dq_set
        with "[$Hset]").
      { iFrame "#". iPureIntro. split_and!.
        - exact Hset_meta_valid.
        - exact Hordinal_nonnegative.
        - exact Hordinal_int32.
        - by apply valid_dns1123_label_length_le_go_int_max. }
      iIntros (new_pod_l controller_ref claim_template_names)
        "(Hset & Hnew_pod & %Hcontroller_ref &
          %Hcontroller_ref_valid & %Hclaim_template_names)".
      set new_pod := new_statefulset_pod set (sint.nat ordinal)
        controller_ref claim_template_names.
      assert (new_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal) ∧
        PodV.valid_named_create
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') new_pod ∧
        obj_parent_ref_is (KObjectV.Pod new_pod) StatefulSetV.kind
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ∧
        pod_match set new_pod) as Hnew_pod_requirements.
      { apply new_statefulset_pod_requirements; done. }
      destruct Hnew_pod_requirements as
        (Hnew_pod_name & Hnew_pod_valid_create & Hnew_pod_parent &
          Hnew_pod_match).
      pose proof (find_pod_none_desired_key_missing set
        (sint.nat ordinal) pods Hordinal_lt Hfind_pod) as Hmissing_pod.
      apply list_elem_of_filter in Hmissing_pod as
        (Hmissing_pod_notin & Hmissing_pod_desired).
      assert (desired_pod_key set (sint.nat ordinal) ∈
          missing_pod_keys set pods) as Hmissing_pod.
      { unfold missing_pod_keys. apply list_elem_of_filter. done. }
      assert (desired_pod_key set (sint.nat ordinal) ∈
          missing_pod_keys set
            (unreserved_pods (filter (pending_pod set) pods) current_pods)) as Hmissing_current.
      { unfold missing_pod_keys. apply list_elem_of_filter. split; last exact Hmissing_pod_desired.
        intros Hin. apply Hmissing_pod_notin.
        rewrite (local_pods_match_stored_keys pods current_pods Hlocal_stored).
        apply list_elem_of_fmap_1 in Hin as (stored & Hkey & Hin).
        rewrite Hkey. apply list_elem_of_fmap_2.
        unfold unreserved_pods in Hin. by apply list_elem_of_filter in Hin as [_ Hin]. }
      assert (desired_pod_key set (sint.nat ordinal) ∈
          list_to_set (C:=gset KKey.t)
            (missing_pod_keys set
              (unreserved_pods (filter (pending_pod set) pods) current_pods))) as Hmissing_current_set.
      { by rewrite elem_of_list_to_set. }
      assert (NoDup (missing_pod_keys set
          (unreserved_pods (filter (pending_pod set) pods) current_pods))) as Hmissing_current_nodup.
      { unfold missing_pod_keys. apply list.NoDup_filter. apply desired_pod_keys_nodup. }
      iEval (rewrite -(big_sepS_list_to_set _ _ Hmissing_current_nodup)) in "Hreserved_pods".
      iEval (rewrite (big_sepS_delete _ _ _ Hmissing_current_set)) in "Hreserved_pods".
      iDestruct "Hreserved_pods" as "[Hpod_reserved Hreserved_pods]".
      assert (∀ name claim_template,
          persistent_volume_claim_templates_by_name
            (StatefulSetSpecV.volume_claim_templates_list
              set.(StatefulSetV.Spec')) !! name =
              Some claim_template →
          PersistentVolumeClaimV.valid_named_create
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (new_persistent_volume_claim set claim_template
              (sint.nat ordinal))) as Hclaim_valid_lookup.
      { intros name claim_template Hlookup.
        pose proof (persistent_volume_claim_template_lookup_elem
          _ _ _ Hlookup) as [Hclaim_template _].
        rewrite Forall_forall in Hclaim_valid.
        apply (Hclaim_valid claim_template
          ltac:(by rewrite -list_elem_of_In) (sint.nat ordinal)).
        exact Hordinal_lt. }
      iDestruct (prepare_pvc_states γ set (sint.nat ordinal)
        (persistent_volume_claim_templates_by_name
          (StatefulSetSpecV.volume_claim_templates_list
            set.(StatefulSetV.Spec')))
        pvc_map reserved_pvcs required_pvcs Hpvc_wf
        Hreserved_pvcs_nodup Hpvc_coverage
        ltac:(intros name claim_template Hlookup;
          unfold required_pvcs; rewrite elem_of_list_to_set;
          by eapply desired_pvc_key_of_template_is_desired)
        ltac:(intros; by eapply desired_pvc_key_name_inj)
        Hclaim_valid_lookup with "Hown_pvcs Hreserved_pvcs")
        as "[Hpvc_states Hpvc_finish]".
      wp_auto.
      wp_apply (wp_createStatefulPod_preservation γ model_l set_l new_pod_l
        set new_pod (sint.nat ordinal)
        (list_to_set (PodV.key <$> unreserved_pods
          (filter (pending_pod set) pods) current_pods)) dq_set
        with "[$Hset $Hnew_pod $Hpod_reserved $Hown_children
          $Hpvc_states]").
      { iFrame "#". iPureIntro.
        pose proof Hset_meta_valid as
          (_ & _ & _ & Hnamespace_nonempty & Hnamespace_valid & _).
        split_and!; done. }
      iIntros "(Hset & Hpvc_states & Hcreate)".
      iEval (rewrite /pvc_done) in "Hpvc_states".
      iEval (rewrite persistent_volume_claim_templates_by_name_dom
        /pvc_claim_template_names) in "Hpvc_finish".
      iDestruct ("Hpvc_finish" with "Hpvc_states") as
        (pvc_map' reserved_pvcs')
        "(Hown_pvcs & Hreserved_pvcs & %Hpvc_result)".
      destruct Hpvc_result as
        (Hpvc_wf' & Hreserved_pvcs_nodup' & Hpvc_coverage' &
          Hpvc_dom_mono & Hordinal_pvcs).
      iDestruct "Hcreate" as "[Hcreated|Hdeleting]".
      2: {
        iDestruct "Hdeleting" as (old_uid) "[Hpod_reserved Hown_children]".
        iAssert (([∗ list] key ∈
              missing_pod_keys set (unreserved_pods (filter (pending_pod set) pods) current_pods),
            own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid)%I)
          with "[Hpod_reserved Hreserved_pods]" as "Hreserved_pods".
        { rewrite -(big_sepS_list_to_set _ _ Hmissing_current_nodup)
            (big_sepS_delete _ _ _ Hmissing_current_set).
          iSplitL "Hpod_reserved".
          - iRight. iExists old_uid. iFrame.
          - iFrame. }
        iPoseProof (own_reserved_pvcs_finish γ set pvc_map' reserved_pvcs'
          Hpvc_wf' Hreserved_pvcs_nodup' Hpvc_coverage' with "Hreserved_pvcs") as "Hreserved_pvcs".
        assert (match_distance set current_pods (pvc_list_of_map pvc_map') ≤
            match_distance set current_pods (pvc_list_of_map pvc_map)) as Hpvc_distance.
        { unfold match_distance.
          pose proof (pvc_distance_map_mono set pvc_map pvc_map' Hpvc_wf Hpvc_wf' Hpvc_dom_mono).
          lia. }
        wp_auto. iApply wp_for_post_return. wp_auto.
        iApply ("HΦ" $! false current_pods pvc_map').
        iFrame "Hset Hpods_sl Hpods Hown_pods Hown_pvcs Hown_children
          Hreserved_pods Hreserved_pvcs".
        iPureIntro. split_and!; try done.
        - etrans; [exact Hpvc_distance|exact Hdistance].
        - by right.
      }
      iDestruct "Hcreated" as (stored_pod' uid) "Hcreate".
      iNamedPrefix "Hcreate" "Hcreate_".
      pose proof (created_statefulset_pod_properties set
        (sint.nat ordinal) new_pod stored_pod'
        Hnew_pod_match Hnew_pod_name Hcreate_Hpod_meta_created
        Hcreate_Hpod_spec_created) as
        (Hstored_pod_key & Hstored_pod_alive & Hstored_pod_member &
          Hstored_pod_match).
      assert (pod_key_not_reserved (filter (pending_pod set) pods)
          stored_pod')
        as Hstored_unreserved.
      { unfold pod_key_not_reserved. intros Hreserved_key.
        apply list_elem_of_fmap_1 in Hreserved_key as
          (pending & Hpending_key & Hpending_in).
        apply list_elem_of_filter in Hpending_in as [_ Hpending_in].
        apply Hmissing_pod_notin. rewrite -Hstored_pod_key Hpending_key.
        by apply list_elem_of_fmap_2. }
      set current_pods' := current_pods ++ [stored_pod'].
      iAssert (own_unreserved_pods γ (filter (pending_pod set) pods)
          current_pods')
        with "[Hown_pods Hcreate_Hpod_meta Hcreate_Hpod_spec
          Hcreate_Hpod_reserved]"
        as "Hown_pods".
      { unfold own_unreserved_pods, unreserved_pods, current_pods'.
        rewrite list.filter_app
          (filter_cons_True _ stored_pod' [] Hstored_unreserved) /=.
        rewrite big_sepL_app big_sepL_singleton.
        rewrite -Hcreate_Hpod_key -Hcreate_Huid. iFrame. }
      iAssert (own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (list_to_set (PodV.key <$> unreserved_pods
            (filter (pending_pod set) pods) current_pods')))
        with "[Hcreate_Hown_children]" as "Hown_children".
      { unfold current_pods'.
        unfold unreserved_pods.
        rewrite list.filter_app
          (filter_cons_True _ stored_pod' [] Hstored_unreserved) /=.
        rewrite fmap_app /= list_to_set_app_L list_to_set_singleton_L.
        rewrite Hcreate_Hpod_key. iExact "Hcreate_Hown_children". }
      assert (PodV.key stored_pod' ∈
          missing_pod_keys set current_pods) as Hstored_missing_current.
      { unfold missing_pod_keys. apply list_elem_of_filter. split.
        - rewrite -(local_pods_match_stored_keys pods current_pods
            Hlocal_stored) Hstored_pod_key.
          exact Hmissing_pod_notin.
        - rewrite Hstored_pod_key.
          apply desired_pod_key_elem_iff. exact Hordinal_lt. }
      assert (match_distance set current_pods'
          (pvc_list_of_map pvc_map') <
        match_distance set current_pods (pvc_list_of_map pvc_map))
        as Hdistance_step.
      { unfold current_pods'.
        exact (proj2 (reconcile_desired_create_progress set pods
          current_pods stored_pod' (sint.nat ordinal) pvc_map pvc_map'
          Hlocal_stored Hordinal_lt Hmissing_pod_notin Hstored_pod_key
          Hstored_pod_alive Hstored_pod_member Hstored_pod_match Hpvc_wf
          Hpvc_wf' Hpvc_dom_mono)). }
      assert (Forall (pod_has_int32_member_key set) current_pods')
        as Hcurrent_members'.
      { unfold current_pods'. apply Forall_app. split;
          first exact Hcurrent_members.
        constructor; done. }
      assert (NoDup (PodV.key <$> current_pods')) as Hcurrent_nodup'.
      { unfold current_pods'. rewrite fmap_app /=.
        apply list.NoDup_app. split_and!; try done.
        - intros key Hkey_current Hkey_new.
          rewrite list_elem_of_singleton in Hkey_new. subst key.
          unfold missing_pod_keys in Hstored_missing_current.
          apply list_elem_of_filter in Hstored_missing_current as [Hfresh _].
          exact (Hfresh Hkey_current).
        - apply NoDup_singleton. }
      iAssert (([∗ list] key ∈
            missing_pod_keys set (unreserved_pods (filter (pending_pod set) pods) current_pods'),
          own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid)%I)
        with "[Hreserved_pods]" as "Hreserved_pods".
      { rewrite /current_pods'.
        assert (unreserved_pods (filter (pending_pod set) pods) (current_pods ++ [stored_pod']) =
            unreserved_pods (filter (pending_pod set) pods) current_pods ++ [stored_pod'])
          as Hunreserved_snoc.
        { unfold unreserved_pods. rewrite list.filter_app.
          assert (pod_key_not_reserved (filter (pending_pod set) pods) stored_pod')
            as Hstored_unreserved'.
          { exact Hstored_unreserved. }
          by rewrite (filter_cons_True _ stored_pod' [] Hstored_unreserved'). }
        assert (PodV.key stored_pod' ∉
            PodV.key <$> unreserved_pods (filter (pending_pod set) pods) current_pods) as Hfresh.
        { unfold missing_pod_keys in Hstored_missing_current.
          apply list_elem_of_filter in Hstored_missing_current as [Hfresh _].
          intros Hin. apply Hfresh.
          unfold unreserved_pods in Hin. apply list_elem_of_fmap_1 in Hin as
            (pod0 & Hkey & Hin).
          rewrite Hkey. apply list_elem_of_fmap_2.
          by apply list_elem_of_filter in Hin as [_ Hin]. }
        assert (list_to_set (C:=gset KKey.t)
            (missing_pod_keys set
              (unreserved_pods (filter (pending_pod set) pods) current_pods ++ [stored_pod'])) =
            list_to_set (missing_pod_keys set
              (unreserved_pods (filter (pending_pod set) pods) current_pods)) ∖
              {[PodV.key stored_pod']}) as Hmissing_snoc.
        { apply missing_pod_key_set_snoc.
          - by rewrite Hstored_pod_key.
          - exact Hfresh. }
        assert (NoDup (missing_pod_keys set
            (unreserved_pods (filter (pending_pod set) pods) current_pods ++ [stored_pod'])))
          as Hmissing_snoc_nodup.
        { unfold missing_pod_keys. apply list.NoDup_filter. apply desired_pod_keys_nodup. }
        rewrite Hunreserved_snoc -(big_sepS_list_to_set _ _ Hmissing_snoc_nodup)
          Hmissing_snoc Hstored_pod_key.
        iExact "Hreserved_pods". }
      assert (filter (pending_pod set) pods ⊆ current_pods')
        as Hreserved_subset'.
      { unfold current_pods'. intros pod Hpod. apply elem_of_app. left.
        by apply Hreserved_subset. }
      iPoseProof (own_reserved_pvcs_finish γ set pvc_map' reserved_pvcs'
        Hpvc_wf' Hreserved_pvcs_nodup' Hpvc_coverage' with "Hreserved_pvcs") as "Hreserved_pvcs".
      wp_auto. iApply wp_for_post_return. wp_auto.
      iApply ("HΦ" $! false current_pods' pvc_map').
      iFrame. iPureIntro. split_and!.
      * exact Hpvc_wf'.
      * etrans; [apply Z.lt_le_incl; exact Hdistance_step|exact Hdistance].
      * exact Hcurrent_members'.
      * exact Hcurrent_nodup'.
      * exact Hreserved_subset'.
      * right. done.
  - match goal with
    | H : ¬ (sint.Z ordinal ≤ sint.Z end_ordinal)%Z |- _ =>
        rename H into Hordinal_after_end
    end.
    assert (sint.nat ordinal = statefulset_replicas set)
      as Hordinal_complete.
    { eapply reconcile_loop_exit_ordinal;
        [exact (proj1 Hordinal_range)|exact (proj2 Hordinal_range)|
         exact Hend_ordinal|exact Hordinal_after_end]. }
    assert (desired_objects_reconciled set current_pods
        (pvc_list_of_map pvc_map)) as Hdesired_reconciled.
    { apply desired_prefix_reconciled_complete;
      [by rewrite -Hordinal_complete|exact Hcurrent_members|
         exact Hcurrent_nodup|exact Hpvc_wf]. }
    iPoseProof (own_reserved_pvcs_finish γ set pvc_map reserved_pvcs
      Hpvc_wf Hreserved_pvcs_nodup Hpvc_coverage with "Hreserved_pvcs") as "Hreserved_pvcs".
    iApply ("HΦ" $! true current_pods pvc_map).
    iFrame. iPureIntro. split_and!; try done.
    left. split_and!; done.
Qed.

Lemma wp_reconcileCondemnedPod_preservation γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (local_pods pods reserved : list PodV.t)
    (pvcs initial_pvcs : list PersistentVolumeClaimV.t) dq_set dq_pods phase :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;local_pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods)) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hlocal_pods_valid" ∷ ⌜ Forall PodV.valid local_pods ⌝ ∗
      "%Hlocal_pods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) local_pods ⌝ ∗
      "%Hlocal_pods_nodup" ∷
        ⌜ NoDup (PodV.key <$> local_pods) ⌝ ∗
      "%Hlocal_stored" ∷
        ⌜ local_pods_match_stored local_pods pods ⌝ ∗
      "%Hreserved_eq" ∷
        ⌜ reserved = filter (pending_pod set) local_pods ⌝ ∗
      "%Hreserved_nonempty" ∷ ⌜ reserved ≠ [] ⌝ ∗
      "%Hreserved_subset" ∷ ⌜ reserved ⊆ pods ⌝ ∗
      "%Hdistance" ∷ ⌜ match_distance set pods pvcs ≤
        match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hdesired_reconciled" ∷
        ⌜ desired_objects_reconciled set pods pvcs ⌝
  }}}
    @! statefulset.reconcileCondemnedPod #set_l #pods_sl
  {{{ (pods' : list PodV.t) phase', RET (#false, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;local_pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods' ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods')) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase' ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods'),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "%Hdistance" ∷ ⌜ match_distance set pods' pvcs ≤
        match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      "%Hreserved_subset" ∷ ⌜ reserved ⊆ pods' ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hset_valid as
    (_ & _ & _ & Hset_spec_valid & _).
  assert (Forall (λ pod,
      pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) local_pods)
    as Hlocal_name_members.
  { eapply Forall_impl; last exact Hlocal_pods_members.
    intros pod Hmember. exact (proj2 Hmember). }
  assert (∀ pod, pod ∈ local_pods →
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
    as Hlocal_name_len.
  { rewrite Forall_forall in Hlocal_pods_valid.
    intros pod Hpod. apply pod_name_length_le_go_int_max_of_valid.
    apply Hlocal_pods_valid. by rewrite -list_elem_of_In. }
  assert (Forall (pod_has_int32_member_key set) pods)
    as Hstored_members.
  { eapply local_pods_match_stored_members; done. }
  assert (NoDup (PodV.key <$> pods)) as Hstored_nodup.
  { rewrite -(local_pods_match_stored_keys _ _ Hlocal_stored).
    exact Hlocal_pods_nodup. }
  wp_apply (wp_firstCondemnedPod set_l pods_sl set ptrs local_pods
    dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
  { iPureIntro. split_and!; done. }
  iIntros (condemned_l)
    "(Hset & Hpods_sl & Hpods & %Hcondemned)".
  destruct Hcondemned as
    [[-> Hnone_local]|(idx & local_pod & Hptr_lookup & Hlocal_lookup &
      Hlocal_condemned)].
  - exfalso.
    destruct reserved as [|pending reserved_tail]; first contradiction.
    assert (pending ∈ filter (pending_pod set) local_pods)
      as Hpending_filter.
    { rewrite -Hreserved_eq. by left. }
    apply list_elem_of_filter in Hpending_filter as
      [Hpending Hpending_local].
    destruct Hpending as [Hpending_not_alive _].
    assert (pending ∈ pods) as Hpending_stored.
    { apply Hreserved_subset. by left. }
    assert (pod_has_int32_member_key set pending) as Hpending_member.
    { rewrite Forall_forall in Hlocal_pods_members.
      apply Hlocal_pods_members. by rewrite -list_elem_of_In. }
    assert (¬ pod_key_is_desired set (PodV.key pending))
      as Hpending_not_desired.
    { intros Hdesired.
      destruct Hdesired_reconciled as (_ & _ & Halive).
      rewrite Forall_forall in Halive.
      exact (Hpending_not_alive (proj1 (Halive pending
        ltac:(by rewrite -list_elem_of_In) Hdesired))). }
    assert (pod_is_condemned set pending) as Hpending_condemned.
    { apply (proj2
        (pod_int32_member_condemned_iff set pending Hpending_member)).
      exact Hpending_not_desired. }
    rewrite Forall_forall in Hnone_local.
    exact (Hnone_local pending ltac:(by rewrite -list_elem_of_In)
      Hpending_condemned).
  - pose proof (local_pods_match_stored_lookup
      local_pods pods idx local_pod Hlocal_stored Hlocal_lookup)
      as (stored_pod & Hstored_lookup & Hlocal_stored_pod).
    pose proof Hlocal_stored_pod as
      (Hlocal_key & Hlocal_uid & Hlocal_deletion & Hlocal_spec).
    assert (pod_is_condemned set stored_pod) as Hstored_condemned.
    { apply (proj1
        (local_pod_matches_stored_condemned set _ _
          Hlocal_stored_pod)). exact Hlocal_condemned. }
    assert (pod_has_int32_member_key set stored_pod) as Hstored_member.
    { rewrite Forall_forall in Hstored_members. apply Hstored_members.
      apply list_elem_of_In.
      by apply list_elem_of_lookup_2 in Hstored_lookup. }
    assert (¬ pod_key_is_desired set (PodV.key stored_pod)) as Hstored_not_desired.
    { apply (proj1 (pod_int32_member_condemned_iff set stored_pod Hstored_member)).
      exact Hstored_condemned. }
    iDestruct (big_sepL2_lookup_acc with "Hpods") as
      "[Hlocal_pod Hlocal_pod_restore]";
      [exact Hptr_lookup|exact Hlocal_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hlocal_pod") as
      "(%Hcondemned_not_null & Hlocal_typemeta & Hlocal_meta &
        Hlocal_spec & Hlocal_status)".
    iPoseProof (PodV.deepown_l_restore _ _ _ Hcondemned_not_null
      with "[$Hlocal_typemeta $Hlocal_meta $Hlocal_spec $Hlocal_status]")
      as "Hlocal_pod".
    wp_auto. wp_if_destruct; first contradiction.
    wp_apply (wp_isTerminating condemned_l local_pod dq_pods
      with "Hlocal_pod").
    iIntros (terminating) "[%Hterminating Hlocal_pod]".
    destruct terminating.
    { iSpecialize ("Hlocal_pod_restore" with "Hlocal_pod").
      wp_auto. iApply ("HΦ" $! pods phase). iFrame.
      iPureIntro. split_and!; done. }
    assert (is_pod_alive local_pod) as Hlocal_pod_alive.
    { apply Classical_Prop.NNPP. intros Hnot_alive.
      pose proof (proj2 Hterminating Hnot_alive) as Hfalse. done. }
    assert (is_pod_alive stored_pod) as Hstored_pod_alive.
    { apply (proj1
        (local_pod_matches_stored_alive _ _ Hlocal_stored_pod)).
      exact Hlocal_pod_alive. }
    assert (pod_key_not_reserved
        (filter (pending_pod set) local_pods) stored_pod)
      as Hstored_unreserved.
    { intros Hkey_reserved.
      apply list_elem_of_fmap_1 in Hkey_reserved as
        (pending & Hpending_key & Hpending_reserved).
      assert (pending ∈ pods) as Hpending_stored.
      { by apply Hreserved_subset. }
      assert (stored_pod = pending) as ->.
      { eapply NoDup_fmap_inj_on; try exact Hstored_nodup.
        - apply list_elem_of_lookup_2 in Hstored_lookup. exact Hstored_lookup.
        - exact Hpending_stored.
        - exact Hpending_key. }
      assert (pending ∈ filter (pending_pod set) local_pods)
        as Hpending_filter by exact Hpending_reserved.
      apply list_elem_of_filter in Hpending_filter as [Hpending _].
      destruct Hpending as [Hnot_alive _].
      exact (Hnot_alive Hstored_pod_alive). }
    wp_auto.
    set before := take idx pods.
    set after := drop (S idx) pods.
    assert (pods = before ++ stored_pod :: after) as Hpods_decomp.
    { unfold before, after. symmetry. by apply take_drop_middle. }
    iEval (rewrite /own_unreserved_pods /unreserved_pods Hpods_decomp
      (filter_remove_reserved (filter (pending_pod set) local_pods)
        before stored_pod after
        Hstored_unreserved) big_sepL_app big_sepL_cons) in "Hown_pods".
    iDestruct "Hown_pods" as
      "[Hown_before [Hstored_own Hown_after]]".
    iDestruct "Hstored_own" as
      "(Hstored_meta & Hstored_spec & Hstored_occupied)".
    assert (PodV.key stored_pod ∈
        list_to_set (C:=gset KKey.t) (PodV.key <$> unreserved_pods
          (filter (pending_pod set) local_pods) pods)) as Hkey_in.
    { apply elem_of_list_to_set. apply list_elem_of_fmap_2.
      unfold unreserved_pods. apply list_elem_of_filter. split;
        [exact Hstored_unreserved|].
      by apply list_elem_of_lookup_2 in Hstored_lookup. }
    wp_apply (wp_deletePod γ model_l condemned_l
      local_pod stored_pod (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
      (list_to_set (PodV.key <$> unreserved_pods
      (filter (pending_pod set) local_pods) pods)) phase dq_pods
      with "[$Hlocal_pod $Hstored_meta $Hstored_spec $Hstored_occupied
        $Hown_children $Hown_terminating_children_frag]").
    { iFrame "#". iPureIntro. split_and!; done. }
    iIntros "Hdelete". iNamedPrefix "Hdelete" "Hdelete_".
    iSpecialize ("Hlocal_pod_restore" with "Hdelete_Hpod").
    iRename "Hlocal_pod_restore" into "Hpods".
    iAssert (own_unreserved_pods γ
        (filter (pending_pod set) local_pods) (before ++ after))
      with "[Hown_before Hown_after]" as "Hown_pods".
    { unfold own_unreserved_pods, unreserved_pods.
      rewrite list.filter_app big_sepL_app.
      iFrame. }
    iAssert (([∗ list] key ∈
          missing_pod_keys set (unreserved_pods (filter (pending_pod set) local_pods) (before ++ after)),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid)%I)
      with "[Hreserved_pods]" as "Hreserved_pods".
    { set P := pod_key_not_reserved (filter (pending_pod set) local_pods).
      iEval (rewrite /unreserved_pods Hpods_decomp
        (filter_remove_reserved _ before stored_pod after Hstored_unreserved)) in "Hreserved_pods".
      rewrite /unreserved_pods list.filter_app.
      assert (missing_pod_keys set (filter P before ++ filter P after) =
          missing_pod_keys set (filter P before ++ stored_pod :: filter P after)) as Hmissing.
      { unfold missing_pod_keys. rewrite !fmap_app /=.
        apply filter_not_elem_add_irrelevant. exact Hstored_not_desired. }
      rewrite Hmissing. iExact "Hreserved_pods". }
    assert (NoDup (PodV.key <$> (before ++ stored_pod :: after)))
      as Hdecomp_nodup.
    { rewrite -Hpods_decomp. exact Hstored_nodup. }
    iAssert (own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods
          (filter (pending_pod set) local_pods) (before ++ after))))
      with "[Hdelete_Hown_children]" as "Hown_children".
    { set P := pod_key_not_reserved
        (filter (pending_pod set) local_pods).
      assert (NoDup (PodV.key <$> (filter P before ++
          stored_pod :: filter P after))) as Hfiltered_nodup.
      { assert (NoDup (PodV.key <$> filter P pods)) as Hfiltered.
        { apply NoDup_fmap_filter. exact Hstored_nodup. }
        rewrite Hpods_decomp
          (filter_remove_reserved _ before stored_pod after
            Hstored_unreserved) in Hfiltered.
        exact Hfiltered. }
      iEval (rewrite /unreserved_pods Hpods_decomp
        (filter_remove_reserved _ _ _ _ Hstored_unreserved))
        in "Hdelete_Hown_children".
      unfold unreserved_pods. rewrite list.filter_app.
      rewrite (list_to_set_pod_keys_remove
        (filter P before) stored_pod (filter P after) Hfiltered_nodup).
      iExact "Hdelete_Hown_children". }
    assert (match_distance set (before ++ after) pvcs <
        match_distance set pods pvcs) as Hdistance'.
    { rewrite Hpods_decomp. eapply match_distance_remove_condemned;
        [rewrite -Hpods_decomp; exact Hstored_members|
         exact Hstored_condemned|exact Hstored_pod_alive]. }
    assert (Forall (pod_has_int32_member_key set) (before ++ after))
      as Hmembers'.
    { apply (pod_members_remove set before stored_pod after).
      rewrite -Hpods_decomp. exact Hstored_members. }
    assert (NoDup (PodV.key <$> (before ++ after))) as Hnodup'.
    { rewrite !fmap_app /= in Hdecomp_nodup |- *.
      apply list.NoDup_app in Hdecomp_nodup as
        (Hbefore_nodup & Hbefore_disjoint & Htail_nodup).
      apply list.NoDup_cons in Htail_nodup as [_ Hafter_nodup].
      apply list.NoDup_app. split_and!; try done.
      intros key Hbefore Hafter.
      apply (Hbefore_disjoint key Hbefore). by right. }
    assert (filter (pending_pod set) local_pods ⊆ before ++ after)
      as Hreserved_subset'.
    { eapply (reserved_subset_remove _ _ stored_pod _).
      - rewrite -Hpods_decomp. exact Hreserved_subset.
      - exact Hstored_unreserved. }
    wp_auto. iApply ("HΦ" $! (before ++ after) Mutable).
    iFrame. iPureIntro. split_and!; try done. lia.
Qed.

Lemma wp_reconcileReplicas_preservation γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods reserved : list PodV.t)
    (pvcs : list PersistentVolumeClaimV.t) dq_set dq_pods phase :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_occupied_reserved_frag γ 1 (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods)) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set pvcs,
        own_available_reserved_frag γ 1 key) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hreserved_eq" ∷
        ⌜ reserved = filter (pending_pod set) pods ⌝ ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement set ⌝
  }}}
    @! statefulset.reconcileReplicas #set_l #pods_sl
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t) phase',
      RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ own_unreserved_pods γ reserved pods' ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_occupied_reserved_frag γ 1 (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> unreserved_pods reserved pods')) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase' ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set (unreserved_pods reserved pods'),
        own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set pvcs',
        own_available_reserved_frag γ 1 key) ∗
      "%Hdistance" ∷ ⌜ match_distance set pods' pvcs' ≤
        match_distance set pods pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      "%Hreserved_subset" ∷ ⌜ reserved ⊆ pods' ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_reconcileDesiredPods_preservation γ model_l set_l pods_sl
    set ptrs pods reserved pvcs dq_set dq_pods with
    "[$Hset $Hpods_sl $Hpods $Hown_pods $Hown_pvcs $Hown_children
      $Hreserved_pods $Hreserved_pvcs]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (continue_desired pods1 pvc_map1)
    "(Hset & Hpods_sl & Hpods & Hown_pods & Hown_pvcs &
      Hown_children & Hreserved_pods & Hreserved_pvcs & %Hpvc_wf1 & %Hdistance1 &
      %Hmembers1 & %Hnodup1 & %Hreserved_subset1 & Hdesired_result)".
  iDestruct "Hdesired_result" as "[Hdesired_continue|Hdesired_stop]".
  - iDestruct "Hdesired_continue" as
      "(%Hcontinue_desired & %Hlocal_stored & %Hdesired_reconciled)".
    subst continue_desired. wp_auto.
    destruct reserved as [|pending reserved_tail].
    + assert (filter (pending_pod set) pods = []) as Hpending_empty.
      { by rewrite -Hreserved_eq. }
      iEval (rewrite /own_unreserved_pods unreserved_pods_nil !big_sepL_sep)
        in "Hown_pods".
      iDestruct "Hown_pods" as "(Hown_meta & Hown_spec & Hoccupied_pods)".
      iCombine "Hown_meta Hown_spec" as "Hown_pods".
      iEval (rewrite -big_sepL_sep) in "Hown_pods".
      iEval (rewrite unreserved_pods_nil) in "Hown_children".
      iEval (rewrite (own_pvc_map_as_list γ pvc_map1 Hpvc_wf1) big_sepL_sep)
        in "Hown_pvcs".
      iDestruct "Hown_pvcs" as "[Hown_pvcs Hoccupied_pvcs]".
      wp_apply (wp_reconcileCondemnedPod γ model_l set_l pods_sl set ptrs
        pods pods1 (pvc_list_of_map pvc_map1) pvcs dq_set dq_pods phase with
        "[$Hset $Hpods_sl $Hpods $Hown_pods $Hown_pvcs $Hown_children
          $Hoccupied_pods $Hown_terminating_children_frag]").
      { iFrame "#". iPureIntro. split_and!; done. }
      iIntros (continue_condemned pods2 deletion2)
        "(Hset & Hpods_sl & Hpods & Hown_pods & Hoccupied_pods & Hown_pvcs &
          Hown_children & Hstarted_deletion & Hown_terminating_children_frag &
          %Hdeletion_retiring & %Hdistance2 & %Hmembers2 & %Hnodup2 &
          %Hdesired_reconciled2 & Hcondemned_result)".
      iDestruct "Hcondemned_result" as "[Hcondemned_continue|Hcondemned_stop]".
      * iDestruct "Hcondemned_continue" as
          "(%Hcontinue_condemned & %Hdeletion2 & %Hpods2 & %Hno_condemned)".
        subst continue_condemned. subst deletion2. subst pods2. wp_auto.
        iClear "Hstarted_deletion".
        wp_apply (wp_reconcileOutdatedPod γ model_l set_l pods_sl set ptrs
          pods pods1 (pvc_list_of_map pvc_map1) pvcs dq_set dq_pods phase with
          "[$Hset $Hpods_sl $Hpods $Hown_pods $Hoccupied_pods $Hown_pvcs
            $Hown_children $Hown_terminating_children_frag]").
        { iFrame "#". iPureIntro. split_and!; done. }
        iIntros (pods3 deletion3)
          "(Hset & Hpods_sl & Hpods & Hown_pods & Hoccupied_pods & Hown_pvcs &
            Hown_children & Hstarted_deletion & Hown_terminating_children_frag &
            %Hdeletion_desired & %Hdistance3 & %Hmembers3 & %Hnodup3 &
            %Hmissing_pods3 & %Hprogress3)".
        iClear "Hreserved_pods".
        iAssert (([∗ list] key ∈ missing_pod_keys set pods3,
            own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid)%I)
          with "[Hstarted_deletion]" as "Hreserved_pods".
        { assert (NoDup (missing_pod_keys set pods3)) as Hmissing_pods3_nodup.
          { unfold missing_pod_keys. apply list.NoDup_filter. apply desired_pod_keys_nodup. }
          rewrite -(big_sepS_list_to_set _ _ Hmissing_pods3_nodup) Hmissing_pods3.
          destruct deletion3 as [[key uid]|]; simpl.
          - rewrite big_sepS_singleton /own_started_deletion /=.
            iRight. by iExists uid.
          - rewrite big_sepS_empty /own_started_deletion. done. }
        iAssert (own_unreserved_pods γ [] pods3)
          with "[Hown_pods Hoccupied_pods]" as "Hown_pods".
        { rewrite /own_unreserved_pods unreserved_pods_nil !big_sepL_sep.
          iFrame. }
        iAssert (own_children_frag γ (StatefulSetV.key set)
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (list_to_set (PodV.key <$> unreserved_pods [] pods3)))
          with "[Hown_children]" as "Hown_children".
        { rewrite unreserved_pods_nil. iFrame. }
        iCombine "Hown_pvcs Hoccupied_pvcs" as "Hown_pvcs".
        iEval (rewrite -big_sepL_sep) in "Hown_pvcs".
        wp_auto. iApply ("HΦ" $! pods3 (pvc_list_of_map pvc_map1)
          (phase_after_deletion phase deletion3)).
        rewrite unreserved_pods_nil. iFrame.
        iPureIntro. split_and!; try done. Timeout 10 set_solver.
      * iDestruct "Hcondemned_stop" as
          "(%Hcontinue_condemned & %Hdeletion2_some & %Hprogress2)".
        subst continue_condemned. wp_auto. iClear "Hstarted_deletion".
        iAssert (([∗ list] key ∈ missing_pod_keys set pods2,
            own_available_reserved_frag γ 1 key ∨ ∃ uid, own_deleting_reserved_frag γ 1 key uid)%I)
          with "[Hreserved_pods]" as "Hreserved_pods".
        { destruct Hdesired_reconciled as (Hmissing1 & _ & _).
          destruct Hdesired_reconciled2 as (Hmissing2 & _ & _).
          iEval (rewrite unreserved_pods_nil Hmissing1) in "Hreserved_pods".
          rewrite Hmissing2. iFrame. }
        iAssert (own_unreserved_pods γ [] pods2)
          with "[Hown_pods Hoccupied_pods]" as "Hown_pods".
        { rewrite /own_unreserved_pods unreserved_pods_nil !big_sepL_sep.
          iFrame. }
        iAssert (own_children_frag γ (StatefulSetV.key set)
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (list_to_set (PodV.key <$> unreserved_pods [] pods2)))
          with "[Hown_children]" as "Hown_children".
        { rewrite unreserved_pods_nil. iFrame. }
        iCombine "Hown_pvcs Hoccupied_pvcs" as "Hown_pvcs".
        iEval (rewrite -big_sepL_sep) in "Hown_pvcs".
        iApply ("HΦ" $! pods2 (pvc_list_of_map pvc_map1)
          (phase_after_deletion phase deletion2)).
        rewrite unreserved_pods_nil. iFrame.
        iPureIntro. split_and!; try done. Timeout 10 set_solver.
    + wp_apply (wp_reconcileCondemnedPod_preservation γ model_l set_l
        pods_sl set ptrs pods pods1 (pending :: reserved_tail)
        (pvc_list_of_map pvc_map1) pvcs dq_set dq_pods phase with
        "[$Hset $Hpods_sl $Hpods $Hown_pods $Hown_children $Hreserved_pods
          $Hown_terminating_children_frag]").
      { iFrame "#". iPureIntro. split_and!; done. }
      iIntros (pods2 phase2)
        "(Hset & Hpods_sl & Hpods & Hown_pods & Hown_children & Hreserved_pods &
          Hown_terminating_children_frag &
          %Hdistance2 & %Hmembers2 & %Hnodup2 & %Hreserved_subset2)".
      wp_auto.
      iEval (rewrite (own_pvc_map_as_list γ pvc_map1 Hpvc_wf1))
        in "Hown_pvcs".
      iApply ("HΦ" $! pods2 (pvc_list_of_map pvc_map1) phase2).
      iFrame. iPureIntro. split_and!; done.
  - iDestruct "Hdesired_stop" as "%Hcontinue_desired".
    subst continue_desired. wp_auto.
    iEval (rewrite (own_pvc_map_as_list γ pvc_map1 Hpvc_wf1))
      in "Hown_pvcs".
    iApply ("HΦ" $! pods1 (pvc_list_of_map pvc_map1) phase).
    iFrame. iPureIntro. split_and!; done.
Qed.

End proof.
