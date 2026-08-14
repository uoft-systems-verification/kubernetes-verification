From New.proof.controllers.statefulset Require Export distance.
From New.proof.controllers.statefulset Require Import pod create_pod create_pvc
  update_pod condemned outdated delete_pod.

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

Lemma statefulset_storage_view_input_requirement sts1 sts2 :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  (input_requirement sts1 ↔ input_requirement sts2).
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Definition pvc_map_of_list (pvcs : list PersistentVolumeClaimV.t) :
    gmap KKey.t PersistentVolumeClaimV.t :=
  list_to_map ((λ pvc, (PersistentVolumeClaimV.key pvc, pvc)) <$> pvcs).

Definition pvc_list_of_map
    (pvc_map : gmap KKey.t PersistentVolumeClaimV.t) :
    list PersistentVolumeClaimV.t :=
  snd <$> map_to_list pvc_map.

Lemma pvc_map_of_list_wf pvcs :
  ∀ key claim, pvc_map_of_list pvcs !! key = Some claim →
    PersistentVolumeClaimV.key claim = key.
Proof.
  intros key claim Hlookup.
  apply elem_of_list_to_map_2 in Hlookup.
  apply list_elem_of_fmap_1 in Hlookup as (pvc & Heq & _).
  inversion Heq. done.
Qed.

Lemma pvc_map_of_list_dom pvcs :
  dom (pvc_map_of_list pvcs) =
    list_to_set (PersistentVolumeClaimV.key <$> pvcs).
Proof.
  unfold pvc_map_of_list. rewrite dom_list_to_map_L.
  f_equal. rewrite -list_fmap_compose. done.
Qed.

Lemma pvc_list_of_map_keys pvc_map :
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map =
    (map_to_list pvc_map).*1.
Proof.
  intros Hwf. unfold pvc_list_of_map.
  rewrite -list_fmap_compose.
  apply list_fmap_ext. intros idx [key claim] Hlookup. simpl.
  apply Hwf. apply elem_of_map_to_list.
  by apply list_elem_of_lookup_2 in Hlookup.
Qed.

Lemma pvc_list_of_map_keys_nodup pvc_map :
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  NoDup (PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map).
Proof.
  intros Hwf. rewrite (pvc_list_of_map_keys pvc_map Hwf).
  apply NoDup_fst_map_to_list.
Qed.

Lemma pvc_list_of_map_key_set pvc_map :
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  list_to_set (C:=gset KKey.t)
      (PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map) =
    dom pvc_map.
Proof.
  intros Hwf. apply set_eq. intros key.
  rewrite elem_of_list_to_set elem_of_dom.
  rewrite (pvc_list_of_map_keys pvc_map Hwf).
  split.
  - intros Hkey. apply list_elem_of_fmap_1 in Hkey as
      ([key' claim] & Hkey & Hpair). simpl in Hkey. subst key'.
    exists claim. by apply elem_of_map_to_list.
  - intros (claim & Hlookup).
    apply (list_elem_of_fmap_2 fst (map_to_list pvc_map) (key, claim)).
    by apply elem_of_map_to_list.
Qed.

Lemma persistent_volume_claim_template_lookup_elem templates name template :
  persistent_volume_claim_templates_by_name templates !! name =
    Some template →
  template ∈ templates ∧
  template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') = name.
Proof.
  induction templates using rev_ind; intros Hlookup.
  - rewrite /persistent_volume_claim_templates_by_name /=
      lookup_empty in Hlookup. done.
  - rewrite persistent_volume_claim_templates_by_name_snoc
      /persistent_volume_claim_template_insert in Hlookup.
    destruct (decide
      (x.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') = name))
      as [Hname|Hname].
    + rewrite Hname lookup_insert_eq in Hlookup. simplify_eq/=.
      split; first (apply elem_of_app; right; by left). done.
    + assert (<[x.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'):=x]>
          (persistent_volume_claim_templates_by_name templates) !! name =
          persistent_volume_claim_templates_by_name templates !! name) as Heq.
      { rewrite lookup_insert_ne //. }
      rewrite Heq in Hlookup.
      apply IHtemplates in Hlookup as [Hlookup Htemplate_name].
      split; [apply elem_of_app; by left|exact Htemplate_name].
Qed.

Lemma desired_pvc_key_of_template_is_desired set ordinal name template :
  (ordinal < statefulset_replicas set)%nat →
  persistent_volume_claim_templates_by_name
      (StatefulSetSpecV.volume_claim_templates_list
        set.(StatefulSetV.Spec')) !!
      name = Some template →
  desired_pvc_key set name ordinal ∈ desired_pvc_keys set.
Proof.
  intros Hordinal Hlookup.
  unfold desired_pvc_keys. rewrite elem_of_elements elem_of_list_to_set.
  unfold desired_pvc_key_candidates.
  apply list_elem_of_In. apply in_concat. exists
    ((λ claim_template_name, desired_pvc_key set claim_template_name ordinal)
      <$> pvc_claim_template_names set).
  split.
  - apply list_elem_of_In.
    apply (list_elem_of_fmap_2
      (λ ordinal0,
        (λ claim_template_name,
          desired_pvc_key set claim_template_name ordinal0) <$>
        pvc_claim_template_names set)
      (seq 0 (statefulset_replicas set)) ordinal).
    apply elem_of_seq. lia.
  - apply list_elem_of_In.
    apply (list_elem_of_fmap_2
      (λ claim_template_name,
        desired_pvc_key set claim_template_name ordinal)
      (pvc_claim_template_names set) name).
    unfold pvc_claim_template_names.
    pose proof (persistent_volume_claim_template_lookup_elem
      _ _ _ Hlookup) as [Htemplate Htemplate_name].
    rewrite -Htemplate_name.
    apply (list_elem_of_fmap_2
      (λ claim_template,
        claim_template.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.Name'))
      (StatefulSetSpecV.volume_claim_templates_list
        set.(StatefulSetV.Spec'))
      template).
    exact Htemplate.
Qed.

Lemma desired_pvc_key_name_inj set ordinal name1 name2 :
  desired_pvc_key set name1 ordinal =
    desired_pvc_key set name2 ordinal →
  name1 = name2.
Proof.
  intros Hkey. apply (f_equal KKey.Name') in Hkey. simpl in Hkey.
  unfold desired_pvc_name in Hkey.
  set suffix := "-"%go ++
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++
    decimal_string ordinal.
  change (name1 ++ suffix = name2 ++ suffix) in Hkey.
  by apply app_inv_tail in Hkey.
Qed.

(* Identity repair is submitted using a deep copy, so it can change the Pod
   stored in the model without changing the Pod value in the caller's slice.
   The fields below are exactly those needed by the later condemned/outdated
   stages to identify and delete that same stored object. *)
Definition local_pod_matches_stored (local stored : PodV.t) : Prop :=
  PodV.key local = PodV.key stored ∧
  local.(PodV.ObjectMeta').(ObjectMetaV.UID') =
    stored.(PodV.ObjectMeta').(ObjectMetaV.UID') ∧
  local.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') =
    stored.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ∧
  local.(PodV.Spec') = stored.(PodV.Spec').

Definition local_pods_match_stored
    (local stored : list PodV.t) : Prop :=
  Forall2 local_pod_matches_stored local stored.

Definition unprocessed_pods_unchanged set next
    (local stored : list PodV.t) : Prop :=
  Forall2
    (λ local_pod stored_pod,
      ∀ ordinal,
        (next ≤ ordinal)%nat →
        PodV.key local_pod = desired_pod_key set ordinal →
        stored_pod = local_pod)
    local stored.

Definition desired_prefix_reconciled set next (pods : list PodV.t)
    (pvc_map : gmap KKey.t PersistentVolumeClaimV.t) : Prop :=
  ∀ ordinal,
    (ordinal < next)%nat →
    (ordinal < statefulset_replicas set)%nat →
    ( (∃ pod,
        pod ∈ pods ∧
        PodV.key pod = desired_pod_key set ordinal ∧
        is_pod_alive pod ∧
        pod_identity_matches set pod) ∧
      (∀ claim_template_name,
        claim_template_name ∈ dom
          (persistent_volume_claim_templates_by_name
            (StatefulSetSpecV.volume_claim_templates_list
              set.(StatefulSetV.Spec'))) →
        desired_pvc_key set claim_template_name ordinal ∈ dom pvc_map) ).

(* Facts established after every desired ordinal has been processed. Extra
   Pods may still be condemned, and desired Pods may still have immutable
   fields that require replacement. *)
Definition desired_objects_reconciled sts pods pvcs : Prop :=
  missing_pod_keys sts pods = [] ∧
  missing_pvc_keys sts pvcs = [] ∧
  Forall
    (λ pod,
      pod_key_is_desired sts (PodV.key pod) →
      is_pod_alive pod ∧ pod_identity_matches sts pod)
    pods.

Lemma local_pods_match_stored_refl pods :
  local_pods_match_stored pods pods.
Proof.
  induction pods as [|pod pods IH]; constructor.
  - unfold local_pod_matches_stored. done.
  - exact IH.
Qed.

Lemma unprocessed_pods_unchanged_refl set next pods :
  unprocessed_pods_unchanged set next pods pods.
Proof.
  induction pods as [|pod pods IH]; constructor.
  - intros. done.
  - exact IH.
Qed.

Lemma desired_prefix_reconciled_zero set pods pvc_map :
  desired_prefix_reconciled set 0 pods pvc_map.
Proof. intros ordinal Hordinal. lia. Qed.

Definition own_pvc_map γ
    (pvc_map : gmap KKey.t PersistentVolumeClaimV.t) : iProp Σ :=
  ([∗ map] key↦pvc ∈ pvc_map,
    own_meta_frag γ key
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
    own_occupied_reserved_frag γ key
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))%I.

Lemma own_pvc_list_as_map γ pvcs :
  NoDup (PersistentVolumeClaimV.key <$> pvcs) →
  ([∗ list] pvc ∈ pvcs,
    own_meta_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
    own_occupied_reserved_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ⊣⊢
  own_pvc_map γ (pvc_map_of_list pvcs).
Proof.
  intros Hnodup.
  rewrite /own_pvc_map /pvc_map_of_list.
  assert (NoDup
      (((λ pvc, (PersistentVolumeClaimV.key pvc, pvc)) <$> pvcs).*1))
    as Hpairs.
  { rewrite -list_fmap_compose. exact Hnodup. }
  rewrite (big_sepM_list_to_map _ _ Hpairs).
  rewrite big_sepL_fmap. done.
Qed.

Lemma own_pvc_map_as_list γ pvc_map :
  (∀ key pvc, pvc_map !! key = Some pvc →
    PersistentVolumeClaimV.key pvc = key) →
  own_pvc_map γ pvc_map ⊣⊢
  ([∗ list] pvc ∈ pvc_list_of_map pvc_map,
    own_meta_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
    own_occupied_reserved_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')).
Proof.
  intros Hwf.
  rewrite /own_pvc_map /pvc_list_of_map big_sepM_map_to_list.
  rewrite big_sepL_fmap. simpl.
  apply big_sepL_proper. intros idx [key pvc] Hlookup. simpl.
  assert (pvc_map !! key = Some pvc) as Hmap_lookup.
  { apply elem_of_map_to_list. apply list_elem_of_lookup_2 in Hlookup.
    exact Hlookup. }
  by rewrite (Hwf key pvc Hmap_lookup).
Qed.

Definition pvc_ready γ set ordinal claim_template_name claim_template :
    iProp Σ :=
  ((∃ claim,
      ⌜ PersistentVolumeClaimV.key claim =
          desired_pvc_key set claim_template_name ordinal ⌝ ∗
      own_meta_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
        claim.(PersistentVolumeClaimV.ObjectMeta') ∗
      own_occupied_reserved_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
   (own_available_frag γ
      (desired_pvc_key set claim_template_name ordinal) ∗
    ⌜ PersistentVolumeClaimV.valid_named_create
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
        (new_persistent_volume_claim set claim_template ordinal) ⌝))%I.

Definition pvc_done γ set ordinal claim_template_name : iProp Σ :=
  (∃ claim,
    ⌜ PersistentVolumeClaimV.key claim =
        desired_pvc_key set claim_template_name ordinal ⌝ ∗
    own_meta_frag γ
      (desired_pvc_key set claim_template_name ordinal)
      claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      claim.(PersistentVolumeClaimV.ObjectMeta') ∗
    own_occupied_reserved_frag γ
      (desired_pvc_key set claim_template_name ordinal)
      claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))%I.

(* Turn the global PVC map and its outstanding reservations into the
   name-indexed state expected by [createPersistentVolumeClaims].  The wand
   consumes the function's completed per-template states and rebuilds a
   well-formed global map, including every PVC that the call just ensured. *)
Lemma prepare_pvc_states γ set ordinal
    (claim_templates : gmap go_string PersistentVolumeClaimV.t)
    (pvc_map : gmap KKey.t PersistentVolumeClaimV.t)
    (reserved : list KKey.t) (required : gset KKey.t) :
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  NoDup reserved →
  (∀ key, key ∈ required → key ∈ dom pvc_map ∨ key ∈ reserved) →
  (∀ name claim_template,
    claim_templates !! name = Some claim_template →
    desired_pvc_key set name ordinal ∈ required) →
  (∀ name1 name2, name1 ∈ dom claim_templates →
    name2 ∈ dom claim_templates →
    desired_pvc_key set name1 ordinal =
      desired_pvc_key set name2 ordinal → name1 = name2) →
  (∀ name claim_template,
    claim_templates !! name = Some claim_template →
    PersistentVolumeClaimV.valid_named_create
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
      (new_persistent_volume_claim set claim_template ordinal)) →
  own_pvc_map γ pvc_map -∗
  ([∗ list] key ∈ reserved, own_available_frag γ key) -∗
  ([∗ map] name↦claim_template ∈ claim_templates,
    pvc_ready γ set ordinal name claim_template) ∗
  (([∗ set] name ∈ dom claim_templates,
      pvc_done γ set ordinal name) -∗
    ∃ (pvc_map' : gmap KKey.t PersistentVolumeClaimV.t)
      (reserved' : list KKey.t),
      own_pvc_map γ pvc_map' ∗
      ([∗ list] key ∈ reserved', own_available_frag γ key) ∗
      ⌜ (∀ key claim, pvc_map' !! key = Some claim →
            PersistentVolumeClaimV.key claim = key) ∧
        NoDup reserved' ∧
        (∀ key, key ∈ required →
          key ∈ dom pvc_map' ∨ key ∈ reserved') ∧
        dom pvc_map ⊆ dom pvc_map' ∧
        (∀ name, name ∈ dom claim_templates →
          desired_pvc_key set name ordinal ∈ dom pvc_map') ⌝).
Proof.
  revert pvc_map reserved required.
  induction claim_templates as
      [|name claim_template claim_templates Hname_fresh IH] using map_ind;
    intros pvc_map reserved required Hwf Hreserved_nodup Hcoverage
      Hrequired Hinjective Hvalid;
    rewrite ?big_sepM_empty ?dom_empty_L ?big_sepS_empty.
  - iIntros "Hpvc_map Hreserved". iSplit; first done.
    iIntros "_". iExists pvc_map, reserved. iFrame.
    iPureIntro. split_and!; try done.
  - set key := desired_pvc_key set name ordinal.
    assert (key ∈ required) as Hkey_required.
    { apply (Hrequired name claim_template).
      rewrite lookup_insert_eq. done. }
    assert (∀ other, other ∈ dom claim_templates →
        desired_pvc_key set other ordinal ≠ key) as Hother_ne.
    { intros other Hother Heq.
      assert (other = name) as ->.
      { eapply Hinjective; [| |exact Heq].
        - rewrite dom_insert_L. apply elem_of_union. right. exact Hother.
        - rewrite dom_insert_L.
          Timeout 10 set_solver. }
      apply elem_of_dom in Hother. rewrite Hname_fresh in Hother. done. }
    assert (∀ other other_template,
        claim_templates !! other = Some other_template →
        desired_pvc_key set other ordinal ∈ required ∖ {[key]})
      as Hrequired_tail.
    { intros other other_template Hlookup.
      assert (name ≠ other) as Hne.
      { intros ->. rewrite Hname_fresh in Hlookup. done. }
      apply elem_of_difference. split.
      - eapply Hrequired. rewrite lookup_insert_ne //.
      - rewrite elem_of_singleton. intros Heq.
        eapply (Hother_ne other); [by apply elem_of_dom|exact Heq]. }
    assert (∀ other1 other2,
        other1 ∈ dom claim_templates → other2 ∈ dom claim_templates →
        desired_pvc_key set other1 ordinal =
          desired_pvc_key set other2 ordinal → other1 = other2)
      as Hinjective_tail.
    { intros other1 other2 Hother1 Hother2 Heq.
      eapply Hinjective; [| |exact Heq].
      - rewrite dom_insert_L. apply elem_of_union. right. exact Hother1.
      - rewrite dom_insert_L. apply elem_of_union. right. exact Hother2. }
    assert (∀ other other_template,
        claim_templates !! other = Some other_template →
        PersistentVolumeClaimV.valid_named_create
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
          (new_persistent_volume_claim set other_template ordinal))
      as Hvalid_tail.
    { intros other other_template Hlookup. eapply Hvalid.
      assert (name ≠ other) as Hne.
      { intros ->. rewrite Hname_fresh in Hlookup. done. }
      rewrite lookup_insert_ne //. }
    pose proof (Hvalid name claim_template ltac:(by rewrite lookup_insert_eq))
      as Hvalid_head.
    assert (name ∉ dom claim_templates) as Hname_notin.
    { apply not_elem_of_dom. exact Hname_fresh. }
    rewrite big_sepM_insert // dom_insert_L
      (big_sepS_insert _ _ _ Hname_notin).
    destruct (pvc_map !! key) as [existing|] eqn:Hkey_lookup.
    + iIntros "Hpvc_map Hreserved".
      iEval (rewrite /own_pvc_map
        (big_sepM_delete _ pvc_map key existing Hkey_lookup))
        in "Hpvc_map".
      iDestruct "Hpvc_map" as "[Hexisting Hpvc_map]".
      iDestruct (IH (delete key pvc_map) reserved (required ∖ {[key]})
        with "Hpvc_map Hreserved") as "[Hready Hfinish]".
      { intros other claim Hlookup.
        apply lookup_delete_Some in Hlookup as [_ Hlookup]. by eapply Hwf. }
      { exact Hreserved_nodup. }
      { intros other Hother.
        apply elem_of_difference in Hother as [Hother Hne].
        specialize (Hcoverage other Hother).
        destruct Hcoverage as [Hin|Hin]; [left|by right].
        rewrite elem_of_dom lookup_delete_is_Some.
        rewrite elem_of_dom in Hin. split.
        - intros ->. apply Hne. Timeout 10 set_solver.
        - exact Hin. }
      { exact Hrequired_tail. }
      { exact Hinjective_tail. }
      { exact Hvalid_tail. }
      iSplitL "Hexisting Hready".
      { iSplitL "Hexisting"; last iExact "Hready".
        iLeft. iExists existing. iFrame.
        iPureIntro.
        pose proof (Hwf key existing Hkey_lookup) as Hexisting_key.
        exact Hexisting_key. }
      iIntros "[Hdone Hdone_tail]".
      iDestruct "Hdone" as (claim) "[%Hclaim_key Hclaim]".
      iDestruct ("Hfinish" with "Hdone_tail") as
        (pvc_map_tail reserved')
        "(Hpvc_map & Hreserved & %Hresult)".
      destruct Hresult as
        (Hwf_tail & Hreserved_nodup' & Hcoverage_tail &
          Hdom_tail & Hdone_tail).
      iEval (rewrite /own_pvc_map) in "Hpvc_map".
      destruct (pvc_map_tail !! key) as [other_claim|] eqn:Htail_lookup.
      { iDestruct (big_sepM_lookup_acc with "Hpvc_map") as
          "[Hother_claim _]"; first exact Htail_lookup.
        iDestruct "Hclaim" as "[Hclaim _]".
        iDestruct "Hother_claim" as "[Hother_claim _]".
        iDestruct (kview.own_meta_meta_false (γ:=γ.(γ_state)) eq_refl
          with "Hclaim Hother_claim") as %[]. }
      iExists (<[key:=claim]> pvc_map_tail), reserved'.
      rewrite /own_pvc_map big_sepM_insert //.
      iFrame.
      iPureIntro. split_and!.
      * intros other claim' Hlookup.
        apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [[<- <-]|[_ Hlookup]].
        -- exact Hclaim_key.
        -- by eapply Hwf_tail.
      * exact Hreserved_nodup'.
      * intros other Hother.
        destruct (decide (other = key)) as [->|Hne].
        -- left. rewrite dom_insert_L. Timeout 10 set_solver.
        -- destruct (Hcoverage_tail other ltac:(
             apply elem_of_difference; split; first done;
             rewrite elem_of_singleton; done)) as [Hin|Hin].
           ++ left. rewrite dom_insert_L. apply elem_of_union. right. exact Hin.
           ++ by right.
      * intros other Hother.
        destruct (decide (other = key)) as [->|Hne].
        -- rewrite dom_insert_L. Timeout 10 set_solver.
        -- rewrite dom_insert_L. apply elem_of_union. right.
           apply Hdom_tail. rewrite elem_of_dom lookup_delete_is_Some.
           rewrite elem_of_dom in Hother. split; [congruence|exact Hother].
      * intros other Hother.
        rewrite dom_insert_L.
        destruct (decide (other = name)) as [->|Hne].
        -- apply elem_of_union. left. rewrite elem_of_singleton.
           unfold key. done.
        -- apply elem_of_union. right. apply Hdone_tail.
           apply elem_of_union in Hother as [Hother|Hother]; last exact Hother.
           rewrite elem_of_singleton in Hother. contradiction.
    + assert (key ∈ reserved) as Hkey_reserved.
      { destruct (Hcoverage key Hkey_required) as [Hin|Hin]; last done.
        rewrite elem_of_dom Hkey_lookup in Hin. done. }
      apply list_elem_of_lookup_1 in Hkey_reserved as (idx & Hreserved_lookup).
      set reserved_tail := take idx reserved ++ drop (S idx) reserved.
      iIntros "Hpvc_map Hreserved".
      iDestruct (big_sepL_split_lookup _ _ _ _ Hreserved_lookup
        with "Hreserved") as "(Hreserved_before & Hkey & Hreserved_after)".
      iAssert (([∗ list] other ∈
          take idx reserved ++ drop (S idx) reserved,
          own_available_frag γ other))%I
        with "[Hreserved_before Hreserved_after]" as "Hreserved".
      { rewrite big_sepL_app.
        iSplitL "Hreserved_before"; iFrame. }
      iDestruct (IH pvc_map reserved_tail (required ∖ {[key]})
        with "Hpvc_map Hreserved") as "[Hready Hfinish]".
      { exact Hwf. }
      { unfold reserved_tail.
        pose proof Hreserved_nodup as Hnodup.
        rewrite -(take_drop_middle reserved idx key Hreserved_lookup) in Hnodup.
        apply list.NoDup_app in Hnodup as
          (Hbefore_nodup & Hbefore_disjoint & Htail_nodup).
        inversion Htail_nodup as [|? ? _ Hafter_nodup]; subst.
        apply list.NoDup_app. split_and!; try done.
        intros other Hbefore Hafter.
        apply (Hbefore_disjoint other Hbefore). by right. }
      { intros other Hother.
        apply elem_of_difference in Hother as [Hother Hne].
        specialize (Hcoverage other Hother).
        destruct Hcoverage as [Hin|Hin]; first by left.
        right. unfold reserved_tail.
        rewrite -(take_drop_middle reserved idx key Hreserved_lookup) in Hin.
        apply elem_of_app in Hin as [Hin|Hin].
        - apply elem_of_app. left. exact Hin.
        - apply elem_of_cons in Hin as [Heq|Hin].
          + exfalso. apply Hne. rewrite elem_of_singleton. exact Heq.
          + apply elem_of_app. right. exact Hin. }
      { exact Hrequired_tail. }
      { exact Hinjective_tail. }
      { exact Hvalid_tail. }
      iSplitL "Hkey Hready".
      { iSplitL "Hkey"; last iExact "Hready".
        iRight. iFrame. done. }
      iIntros "[Hdone Hdone_tail]".
      iDestruct "Hdone" as (claim) "[%Hclaim_key Hclaim]".
      iDestruct ("Hfinish" with "Hdone_tail") as
        (pvc_map_tail reserved')
        "(Hpvc_map & Hreserved & %Hresult)".
      destruct Hresult as
        (Hwf_tail & Hreserved_nodup' & Hcoverage_tail &
          Hdom_tail & Hdone_tail).
      iEval (rewrite /own_pvc_map) in "Hpvc_map".
      destruct (pvc_map_tail !! key) as [other_claim|] eqn:Htail_lookup.
      { iDestruct (big_sepM_lookup_acc with "Hpvc_map") as
          "[Hother_claim _]"; first exact Htail_lookup.
        iDestruct "Hclaim" as "[Hclaim _]".
        iDestruct "Hother_claim" as "[Hother_claim _]".
        iDestruct (kview.own_meta_meta_false (γ:=γ.(γ_state)) eq_refl
          with "Hclaim Hother_claim") as %[]. }
      iExists (<[key:=claim]> pvc_map_tail), reserved'.
      rewrite /own_pvc_map big_sepM_insert //.
      iFrame.
      iPureIntro. split_and!.
      * intros other claim' Hlookup.
        apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [[<- <-]|[_ Hlookup]].
        -- exact Hclaim_key.
        -- by eapply Hwf_tail.
      * exact Hreserved_nodup'.
      * intros other Hother.
        destruct (decide (other = key)) as [->|Hne].
        -- left. rewrite dom_insert_L. Timeout 10 set_solver.
        -- destruct (Hcoverage_tail other ltac:(
             apply elem_of_difference; split; first done;
             rewrite elem_of_singleton; done)) as [Hin|Hin].
           ++ left. rewrite dom_insert_L. apply elem_of_union. right. exact Hin.
           ++ by right.
      * intros other Hother. rewrite dom_insert_L.
        apply elem_of_union. right. by apply Hdom_tail.
      * intros other Hother.
        rewrite dom_insert_L.
        destruct (decide (other = name)) as [->|Hne].
        -- apply elem_of_union. left. rewrite elem_of_singleton.
           unfold key. done.
        -- apply elem_of_union. right. apply Hdone_tail.
           apply elem_of_union in Hother as [Hother|Hother]; last exact Hother.
           rewrite elem_of_singleton in Hother. contradiction.
Qed.

Lemma local_pod_matches_stored_key_name local stored :
  local_pod_matches_stored local stored →
  local.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    stored.(PodV.ObjectMeta').(ObjectMetaV.Name').
Proof.
  intros (Hkey & _).
  apply (f_equal KKey.Name') in Hkey. exact Hkey.
Qed.

Lemma local_pod_matches_stored_alive local stored :
  local_pod_matches_stored local stored →
  (is_pod_alive local ↔ is_pod_alive stored).
Proof.
  intros (_ & _ & Hdeletion & _).
  unfold is_pod_alive. rewrite Hdeletion. done.
Qed.

Lemma local_pod_matches_stored_condemned set local stored :
  local_pod_matches_stored local stored →
  (pod_is_condemned set local ↔ pod_is_condemned set stored).
Proof.
  intros Hmatches.
  unfold pod_is_condemned.
  rewrite (local_pod_matches_stored_key_name _ _ Hmatches). done.
Qed.

Lemma local_pod_matches_stored_outdated set local stored :
  local_pod_matches_stored local stored →
  (pod_is_outdated set local ↔ pod_is_outdated set stored).
Proof.
  intros (Hkey & _ & _ & Hspec).
  apply (f_equal KKey.Name') in Hkey.
  unfold PodV.key, PodV.meta_key in Hkey. simpl in Hkey.
  assert (pod_storage_matches set local ↔
      pod_storage_matches set stored) as Hstorage.
  { unfold pod_storage_matches. rewrite Hkey Hspec. done. }
  assert (pod_immutable_matches set local ↔
      pod_immutable_matches set stored) as Himmutable.
  { unfold pod_immutable_matches. rewrite Hkey Hspec Hstorage. done. }
  unfold pod_is_outdated. split.
  - intros (ordinal & Hbound & Hname & Hdesired & Hnot_immutable).
    exists ordinal. split_and!; try done.
    + rewrite -Hkey. exact Hname.
    + intros Hstored. apply Hnot_immutable.
      apply (proj2 Himmutable). exact Hstored.
  - intros (ordinal & Hbound & Hname & Hdesired & Hnot_immutable).
    exists ordinal. split_and!; try done.
    + rewrite Hkey. exact Hname.
    + intros Hlocal. apply Hnot_immutable.
      apply (proj1 Himmutable). exact Hlocal.
Qed.

Lemma local_pods_match_stored_lookup local stored idx local_pod :
  local_pods_match_stored local stored →
  local !! idx = Some local_pod →
  ∃ stored_pod,
    stored !! idx = Some stored_pod ∧
    local_pod_matches_stored local_pod stored_pod.
Proof.
  intros Hmatches. revert idx local_pod.
  induction Hmatches as [|local_pod0 stored_pod0 local stored
      Hhead Htail IH]; intros idx local_pod Hlookup.
  - destruct idx; done.
  - destruct idx as [|idx]; simpl in Hlookup.
    + injection Hlookup as <-. exists stored_pod0. split; done.
    + apply IH in Hlookup as (stored_pod & Hlookup & Hmatches).
      exists stored_pod. split; done.
Qed.

Lemma unprocessed_pods_unchanged_lookup set next local stored
    idx local_pod stored_pod :
  unprocessed_pods_unchanged set next local stored →
  local !! idx = Some local_pod →
  stored !! idx = Some stored_pod →
  ∀ ordinal,
    (next ≤ ordinal)%nat →
    PodV.key local_pod = desired_pod_key set ordinal →
    stored_pod = local_pod.
Proof.
  intros Hunchanged. revert idx local_pod stored_pod.
  induction Hunchanged as [|local0 stored0 local stored
      Hhead Htail IH]; intros idx local_pod stored_pod
      Hlocal Hstored ordinal Hnext Hkey.
  - destruct idx; done.
  - destruct idx as [|idx]; simpl in Hlocal, Hstored.
    + injection Hlocal as <-. injection Hstored as <-.
      by eapply Hhead.
    + by eapply IH.
Qed.

Lemma pod_identity_matches_meta_updated set pod pod' :
  pod_identity_matches set pod →
  PodV.key pod = PodV.key pod' →
  ObjectMetaV.updated pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') →
  pod_identity_matches set pod'.
Proof.
  destruct pod as [typemeta meta spec status],
    pod' as [typemeta' meta' spec' status']; simpl.
  destruct meta, meta'; simpl.
  unfold pod_identity_matches, PodV.key, PodV.meta_key.
  simpl. intros Hidentity Hkey Hupdated.
  destruct Hupdated as
    (Hname & _ & Hnamespace & _ & _ & _ & _ & _ & Hlabels & _).
  simpl in Hname, Hnamespace, Hlabels.
  rewrite Hname Hnamespace Hlabels. exact Hidentity.
Qed.

Lemma local_pods_match_stored_insert local stored idx local_pod stored_pod' :
  local_pods_match_stored local stored →
  local !! idx = Some local_pod →
  local_pod_matches_stored local_pod stored_pod' →
  local_pods_match_stored local (<[idx:=stored_pod']> stored).
Proof.
  intros Hmatches Hlookup Hhead.
  rewrite -(list_insert_id local idx local_pod Hlookup).
  by apply Forall2_insert.
Qed.

Lemma unprocessed_pods_unchanged_mono set next next' local stored :
  (next ≤ next')%nat →
  unprocessed_pods_unchanged set next local stored →
  unprocessed_pods_unchanged set next' local stored.
Proof.
  intros Hnext Hunchanged.
  eapply Forall2_impl; last exact Hunchanged.
  intros local_pod stored_pod Hpod ordinal Hordinal Hkey.
  eapply Hpod; [exact (Nat.le_trans _ _ _ Hnext Hordinal)|exact Hkey].
Qed.

Lemma unprocessed_pods_unchanged_insert set next local stored idx
    local_pod stored_pod' :
  unprocessed_pods_unchanged set next local stored →
  local !! idx = Some local_pod →
  PodV.key local_pod = desired_pod_key set next →
  unprocessed_pods_unchanged set (S next) local
    (<[idx:=stored_pod']> stored).
Proof.
  intros Hunchanged Hlookup Hlocal_key.
  pose proof (unprocessed_pods_unchanged_mono set next (S next)
    local stored ltac:(lia) Hunchanged) as Htail.
  rewrite -(list_insert_id local idx local_pod Hlookup).
  apply Forall2_insert; first exact Htail.
  intros ordinal Hordinal Hkey.
  exfalso. assert (ordinal = next).
  { apply (desired_pod_name_inj
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
    apply (f_equal KKey.Name') in Hlocal_key.
    apply (f_equal KKey.Name') in Hkey.
    simpl in Hlocal_key, Hkey. rewrite -Hlocal_key Hkey. done. }
  lia.
Qed.

Lemma local_pods_match_stored_keys local stored :
  local_pods_match_stored local stored →
  PodV.key <$> local = PodV.key <$> stored.
Proof.
  intros Hmatches.
  induction Hmatches as [|local_pod stored_pod local stored
      [Hkey _] _ IH]; simpl; first done.
  f_equal; done.
Qed.

Lemma local_pods_match_stored_no_condemned set local stored :
  local_pods_match_stored local stored →
  Forall (λ pod, ¬ pod_is_condemned set pod) local →
  Forall (λ pod, ¬ pod_is_condemned set pod) stored.
Proof.
  intros Hmatches Hnone.
  induction Hmatches as [|local_pod stored_pod local stored
      Hhead Htail IH]; inversion Hnone; subst; constructor.
  - intros Hcondemned.
    apply H1. apply (proj2
      (local_pod_matches_stored_condemned set _ _ Hhead)).
    exact Hcondemned.
  - by apply IH.
Qed.

Lemma local_pods_match_stored_no_outdated set local stored :
  local_pods_match_stored local stored →
  Forall (λ pod, ¬ pod_is_outdated set pod) local →
  Forall (λ pod, ¬ pod_is_outdated set pod) stored.
Proof.
  intros Hmatches Hnone.
  induction Hmatches as [|local_pod stored_pod local stored
      Hhead Htail IH]; inversion Hnone; subst; constructor.
  - intros Houtdated.
    apply H1. apply (proj2
      (local_pod_matches_stored_outdated set _ _ Hhead)).
    exact Houtdated.
  - by apply IH.
Qed.

Lemma local_pods_match_stored_alive_all local stored :
  local_pods_match_stored local stored →
  Forall is_pod_alive local →
  Forall is_pod_alive stored.
Proof.
  intros Hmatches Halive.
  induction Hmatches as [|local_pod stored_pod local stored
      Hhead Htail IH]; inversion Halive; subst; constructor.
  - apply (proj1 (local_pod_matches_stored_alive _ _ Hhead)). exact H1.
  - by apply IH.
Qed.

Lemma local_pods_match_stored_members set local stored :
  local_pods_match_stored local stored →
  Forall (pod_has_int32_member_key set) local →
  Forall (pod_has_int32_member_key set) stored.
Proof.
  intros Hmatches Hmembers.
  induction Hmatches as [|local_pod stored_pod local stored
      Hhead Htail IH]; inversion Hmembers; subst; constructor.
  - destruct Hhead as (Hkey & _).
    destruct H1 as (Hnamespace & ordinal & Hbound & Hname).
    apply (f_equal KKey.Namespace') in Hkey as Hnamespace_key.
    apply (f_equal KKey.Name') in Hkey as Hname_key.
    unfold PodV.key, PodV.meta_key in Hnamespace_key, Hname_key.
    simpl in Hnamespace_key, Hname_key.
    split.
    + rewrite -Hnamespace_key. exact Hnamespace.
    + exists ordinal. split; first done.
      rewrite -Hname_key. exact Hname.
  - by apply IH.
Qed.

Lemma pending_pods_empty_alive set pods :
  filter (pending_pod set) pods = [] →
  Forall (pod_has_int32_member_key set) pods →
  Forall is_pod_alive pods.
Proof.
  intros Hpending Hmembers.
  apply Forall_forall. intros pod Hpod.
  rewrite -list_elem_of_In in Hpod.
  rewrite Forall_forall in Hmembers.
  destruct (decide (is_pod_alive pod)) as [Halive|Hnot_alive]; first done.
  exfalso.
  assert (pod ∈ filter (pending_pod set) pods) as Hcontra.
  { apply list_elem_of_filter. split.
    - split; first exact Hnot_alive.
      pose proof (Hmembers pod ltac:(by rewrite -list_elem_of_In))
        as Hmember.
      exact (proj2 Hmember).
    - exact Hpod. }
  rewrite Hpending in Hcontra. inversion Hcontra.
Qed.

Lemma desired_pod_key_elem_iff set ordinal :
  desired_pod_key set ordinal ∈ desired_pod_keys set ↔
  (ordinal < statefulset_replicas set)%nat.
Proof.
  unfold desired_pod_keys, desired_ordinals. split.
  - intros Hkey.
    apply list_elem_of_fmap_1 in Hkey as
      (ordinal' & Hkey & Hordinal').
    apply (f_equal KKey.Name') in Hkey. simpl in Hkey.
    apply desired_pod_name_inj in Hkey. subst ordinal'.
    apply elem_of_seq in Hordinal'. lia.
  - intros Hbound. apply list_elem_of_fmap_2.
    apply elem_of_seq. lia.
Qed.

Lemma desired_pod_key_inj set ordinal1 ordinal2 :
  desired_pod_key set ordinal1 = desired_pod_key set ordinal2 →
  ordinal1 = ordinal2.
Proof.
  intros Hkey. apply (f_equal KKey.Name') in Hkey. simpl in Hkey.
  by apply desired_pod_name_inj in Hkey.
Qed.

Lemma pod_int32_member_key set pod ordinal :
  pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') →
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    desired_pod_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal →
  PodV.key pod = desired_pod_key set ordinal.
Proof.
  intros Hnamespace Hname.
  rewrite /PodV.key /PodV.meta_key /desired_pod_key /=
    Hnamespace Hname. done.
Qed.

Lemma pod_int32_member_condemned_iff set pod :
  pod_has_int32_member_key set pod →
  (pod_is_condemned set pod ↔
    ¬ pod_key_is_desired set (PodV.key pod)).
Proof.
  intros (Hnamespace & ordinal & Hbound & Hname).
  pose proof (pod_int32_member_key set pod ordinal
    Hnamespace Hname) as Hkey.
  unfold pod_is_condemned, pod_key_is_desired.
  rewrite Hkey desired_pod_key_elem_iff. split.
  - intros (ordinal' & _ & Hname' & Hreplicas) Hdesired.
    assert (ordinal = ordinal') as ->.
    { apply (desired_pod_name_inj
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
      rewrite -Hname -Hname'. done. }
    lia.
  - intros Hnot_desired. exists ordinal. split_and!; try done. lia.
Qed.

Lemma pod_int32_member_outdated_iff set pod :
  pod_has_int32_member_key set pod →
  (pod_is_outdated set pod ↔
    pod_key_is_desired set (PodV.key pod) ∧
    ¬ pod_immutable_matches set pod).
Proof.
  intros (Hnamespace & ordinal & Hbound & Hname).
  pose proof (pod_int32_member_key set pod ordinal
    Hnamespace Hname) as Hkey.
  unfold pod_is_outdated, pod_key_is_desired.
  rewrite Hkey desired_pod_key_elem_iff. split.
  - intros (ordinal' & _ & Hname' & Hdesired & Hnot_immutable).
    assert (ordinal = ordinal') as ->.
    { apply (desired_pod_name_inj
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
      rewrite -Hname -Hname'. done. }
    done.
  - intros (Hdesired & Hnot_immutable).
    exists ordinal. split_and!; done.
Qed.

Lemma pod_has_int32_member_key_of_key_eq set pod pod' :
  PodV.key pod = PodV.key pod' →
  pod_has_int32_member_key set pod →
  pod_has_int32_member_key set pod'.
Proof.
  intros Hkey (Hnamespace & ordinal & Hbound & Hname).
  apply (f_equal KKey.Namespace') in Hkey as Hnamespace_key.
  apply (f_equal KKey.Name') in Hkey as Hname_key.
  unfold PodV.key, PodV.meta_key in Hnamespace_key, Hname_key.
  simpl in Hnamespace_key, Hname_key.
  split.
  - rewrite -Hnamespace_key. exact Hnamespace.
  - exists ordinal. split; first done.
    rewrite -Hname_key. exact Hname.
Qed.

Lemma pod_members_replace_by_key set before pod after pod' :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  PodV.key pod = PodV.key pod' →
  Forall (pod_has_int32_member_key set) (before ++ pod' :: after).
Proof.
  intros Hmembers Hkey.
  apply Forall_app in Hmembers as [Hbefore Htail].
  inversion Htail as [|? ? Hpod Hafter]; subst.
  apply Forall_app. split; first exact Hbefore.
  constructor; last exact Hafter.
  by eapply pod_has_int32_member_key_of_key_eq.
Qed.

Lemma pod_members_remove set before pod after :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  Forall (pod_has_int32_member_key set) (before ++ after).
Proof.
  intros Hmembers.
  apply Forall_app in Hmembers as [Hbefore Htail].
  inversion Htail as [|? ? _ Hafter]; subst.
  by apply Forall_app.
Qed.

Lemma pod_immutable_matches_key_spec_eq set pod pod' :
  PodV.key pod = PodV.key pod' →
  pod.(PodV.Spec') = pod'.(PodV.Spec') →
  (pod_immutable_matches set pod ↔ pod_immutable_matches set pod').
Proof.
  intros Hkey Hspec.
  apply (f_equal KKey.Name') in Hkey.
  unfold PodV.key, PodV.meta_key in Hkey. simpl in Hkey.
  assert (pod_storage_matches set pod ↔
      pod_storage_matches set pod') as Hstorage.
  { unfold pod_storage_matches. rewrite Hkey Hspec. done. }
  unfold pod_immutable_matches. rewrite Hkey Hspec Hstorage. done.
Qed.

Lemma filter_not_elem_add_irrelevant {A} `{EqDecision A}
    (keys before after : list A) x :
  x ∉ keys →
  filter (λ key, key ∉ before ++ after) keys =
    filter (λ key, key ∉ before ++ x :: after) keys.
Proof.
  induction keys as [|key keys IH]; intros Hx; simpl; first done.
  apply not_elem_of_cons in Hx as [Hne Hx].
  assert (key ∈ before ++ after ↔ key ∈ before ++ x :: after)
    as Hmember.
  { split.
    - intros Hin. apply elem_of_app in Hin as [Hbefore|Hafter].
      + apply elem_of_app. left. exact Hbefore.
      + apply elem_of_app. right. apply elem_of_cons. right. exact Hafter.
    - intros Hin. apply elem_of_app in Hin as [Hbefore|Htail].
      + apply elem_of_app. left. exact Hbefore.
      + apply elem_of_cons in Htail as [Heq|Hafter].
        * exfalso. apply Hne. symmetry. exact Heq.
        * apply elem_of_app. right. exact Hafter. }
  destruct (decide (key ∈ before ++ after)) as [Hin|Hnotin].
  - rewrite (filter_cons_False
      (λ key, key ∉ before ++ after) key keys
      ltac:(intros Hnot; exact (Hnot Hin))).
    rewrite (filter_cons_False
      (λ key, key ∉ before ++ x :: after) key keys
      ltac:(intros Hnot; apply Hnot; apply Hmember; exact Hin)).
    by apply IH.
  - rewrite (filter_cons_True
      (λ key, key ∉ before ++ after) key keys Hnotin).
    rewrite (filter_cons_True
      (λ key, key ∉ before ++ x :: after) key keys
      ltac:(intros H; apply Hnotin; apply Hmember; exact H)).
    f_equal. by apply IH.
Qed.

Lemma filter_not_elem_remove_unique {A} `{EqDecision A}
    (keys before after : list A) x :
  NoDup keys →
  x ∈ keys →
  x ∉ before →
  x ∉ after →
  length (filter (λ key, key ∉ before ++ after) keys) =
    S (length (filter (λ key, key ∉ before ++ x :: after) keys)).
Proof.
  induction keys as [|key keys IH]; intros Hnodup Hx Hbefore Hafter;
    first inversion Hx.
  inversion Hnodup as [|? ? Hkey_notin Hkeys_nodup]; subst.
  apply elem_of_cons in Hx as [Hkey|Hx].
  - subst key.
    assert (x ∉ before ++ after) as Hmissing.
    { intros Hin. apply elem_of_app in Hin as [Hin|Hin];
        [exact (Hbefore Hin)|exact (Hafter Hin)]. }
    assert (x ∈ before ++ x :: after) as Hpresent.
    { apply elem_of_app. right. apply elem_of_cons. by left. }
    rewrite (filter_cons_True
      (λ key, key ∉ before ++ after) x keys Hmissing)
      (filter_cons_False
        (λ key, key ∉ before ++ x :: after) x keys
        ltac:(intros Hnot; exact (Hnot Hpresent))) /=.
    rewrite (filter_not_elem_add_irrelevant keys before after x
      Hkey_notin). done.
  - assert (key ∈ before ++ after ↔ key ∈ before ++ x :: after)
      as Hmember.
    { assert (key ≠ x) as Hne.
      { intros ->. exact (Hkey_notin Hx). }
      split.
      - intros Hin. apply elem_of_app in Hin as [Hbefore'|Hafter'].
        + apply elem_of_app. left. exact Hbefore'.
        + apply elem_of_app. right. apply elem_of_cons. right. exact Hafter'.
      - intros Hin. apply elem_of_app in Hin as [Hbefore'|Htail].
        + apply elem_of_app. left. exact Hbefore'.
        + apply elem_of_cons in Htail as [Heq|Hafter'].
          * contradiction.
          * apply elem_of_app. right. exact Hafter'. }
    destruct (decide (key ∈ before ++ after)) as [Hin|Hnotin].
    + rewrite (filter_cons_False
        (λ key, key ∉ before ++ after) key keys
        ltac:(intros Hnot; exact (Hnot Hin))).
      rewrite (filter_cons_False
        (λ key, key ∉ before ++ x :: after) key keys
        ltac:(intros Hnot; apply Hnot; apply Hmember; exact Hin)).
      by apply IH.
    + rewrite (filter_cons_True
        (λ key, key ∉ before ++ after) key keys Hnotin).
      rewrite (filter_cons_True
        (λ key, key ∉ before ++ x :: after) key keys
        ltac:(intros H; apply Hnotin; apply Hmember; exact H)) /=.
      f_equal. by apply IH.
Qed.

Lemma match_distance_mark_deleting_condemned set before pod after pod' pvcs :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  pod_is_condemned set pod →
  is_pod_alive pod →
  PodV.key pod = PodV.key pod' →
  pod.(PodV.Spec') = pod'.(PodV.Spec') →
  ¬ is_pod_alive pod' →
  match_distance set (before ++ pod' :: after) pvcs <
    match_distance set (before ++ pod :: after) pvcs.
Proof.
  intros Hmembers Hcondemned Halive Hkey Hspec Hnot_alive.
  assert (pod_has_int32_member_key set pod) as Hmember.
  { rewrite Forall_forall in Hmembers. apply Hmembers.
    apply list_elem_of_In. apply elem_of_app. right. by left. }
  assert (pod_has_int32_member_key set pod') as Hmember'.
  { by eapply pod_has_int32_member_key_of_key_eq. }
  assert (¬ pod_key_is_desired set (PodV.key pod)) as Hnot_desired.
  { apply (proj1 (pod_int32_member_condemned_iff set pod Hmember)).
    exact Hcondemned. }
  assert (¬ pod_key_is_desired set (PodV.key pod')) as Hnot_desired'.
  { rewrite -Hkey. exact Hnot_desired. }
  assert (living_pods (before ++ pod :: after) =
      living_pods before ++ pod :: living_pods after) as Hliving_old.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_True is_pod_alive pod after Halive). done. }
  assert (living_pods (before ++ pod' :: after) =
      living_pods before ++ living_pods after) as Hliving_new.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_False is_pod_alive pod' after Hnot_alive). done. }
  assert (missing_pod_keys set
      (living_pods before ++ living_pods after) =
      missing_pod_keys set
        (living_pods before ++ pod :: living_pods after)) as Hmissing.
  { unfold missing_pod_keys. rewrite !fmap_app /=.
    apply filter_not_elem_add_irrelevant. exact Hnot_desired. }
  assert (outdated_pods set
      (living_pods before ++ living_pods after) =
      outdated_pods set
        (living_pods before ++ pod :: living_pods after)) as Houtdated.
  { unfold outdated_pods, needed_pods.
    rewrite !list.filter_app /=
      (filter_cons_False _ pod (living_pods after) Hnot_desired).
    done. }
  assert (bad_name_pods set
      (living_pods before ++ living_pods after) =
      bad_name_pods set
        (living_pods before ++ pod :: living_pods after)) as Hbad.
  { unfold bad_name_pods.
    rewrite !list.filter_app /= (filter_cons_False
      (λ pod, ¬ pod_has_int32_member_key set pod) pod
      (living_pods after) ltac:(intros Hnot; exact (Hnot Hmember))).
    done. }
  assert (condemned_pods set
      (living_pods before ++ pod :: living_pods after) =
      condemned_pods set (living_pods before) ++
        pod :: condemned_pods set (living_pods after)) as Hold_condemned.
  { unfold condemned_pods. rewrite list.filter_app /=.
    rewrite (filter_cons_True
      (λ pod0, pod_has_int32_member_key set pod0 ∧
        ¬ pod_key_is_desired set (PodV.key pod0))
      pod (living_pods after) ltac:(split; done)).
    done. }
  assert (condemned_pods set
      (living_pods before ++ living_pods after) =
      condemned_pods set (living_pods before) ++
        condemned_pods set (living_pods after)) as Hnew_condemned.
  { unfold condemned_pods. by rewrite list.filter_app. }
  unfold match_distance, pod_distance.
  rewrite Hliving_old Hliving_new.
  rewrite Hmissing Houtdated Hbad Hold_condemned Hnew_condemned.
  rewrite !app_length /=. lia.
Qed.

Lemma match_distance_mark_deleting_outdated set before pod after pod' pvcs :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  pod_is_outdated set pod →
  is_pod_alive pod →
  PodV.key pod = PodV.key pod' →
  pod.(PodV.Spec') = pod'.(PodV.Spec') →
  ¬ is_pod_alive pod' →
  match_distance set (before ++ pod' :: after) pvcs <
    match_distance set (before ++ pod :: after) pvcs.
Proof.
  intros Hmembers Hnodup Houtdated_pod Halive Hkey Hspec Hnot_alive.
  assert (pod_has_int32_member_key set pod) as Hmember.
  { rewrite Forall_forall in Hmembers. apply Hmembers.
    apply list_elem_of_In. apply elem_of_app. right. by left. }
  assert (pod_has_int32_member_key set pod') as Hmember'.
  { by eapply pod_has_int32_member_key_of_key_eq. }
  pose proof (proj1
    (pod_int32_member_outdated_iff set pod Hmember) Houtdated_pod)
    as [Hdesired Hnot_immutable].
  assert (pod_key_is_desired set (PodV.key pod')) as Hdesired'.
  { rewrite -Hkey. exact Hdesired. }
  assert (¬ pod_immutable_matches set pod') as Hnot_immutable'.
  { intros Himmutable'. apply Hnot_immutable.
    apply (proj2
      (pod_immutable_matches_key_spec_eq set pod pod' Hkey Hspec)).
    exact Himmutable'. }
  assert (¬ pod_match set pod) as Hnot_match.
  { intros [_ Himmutable]. exact (Hnot_immutable Himmutable). }
  assert (¬ pod_match set pod') as Hnot_match'.
  { intros [_ Himmutable]. exact (Hnot_immutable' Himmutable). }
  rewrite fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as
    (Hbefore_nodup & Hdisjoint & Htail_nodup).
  inversion Htail_nodup as [|? ? Hnot_after Hafter_nodup].
  assert (PodV.key pod ∉ PodV.key <$> before) as Hnot_before.
  { intros Hin. apply (Hdisjoint (PodV.key pod) Hin). by left. }
  assert (PodV.key pod ∉ PodV.key <$> living_pods before)
    as Hnot_before_living.
  { intros Hin. apply Hnot_before.
    apply list_elem_of_fmap_1 in Hin as (pod0 & -> & Hin).
    apply list_elem_of_fmap_2. unfold living_pods in Hin.
    by apply list_elem_of_filter in Hin as [_ Hin]. }
  assert (PodV.key pod ∉ PodV.key <$> living_pods after)
    as Hnot_after_living.
  { intros Hin. apply Hnot_after.
    apply list_elem_of_fmap_1 in Hin as (pod0 & -> & Hin).
    apply list_elem_of_fmap_2. unfold living_pods in Hin.
    by apply list_elem_of_filter in Hin as [_ Hin]. }
  assert (living_pods (before ++ pod :: after) =
      living_pods before ++ pod :: living_pods after) as Hliving_old.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_True is_pod_alive pod after Halive). done. }
  assert (living_pods (before ++ pod' :: after) =
      living_pods before ++ living_pods after) as Hliving_new.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_False is_pod_alive pod' after Hnot_alive). done. }
  assert (length (missing_pod_keys set
      (living_pods before ++ living_pods after)) =
      S (length (missing_pod_keys set
        (living_pods before ++ pod :: living_pods after)))) as Hmissing.
  { unfold missing_pod_keys. rewrite !fmap_app /=.
    apply filter_not_elem_remove_unique.
    - unfold desired_pod_keys, desired_ordinals. apply NoDup_fmap_2.
      + intros ordinal1 ordinal2 Hkey_eq.
        apply (f_equal KKey.Name') in Hkey_eq. simpl in Hkey_eq.
        by apply desired_pod_name_inj in Hkey_eq.
      + apply NoDup_seq.
    - exact Hdesired.
    - exact Hnot_before_living.
    - exact Hnot_after_living. }
  assert (outdated_pods set
      (living_pods before ++ pod :: living_pods after) =
      outdated_pods set (living_pods before) ++
        pod :: outdated_pods set (living_pods after)) as Hold_outdated.
  { unfold outdated_pods, needed_pods.
    rewrite list.filter_app /=
      (filter_cons_True _ pod (living_pods after) Hdesired).
    rewrite list.filter_app /=
      (filter_cons_True
        (λ pod0, ¬ pod_match set pod0)
        pod (filter (λ pod0, pod_key_is_desired set (PodV.key pod0))
          (living_pods after))
        Hnot_match).
    done. }
  assert (outdated_pods set
      (living_pods before ++ living_pods after) =
      outdated_pods set (living_pods before) ++
        outdated_pods set (living_pods after)) as Hnew_outdated.
  { unfold outdated_pods, needed_pods. by rewrite !list.filter_app. }
  assert (condemned_pods set
      (living_pods before ++ living_pods after) =
      condemned_pods set
        (living_pods before ++ pod :: living_pods after)) as Hcondemned.
  { unfold condemned_pods.
    rewrite !list.filter_app /= (filter_cons_False
      (λ pod0, pod_has_int32_member_key set pod0 ∧
        ¬ pod_key_is_desired set (PodV.key pod0)) pod
      (living_pods after) ltac:(intros [_ Hnot]; exact (Hnot Hdesired))).
    done. }
  assert (bad_name_pods set
      (living_pods before ++ living_pods after) =
      bad_name_pods set
        (living_pods before ++ pod :: living_pods after)) as Hbad.
  { unfold bad_name_pods.
    rewrite !list.filter_app /= (filter_cons_False
      (λ pod0, ¬ pod_has_int32_member_key set pod0) pod
      (living_pods after) ltac:(intros Hnot; exact (Hnot Hmember))).
    done. }
  unfold match_distance, pod_distance.
  rewrite Hliving_old Hliving_new.
  rewrite Hmissing Hold_outdated Hnew_outdated Hcondemned Hbad.
  rewrite !app_length /=. lia.
Qed.

Lemma pods_progress_observed_mark_deleting before pod after pod' :
  PodV.key pod = PodV.key pod' →
  pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None →
  pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None →
  pods_progress_observed
    (before ++ pod :: after) (before ++ pod' :: after).
Proof.
  intros Hkey Hold_deletion Hnew_deletion.
  right. left. exists pod, pod'. split_and!.
  - apply elem_of_app. right. by left.
  - apply elem_of_app. right. by left.
  - exact Hkey.
  - intros Hmeta.
    apply (f_equal ObjectMetaV.DeletionTimestamp') in Hmeta.
    simpl in Hmeta. rewrite Hold_deletion in Hmeta.
    apply Hnew_deletion. symmetry. exact Hmeta.
Qed.

Lemma pods_progress_observed_remove before pod after :
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  pods_progress_observed (before ++ pod :: after) (before ++ after).
Proof.
  intros Hnodup. left. intros Hsets.
  assert (PodV.key pod ∈
      list_to_set (C:=gset KKey.t)
        (PodV.key <$> (before ++ pod :: after))) as Hin.
  { apply elem_of_list_to_set. rewrite fmap_app /=.
    apply elem_of_app. right. by left. }
  rewrite Hsets elem_of_list_to_set fmap_app in Hin.
  rewrite fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as (_ & Hdisjoint & Htail_nodup).
  simpl in Htail_nodup. inversion Htail_nodup as [|? ? Hnot_after _].
  apply elem_of_app in Hin as [Hbefore|Hafter].
  - apply (Hdisjoint (PodV.key pod) Hbefore). by left.
  - exact (Hnot_after Hafter).
Qed.

Lemma pods_progress_observed_mark_deleting_local local_pod stored_pod pod'
    local_pods before after idx :
  local_pods !! idx = Some local_pod →
  local_pod_matches_stored local_pod stored_pod →
  PodV.key stored_pod = PodV.key pod' →
  stored_pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None →
  pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None →
  pods_progress_observed local_pods (before ++ pod' :: after).
Proof.
  intros Hlocal_lookup Hlocal_stored Hstored_key Hstored_alive Hpod_not_alive.
  right. left. unfold pod_meta_except_resource_version_changed.
  exists local_pod, pod'. split_and!.
  - by apply list_elem_of_lookup_2 in Hlocal_lookup.
  - apply elem_of_app. right. by left.
  - etrans; first exact (proj1 Hlocal_stored). exact Hstored_key.
  - intros Hmeta.
    pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hmeta) as Hdeletion.
    simpl in Hdeletion.
    apply Hpod_not_alive. rewrite -Hdeletion.
    rewrite (proj1 (proj2 (proj2 Hlocal_stored))). exact Hstored_alive.
Qed.

Lemma pods_progress_observed_remove_local local_pods stored_pods
    before pod after :
  local_pods_match_stored local_pods stored_pods →
  stored_pods = before ++ pod :: after →
  NoDup (PodV.key <$> stored_pods) →
  pods_progress_observed local_pods (before ++ after).
Proof.
  intros Hlocal_stored Hstored_decomp Hnodup.
  left. rewrite (local_pods_match_stored_keys _ _ Hlocal_stored)
    Hstored_decomp.
  intros Hsets.
  assert (PodV.key pod ∈
      list_to_set (C:=gset KKey.t)
        (PodV.key <$> (before ++ pod :: after))) as Hin.
  { apply elem_of_list_to_set. rewrite fmap_app /=.
    apply elem_of_app. right. by left. }
  rewrite Hsets elem_of_list_to_set fmap_app in Hin.
  rewrite Hstored_decomp fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as (_ & Hdisjoint & Htail_nodup).
  simpl in Htail_nodup. inversion Htail_nodup as [|? ? Hnot_after _].
  apply elem_of_app in Hin as [Hbefore|Hafter].
  - apply (Hdisjoint (PodV.key pod) Hbefore). by left.
  - exact (Hnot_after Hafter).
Qed.

Lemma desired_pod_keys_nodup set : NoDup (desired_pod_keys set).
Proof.
  unfold desired_pod_keys, desired_ordinals.
  apply NoDup_fmap_2.
  - intros ordinal1 ordinal2 Hkey.
    apply (f_equal KKey.Name') in Hkey. simpl in Hkey.
    by apply desired_pod_name_inj in Hkey.
  - apply NoDup_seq.
Qed.

Lemma missing_pvc_key_set_subset_reserved set pvc_map reserved :
  (∀ key claim, pvc_map !! key = Some claim → PersistentVolumeClaimV.key claim = key) →
  (∀ key, key ∈ list_to_set (C:=gset KKey.t) (desired_pvc_keys set) →
    key ∈ dom pvc_map ∨ key ∈ reserved) →
  list_to_set (C:=gset KKey.t) (missing_pvc_keys set (pvc_list_of_map pvc_map)) ⊆
    list_to_set reserved.
Proof.
  intros Hwf Hcoverage key Hmissing.
  rewrite elem_of_list_to_set in Hmissing |- *.
  unfold missing_pvc_keys in Hmissing.
  apply list_elem_of_filter in Hmissing as [Hnotin Hdesired].
  specialize (Hcoverage key ltac:(by rewrite elem_of_list_to_set)).
  destruct Hcoverage as [Hdom|Hreserved]; last by apply elem_of_list_to_set.
  exfalso. apply Hnotin.
  rewrite -(elem_of_list_to_set (C:=gset KKey.t))
    (pvc_list_of_map_key_set pvc_map Hwf).
  exact Hdom.
Qed.

Lemma own_reserved_pvcs_finish γ set pvc_map reserved :
  (∀ key claim, pvc_map !! key = Some claim → PersistentVolumeClaimV.key claim = key) →
  NoDup reserved →
  (∀ key, key ∈ list_to_set (C:=gset KKey.t) (desired_pvc_keys set) →
    key ∈ dom pvc_map ∨ key ∈ reserved) →
  ([∗ list] key ∈ reserved, own_available_frag γ key) -∗
  own_missing_pvc_reservations γ set (pvc_list_of_map pvc_map).
Proof.
  intros Hwf Hnodup Hcoverage. iIntros "Hreserved".
  rewrite /own_missing_pvc_reservations.
  iEval (rewrite -(big_sepS_list_to_set _ _ Hnodup)) in "Hreserved".
  iApply (big_sepS_subseteq with "Hreserved").
  by apply missing_pvc_key_set_subset_reserved.
Qed.

Lemma missing_pod_key_set_fmap_eq sts pods pods' :
  PodV.key <$> pods = PodV.key <$> pods' →
  list_to_set (C:=gset KKey.t) (missing_pod_keys sts pods) =
    list_to_set (missing_pod_keys sts pods').
Proof. intros Hkeys. unfold missing_pod_keys. by rewrite Hkeys. Qed.

Lemma missing_pod_key_set_snoc sts pods pod :
  PodV.key pod ∈ desired_pod_keys sts →
  PodV.key pod ∉ PodV.key <$> pods →
  list_to_set (C:=gset KKey.t) (missing_pod_keys sts (pods ++ [pod])) =
    list_to_set (missing_pod_keys sts pods) ∖ {[PodV.key pod]}.
Proof.
  intros Hdesired Hfresh. apply set_eq. intros key.
  rewrite elem_of_difference elem_of_singleton !elem_of_list_to_set.
  unfold missing_pod_keys. rewrite !list_elem_of_filter fmap_app /=.
  split.
  - intros [Hnotin Hkey]. split.
    + split; last exact Hkey. intros Hin. apply Hnotin. apply elem_of_app. by left.
    + intros ->. apply Hnotin. apply elem_of_app. right. by left.
  - intros [[Hnotin Hkey] Hneq]. split; last exact Hkey.
    intros Hin. apply elem_of_app in Hin as [Hin|Hin]; first by apply Hnotin.
    apply list_elem_of_singleton in Hin. by apply Hneq.
Qed.

Lemma own_available_missing_to_missing γ set pods :
  ([∗ set] key ∈ list_to_set (C:=gset KKey.t) (missing_pod_keys set pods),
    own_available_frag γ key) -∗
  own_missing_pod_reservations γ set pods.
Proof.
  iIntros "Havailable". rewrite /own_missing_pod_reservations.
  iApply (big_sepS_mono with "Havailable"). iIntros (key Hkey) "Hkey". by iLeft.
Qed.

Lemma pod_names_nodup_of_key_nodup set pods :
  Forall (pod_has_int32_member_key set) pods →
  NoDup (PodV.key <$> pods) →
  NoDup
    ((λ pod, pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <$> pods).
Proof.
  intros Hmembers Hkeys.
  induction pods as [|pod pods IH]; simpl; first constructor.
  inversion Hmembers as [|? ? Hmember Hmembers']; subst.
  inversion Hkeys as [|? ? Hkey_notin Hkeys']; subst.
  constructor.
  - intros Hname_in.
    apply list_elem_of_fmap_1 in Hname_in as
      (pod' & Hname & Hpod_in).
    rewrite Forall_forall in Hmembers'.
    pose proof (Hmembers' pod' ltac:(by rewrite -list_elem_of_In))
      as Hmember'.
    apply Hkey_notin.
    assert (PodV.key pod = PodV.key pod') as Hkey.
    { destruct Hmember as (Hnamespace & _).
      destruct Hmember' as (Hnamespace' & _).
      unfold PodV.key, PodV.meta_key. simpl.
      rewrite Hnamespace Hnamespace' Hname. done. }
    rewrite Hkey. apply list_elem_of_fmap_2. exact Hpod_in.
  - by apply IH.
Qed.

Lemma desired_objects_reconciled_distance_zero set pods pvcs :
  Forall (pod_has_int32_member_key set) pods →
  Forall (λ pod, ¬ pod_is_condemned set pod) pods →
  Forall (λ pod, ¬ pod_is_outdated set pod) pods →
  desired_objects_reconciled set pods pvcs →
  match_distance set pods pvcs = 0%nat.
Proof.
  intros Hmembers Hno_condemned Hno_outdated
    (Hmissing_pods & Hmissing_pvcs & Hdesired).
  assert (bad_name_pods set pods = []) as Hbad.
  { unfold bad_name_pods. apply filter_none. intros pod Hpod Hbad.
    rewrite Forall_forall in Hmembers.
    exact (Hbad (Hmembers pod ltac:(by rewrite -list_elem_of_In))). }
  assert (condemned_pods set pods = []) as Hcondemned.
  { unfold condemned_pods. apply filter_none.
    intros pod Hpod (Hmember & Hnot_desired).
    rewrite Forall_forall in Hno_condemned.
    apply (Hno_condemned pod ltac:(by rewrite -list_elem_of_In)).
    apply (proj2 (pod_int32_member_condemned_iff set pod Hmember)).
    exact Hnot_desired. }
  assert (outdated_pods set pods = []) as Houtdated.
  { unfold outdated_pods, needed_pods. apply filter_none.
    intros pod Hpod.
    apply list_elem_of_filter in Hpod as (Hdesired_key & Hpod).
    rewrite Forall_forall in Hmembers.
    rewrite Forall_forall in Hno_outdated.
    rewrite Forall_forall in Hdesired.
    intros Hnot_match.
    assert (In pod pods) as Hpod_in by
      (rewrite -list_elem_of_In; exact Hpod).
    pose proof (Hdesired pod Hpod_in Hdesired_key) as (_ & Hidentity).
    apply (Hno_outdated pod Hpod_in).
    apply (proj2 (pod_int32_member_outdated_iff set pod
      (Hmembers pod Hpod_in))).
    split; first exact Hdesired_key.
    intros Himmutable. apply Hnot_match. split; done. }
  assert (living_pods pods = pods) as Hliving.
  { unfold living_pods. apply filter_all. intros pod Hpod.
    rewrite Forall_forall in Hmembers.
    rewrite Forall_forall in Hno_condemned.
    rewrite Forall_forall in Hdesired.
    assert (pod_key_is_desired set (PodV.key pod)) as Hpod_desired.
    { destruct (decide (pod_key_is_desired set (PodV.key pod))) as
        [Hpod_desired|Hnot_desired]; first done.
      exfalso. apply (Hno_condemned pod ltac:(by rewrite -list_elem_of_In)).
      apply (proj2 (pod_int32_member_condemned_iff set pod
        (Hmembers pod ltac:(by rewrite -list_elem_of_In)))).
      exact Hnot_desired. }
    exact (proj1 (Hdesired pod ltac:(by rewrite -list_elem_of_In)
      Hpod_desired)). }
  unfold match_distance, pod_distance, pvc_distance.
  rewrite Hliving.
  rewrite Hmissing_pods Hmissing_pvcs Hbad Hcondemned Houtdated /=.
  done.
Qed.

Lemma match_distance_remove_condemned set before pod after pvcs :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  pod_is_condemned set pod →
  is_pod_alive pod →
  match_distance set (before ++ after) pvcs <
    match_distance set (before ++ pod :: after) pvcs.
Proof.
  intros Hmembers Hcondemned Halive.
  assert (pod_has_int32_member_key set pod) as Hmember.
  { rewrite Forall_forall in Hmembers. apply Hmembers.
    apply list_elem_of_In. apply elem_of_app. right. by left. }
  assert (¬ pod_key_is_desired set (PodV.key pod)) as Hnot_desired.
  { apply (proj1 (pod_int32_member_condemned_iff set pod Hmember)).
    exact Hcondemned. }
  assert (living_pods (before ++ pod :: after) =
      living_pods before ++ pod :: living_pods after) as Hliving_old.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_True is_pod_alive pod after Halive). done. }
  assert (living_pods (before ++ after) =
      living_pods before ++ living_pods after) as Hliving_new.
  { unfold living_pods. by rewrite list.filter_app. }
  assert (missing_pod_keys set
      (living_pods before ++ living_pods after) =
      missing_pod_keys set
        (living_pods before ++ pod :: living_pods after)) as Hmissing.
  { unfold missing_pod_keys. rewrite !fmap_app /=.
    apply filter_not_elem_add_irrelevant. exact Hnot_desired. }
  assert (outdated_pods set
      (living_pods before ++ living_pods after) =
      outdated_pods set
        (living_pods before ++ pod :: living_pods after)) as Houtdated.
  { unfold outdated_pods, needed_pods.
    rewrite !list.filter_app /=
      (filter_cons_False _ pod (living_pods after) Hnot_desired). done. }
  assert (bad_name_pods set
      (living_pods before ++ living_pods after) =
      bad_name_pods set
        (living_pods before ++ pod :: living_pods after)) as Hbad.
  { unfold bad_name_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_False
      (λ pod0, ¬ pod_has_int32_member_key set pod0) pod
      (living_pods after)
      ltac:(intros Hnot; exact (Hnot Hmember))). done. }
  assert (length (condemned_pods set
      (living_pods before ++ pod :: living_pods after)) =
      S (length (condemned_pods set
        (living_pods before ++ living_pods after)))) as Hcondemned_distance.
  { assert (condemned_pods set
        (living_pods before ++ pod :: living_pods after) =
        condemned_pods set (living_pods before) ++
          pod :: condemned_pods set (living_pods after)) as Hold.
    { unfold condemned_pods. rewrite list.filter_app.
      rewrite (filter_cons_True
        (λ pod0, pod_has_int32_member_key set pod0 ∧
          ¬ pod_key_is_desired set (PodV.key pod0))
        pod (living_pods after) ltac:(split; done)). done. }
    assert (condemned_pods set
        (living_pods before ++ living_pods after) =
        condemned_pods set (living_pods before) ++
          condemned_pods set (living_pods after)) as Hnew.
    { unfold condemned_pods. by rewrite list.filter_app. }
    rewrite Hold Hnew.
    rewrite !app_length /=. lia. }
  unfold match_distance, pod_distance.
  rewrite Hliving_old Hliving_new.
  rewrite Hmissing Houtdated Hbad Hcondemned_distance.
  lia.
Qed.

Lemma match_distance_remove_outdated set before pod after pvcs :
  Forall (pod_has_int32_member_key set) (before ++ pod :: after) →
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  pod_is_outdated set pod →
  is_pod_alive pod →
  match_distance set (before ++ after) pvcs <
    match_distance set (before ++ pod :: after) pvcs.
Proof.
  intros Hmembers Hnodup Houtdated_pod Halive.
  assert (pod_has_int32_member_key set pod) as Hmember.
  { rewrite Forall_forall in Hmembers. apply Hmembers.
    apply list_elem_of_In. apply elem_of_app. right. by left. }
  pose proof (proj1
    (pod_int32_member_outdated_iff set pod Hmember) Houtdated_pod)
    as [Hdesired Hnot_immutable].
  assert (¬ pod_match set pod) as Hnot_match.
  { intros [_ Himmutable]. exact (Hnot_immutable Himmutable). }
  rewrite fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as
    (Hbefore_nodup & Hdisjoint & Htail_nodup).
  inversion Htail_nodup as [|? ? Hnot_after Hafter_nodup].
  assert (PodV.key pod ∉ PodV.key <$> before) as Hnot_before.
  { intros Hin. apply (Hdisjoint (PodV.key pod) Hin). by left. }
  assert (PodV.key pod ∉ PodV.key <$> living_pods before)
    as Hnot_before_living.
  { intros Hin. apply Hnot_before.
    apply list_elem_of_fmap_1 in Hin as (pod0 & -> & Hin).
    apply list_elem_of_fmap_2. unfold living_pods in Hin.
    by apply list_elem_of_filter in Hin as [_ Hin]. }
  assert (PodV.key pod ∉ PodV.key <$> living_pods after)
    as Hnot_after_living.
  { intros Hin. apply Hnot_after.
    apply list_elem_of_fmap_1 in Hin as (pod0 & -> & Hin).
    apply list_elem_of_fmap_2. unfold living_pods in Hin.
    by apply list_elem_of_filter in Hin as [_ Hin]. }
  assert (living_pods (before ++ pod :: after) =
      living_pods before ++ pod :: living_pods after) as Hliving_old.
  { unfold living_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_True is_pod_alive pod after Halive). done. }
  assert (living_pods (before ++ after) =
      living_pods before ++ living_pods after) as Hliving_new.
  { unfold living_pods. by rewrite list.filter_app. }
  assert (length (missing_pod_keys set
      (living_pods before ++ living_pods after)) =
      S (length (missing_pod_keys set
        (living_pods before ++ pod :: living_pods after)))) as Hmissing.
  { unfold missing_pod_keys. rewrite !fmap_app /=.
    apply filter_not_elem_remove_unique.
    - apply desired_pod_keys_nodup.
    - exact Hdesired.
    - exact Hnot_before_living.
    - exact Hnot_after_living. }
  assert (length (outdated_pods set
      (living_pods before ++ pod :: living_pods after)) =
      S (length (outdated_pods set
        (living_pods before ++ living_pods after)))) as Houtdated.
  { assert (outdated_pods set
        (living_pods before ++ pod :: living_pods after) =
        outdated_pods set (living_pods before) ++
          pod :: outdated_pods set (living_pods after)) as Hold.
    { unfold outdated_pods, needed_pods.
      rewrite list.filter_app /=
        (filter_cons_True _ pod (living_pods after) Hdesired).
      rewrite list.filter_app /=
        (filter_cons_True
          (λ pod0, ¬ pod_match set pod0) pod
          (filter (λ pod0, pod_key_is_desired set (PodV.key pod0))
            (living_pods after))
          Hnot_match). done. }
    assert (outdated_pods set
        (living_pods before ++ living_pods after) =
        outdated_pods set (living_pods before) ++
          outdated_pods set (living_pods after)) as Hnew.
    { unfold outdated_pods, needed_pods.
      by rewrite !list.filter_app. }
    rewrite Hold Hnew.
    rewrite !app_length /=. lia. }
  assert (condemned_pods set
      (living_pods before ++ living_pods after) =
      condemned_pods set
        (living_pods before ++ pod :: living_pods after)) as Hcondemned.
  { unfold condemned_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_False
      (λ pod0, pod_has_int32_member_key set pod0 ∧
        ¬ pod_key_is_desired set (PodV.key pod0)) pod
      (living_pods after)
      ltac:(intros [_ Hnot]; exact (Hnot Hdesired))). done. }
  assert (bad_name_pods set
      (living_pods before ++ living_pods after) =
      bad_name_pods set
        (living_pods before ++ pod :: living_pods after)) as Hbad.
  { unfold bad_name_pods. rewrite !list.filter_app /=.
    rewrite (filter_cons_False
      (λ pod0, ¬ pod_has_int32_member_key set pod0) pod
      (living_pods after)
      ltac:(intros Hnot; exact (Hnot Hmember))). done. }
  unfold match_distance, pod_distance.
  rewrite Hliving_old Hliving_new.
  rewrite Hmissing Houtdated Hcondemned Hbad. lia.
Qed.

Lemma desired_objects_reconciled_mark_condemned set before pod after pod' pvcs :
  desired_objects_reconciled set (before ++ pod :: after) pvcs →
  pod_has_int32_member_key set pod →
  pod_is_condemned set pod →
  PodV.key pod = PodV.key pod' →
  desired_objects_reconciled set (before ++ pod' :: after) pvcs.
Proof.
  intros (Hmissing_pods & Hmissing_pvcs & Hdesired)
    Hmember Hcondemned Hkey.
  split_and!.
  - unfold missing_pod_keys in Hmissing_pods |- *.
    rewrite !fmap_app /= in Hmissing_pods.
    rewrite !fmap_app /= -Hkey.
    exact Hmissing_pods.
  - exact Hmissing_pvcs.
  - apply Forall_forall. intros other Hother.
    rewrite Forall_forall in Hdesired.
    rewrite -list_elem_of_In in Hother.
    apply elem_of_app in Hother as [Hbefore|Htail].
    + apply Hdesired. rewrite -list_elem_of_In.
      apply elem_of_app. left. exact Hbefore.
    + apply elem_of_cons in Htail as [->|Hafter].
      * intros Hnew_desired.
        exfalso.
        apply (proj1
          (pod_int32_member_condemned_iff set pod Hmember)
          Hcondemned).
        rewrite Hkey. exact Hnew_desired.
      * apply Hdesired. rewrite -list_elem_of_In.
        apply elem_of_app. right. apply elem_of_cons. right. exact Hafter.
Qed.

Lemma desired_objects_reconciled_remove_condemned set before pod after pvcs :
  desired_objects_reconciled set (before ++ pod :: after) pvcs →
  pod_has_int32_member_key set pod →
  pod_is_condemned set pod →
  desired_objects_reconciled set (before ++ after) pvcs.
Proof.
  intros (Hmissing_pods & Hmissing_pvcs & Hdesired)
    Hmember Hcondemned.
  pose proof (proj1
    (pod_int32_member_condemned_iff set pod Hmember) Hcondemned)
    as Hnot_desired.
  split_and!.
  - unfold missing_pod_keys in Hmissing_pods |- *.
    rewrite !fmap_app /= in Hmissing_pods |- *.
    rewrite (filter_not_elem_add_irrelevant
      (desired_pod_keys set) (PodV.key <$> before)
      (PodV.key <$> after) (PodV.key pod) Hnot_desired).
    exact Hmissing_pods.
  - exact Hmissing_pvcs.
  - apply Forall_forall. intros other Hother.
    rewrite Forall_forall in Hdesired.
    rewrite -list_elem_of_In in Hother.
    apply elem_of_app in Hother as [Hbefore|Hafter].
    + apply Hdesired. rewrite -list_elem_of_In.
      apply elem_of_app. left. exact Hbefore.
    + apply Hdesired. rewrite -list_elem_of_In.
      apply elem_of_app. right. apply elem_of_cons. right. exact Hafter.
Qed.

Lemma desired_objects_reconciled_remove_desired_missing_pod_keys
    set before pod after pvcs :
  desired_objects_reconciled set (before ++ pod :: after) pvcs →
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  PodV.key pod ∈ desired_pod_keys set →
  list_to_set (C:=gset KKey.t) (missing_pod_keys set (before ++ after)) =
    {[PodV.key pod]}.
Proof.
  intros (Hmissing & _ & _) Hnodup Hdesired.
  apply set_eq. intros key.
  rewrite elem_of_list_to_set elem_of_singleton.
  unfold missing_pod_keys in Hmissing |- *.
  rewrite list_elem_of_filter.
  split.
  - intros [Hnotin Hkey_desired].
    destruct (decide (key = PodV.key pod)); first done.
    exfalso. apply Hnotin.
    assert (key ∈ PodV.key <$> (before ++ pod :: after)) as Hall.
    { destruct (decide (key ∈ PodV.key <$> (before ++ pod :: after))); first done.
      assert (key ∈ filter (λ key0, key0 ∉ PodV.key <$> (before ++ pod :: after))
        (desired_pod_keys set)) as Hmissing_key.
      { apply list_elem_of_filter. done. }
      rewrite Hmissing in Hmissing_key. inversion Hmissing_key. }
    rewrite !fmap_app /= in Hall Hnotin.
    apply elem_of_app in Hall as [Hbefore|Htail].
    + rewrite fmap_app. apply elem_of_app. by left.
    + apply elem_of_cons in Htail as [Heq|Hafter].
      * contradiction.
      * rewrite fmap_app. apply elem_of_app. by right.
  - intros ->. split; last exact Hdesired.
    rewrite !fmap_app /= in Hnodup |- *.
    apply list.NoDup_app in Hnodup as (_ & Hdisjoint & Htail_nodup).
    apply list.NoDup_cons in Htail_nodup as (Hnot_after & _).
    intros Hin. apply elem_of_app in Hin as [Hbefore|Hafter].
    + apply (Hdisjoint (PodV.key pod) Hbefore). by left.
    + exact (Hnot_after Hafter).
Qed.

Lemma list_to_set_pod_keys_remove before pod after :
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  list_to_set (C:=gset KKey.t) (PodV.key <$> (before ++ after)) =
    list_to_set (C:=gset KKey.t)
      (PodV.key <$> (before ++ pod :: after)) ∖ {[PodV.key pod]}.
Proof.
  intros Hnodup.
  assert (PodV.key pod ∉ PodV.key <$> (before ++ after)) as Hnotin.
  { rewrite fmap_app /= in Hnodup.
    apply list.NoDup_app in Hnodup as (_ & Hdisjoint & Htail_nodup).
    inversion Htail_nodup as [|? ? Hnot_after _].
    rewrite fmap_app. intros Hin.
    apply elem_of_app in Hin as [Hbefore|Hafter].
    - apply (Hdisjoint (PodV.key pod) Hbefore). by left.
    - exact (Hnot_after Hafter). }
  apply set_eq. intros key.
  rewrite elem_of_difference !elem_of_list_to_set elem_of_singleton.
  split.
  - intros Hin. split.
    + rewrite !fmap_app /= in Hin |- *.
      apply elem_of_app in Hin as [Hbefore|Hafter].
      * apply elem_of_app. left. exact Hbefore.
      * apply elem_of_app. right. apply elem_of_cons. right. exact Hafter.
    + intros ->. exact (Hnotin Hin).
  - intros [Hin Hneq].
    rewrite !fmap_app /= in Hin |- *.
    apply elem_of_app in Hin as [Hbefore|Htail].
    + apply elem_of_app. left. exact Hbefore.
    + apply elem_of_cons in Htail as [Heq|Hafter].
      * exfalso. exact (Hneq Heq).
      * apply elem_of_app. right. exact Hafter.
Qed.

Lemma pod_keys_nodup_remove before pod after :
  NoDup (PodV.key <$> (before ++ pod :: after)) →
  NoDup (PodV.key <$> (before ++ after)).
Proof.
  intros Hnodup. rewrite !fmap_app /= in Hnodup |- *.
  apply list.NoDup_app in Hnodup as
    (Hbefore_nodup & Hbefore_disjoint & Htail_nodup).
  apply list.NoDup_cons in Htail_nodup as (_ & Hafter_nodup).
  apply list.NoDup_app. split_and!; try done.
  intros key Hbefore Hafter.
  apply (Hbefore_disjoint key Hbefore). by right.
Qed.

Definition progress_or_complete sts pods pvcs pods' pvcs' : Prop :=
  current_state_matches sts pods' pvcs' ∨
  pods_progress_observed pods pods' ∧
  match_distance sts pods' pvcs' < match_distance sts pods pvcs.

Lemma reconcile_loop_ordinal_lt (ordinal end_ordinal : w64) replicas :
  0 ≤ sint.Z ordinal →
  sint.Z ordinal ≤ sint.Z end_ordinal →
  sint.Z end_ordinal = Z.of_nat replicas - 1 →
  (sint.nat ordinal < replicas)%nat.
Proof. word. Qed.

Lemma reconcile_loop_ordinal_int32 (ordinal : w64) replicas :
  (sint.nat ordinal < replicas)%nat →
  (replicas ≤ go_int32_max_nat)%nat →
  (sint.nat ordinal ≤ go_int32_max_nat)%nat.
Proof. lia. Qed.

Lemma valid_dns1123_label_length_le_go_int_max name :
  valid_dns1123_label name →
  Z.of_nat (length name) ≤ go_int_max.
Proof.
  intros [_ Hlength]. unfold go_int_max. lia.
Qed.

Lemma reconcile_loop_ordinal_next (ordinal : w64) replicas :
  0 ≤ sint.Z ordinal →
  (sint.nat ordinal < replicas)%nat →
  (replicas ≤ go_int32_max_nat)%nat →
  0 ≤ sint.Z (word.add ordinal (W64 1)) ∧
  sint.Z (word.add ordinal (W64 1)) ≤ Z.of_nat replicas ∧
  sint.nat (word.add ordinal (W64 1)) = S (sint.nat ordinal).
Proof.
  intros Hordinal_nonnegative Hordinal_lt Hreplicas_bound.
  pose proof (proj1 (Nat2Z.inj_lt (sint.nat ordinal) replicas)
    Hordinal_lt) as Hordinal_lt_Z.
  rewrite Z2Nat.id in Hordinal_lt_Z.
  1: exact Hordinal_nonnegative.
  pose proof (proj1 (Nat2Z.inj_le replicas go_int32_max_nat)
    Hreplicas_bound) as Hreplicas_bound_Z.
  unfold go_int32_max_nat in Hreplicas_bound_Z.
  rewrite Z2Nat.id in Hreplicas_bound_Z.
  1: { unfold go_int32_max. lia. }
  assert (sint.Z (word.add ordinal (W64 1)) = sint.Z ordinal + 1)
    as Hnext_Z.
  { rewrite word.signed_add /=.
    apply swrap_small. unfold go_int32_max in Hreplicas_bound_Z. lia. }
  rewrite Hnext_Z.
  split_and!; lia.
Qed.

Lemma desired_prefix_reconciled_step set next pods idx pod pod'
    pvc_map pvc_map' :
  desired_prefix_reconciled set next pods pvc_map →
  pods !! idx = Some pod →
  NoDup (PodV.key <$> pods) →
  PodV.key pod = desired_pod_key set next →
  PodV.key pod' = PodV.key pod →
  is_pod_alive pod' →
  pod_identity_matches set pod' →
  dom pvc_map ⊆ dom pvc_map' →
  (∀ name,
    name ∈ dom
      (persistent_volume_claim_templates_by_name
        (StatefulSetSpecV.volume_claim_templates_list
          set.(StatefulSetV.Spec'))) →
    desired_pvc_key set name next ∈ dom pvc_map') →
  desired_prefix_reconciled set (S next)
    (<[idx:=pod']> pods) pvc_map'.
Proof.
  intros Hprefix Hlookup _ Hpod_key Hpod'_key Halive Hidentity
    Hdom Hpvc.
  intros ordinal Hordinal_next Hordinal_replicas.
  assert (Hordinal_le : (ordinal ≤ next)%nat) by lia.
  destruct (proj1 (Nat.lt_eq_cases ordinal next) Hordinal_le) as
    [Hordinal_lt|Hordinal_eq].
  - destruct (Hprefix ordinal Hordinal_lt Hordinal_replicas) as
        [[old_pod [Hold_in [Hold_key [Hold_alive Hold_identity]]]]
         Hold_pvcs].
    split.
    + exists old_pod.
      split_and!; try done.
      apply list_elem_of_lookup_1 in Hold_in as [old_idx Hold_lookup].
      assert (idx ≠ old_idx) as Hindices_ne.
      { intros ->.
        rewrite Hlookup in Hold_lookup.
        injection Hold_lookup as ->.
        assert (ordinal = next) as ->.
        { eapply desired_pod_key_inj.
          trans (PodV.key old_pod); [symmetry; exact Hold_key|exact Hpod_key]. }
        lia. }
      apply (list_elem_of_lookup_2 (<[idx:=pod']> pods) old_idx old_pod).
      rewrite list_lookup_insert_ne; done.
    + intros name Hname.
      apply Hdom, Hold_pvcs, Hname.
  - subst ordinal.
    split.
    + exists pod'.
      split.
      { apply list_elem_of_insert.
        eapply lookup_lt_Some, Hlookup. }
      split.
      { rewrite Hpod'_key Hpod_key. done. }
      done.
    + exact Hpvc.
Qed.

Lemma pvc_distance_map_mono set pvc_map pvc_map' :
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  (∀ key claim, pvc_map' !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  dom pvc_map ⊆ dom pvc_map' →
  pvc_distance set (pvc_list_of_map pvc_map') ≤
    pvc_distance set (pvc_list_of_map pvc_map).
Proof.
  intros Hwf Hwf' Hdom.
  unfold pvc_distance, missing_pvc_keys.
  pose proof (pvc_list_of_map_key_set pvc_map Hwf) as Hkeys.
  pose proof (pvc_list_of_map_key_set pvc_map' Hwf') as Hkeys'.
  induction (desired_pvc_keys set) as [|key keys IH]; simpl; first lia.
  rewrite !filter_cons.
  destruct (decide
      (key ∉ PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map'))
    as [Hmissing'|Hpresent'];
    destruct (decide
      (key ∉ PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map))
    as [Hmissing|Hpresent]; simpl.
  - lia.
  - exfalso. apply Hmissing'.
    assert (key ∈ PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map)
      as Hpresent0.
    { destruct (decide (key ∈
        PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map)); done. }
    assert (key ∈ dom pvc_map) as Hkey.
    { rewrite -Hkeys elem_of_list_to_set. exact Hpresent0. }
    assert (key ∈ dom pvc_map') as Hkey'.
    { apply Hdom. exact Hkey. }
    rewrite -Hkeys' elem_of_list_to_set in Hkey'. exact Hkey'.
  - lia.
  - lia.
Qed.

Lemma filter2_cons {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} x xs :
  filter Q (filter P (x :: xs)) =
    if decide (P x ∧ Q x)
    then x :: filter Q (filter P xs)
    else filter Q (filter P xs).
Proof.
  destruct (decide (P x)) as [HP|HP].
  - rewrite (filter_cons_True P x xs HP).
    destruct (decide (Q x)) as [HQ|HQ].
    + rewrite (filter_cons_True Q x (filter P xs) HQ).
      case_decide; [done|tauto].
    + rewrite (filter_cons_False Q x (filter P xs) HQ).
      case_decide; [tauto|done].
  - rewrite (filter_cons_False P x xs HP).
    case_decide; [tauto|done].
Qed.

Lemma filter_replace_length_eq {A} (P : A → Prop)
    `{∀ x, Decision (P x)} before after x y :
  (P y ↔ P x) →
  length (filter P (before ++ y :: after)) =
    length (filter P (before ++ x :: after)).
Proof.
  intros Hiff. induction before as [|b before IH]; simpl.
  - rewrite !filter_cons.
    destruct (decide (P y)) as [Hy|Hy];
      destruct (decide (P x)) as [Hx|Hx]; simpl; try lia;
      exfalso.
    + apply Hx, (proj1 Hiff), Hy.
    + apply Hy, (proj2 Hiff), Hx.
  - rewrite !filter_cons.
    destruct (decide (P b)); simpl; lia.
Qed.

Lemma filter3_cons {A} (P Q R : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    `{∀ x, Decision (R x)} x xs :
  filter R (filter Q (filter P (x :: xs))) =
    if decide (P x ∧ Q x ∧ R x)
    then x :: filter R (filter Q (filter P xs))
    else filter R (filter Q (filter P xs)).
Proof.
  destruct (decide (P x)) as [HP|HP].
  - rewrite (filter_cons_True P x xs HP).
    destruct (decide (Q x)) as [HQ|HQ].
    + rewrite (filter_cons_True Q x (filter P xs) HQ).
      destruct (decide (R x)) as [HR|HR].
      * rewrite (filter_cons_True R x (filter Q (filter P xs)) HR).
        case_decide; [done|tauto].
      * rewrite (filter_cons_False R x (filter Q (filter P xs)) HR).
        case_decide; [tauto|done].
    + rewrite (filter_cons_False Q x (filter P xs) HQ).
      case_decide; [tauto|done].
  - rewrite (filter_cons_False P x xs HP).
    case_decide; [tauto|done].
Qed.

Lemma filter2_replace_length_eq {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} before after x y :
  (P y ∧ Q y ↔ P x ∧ Q x) →
  length (filter Q (filter P (before ++ y :: after))) =
    length (filter Q (filter P (before ++ x :: after))).
Proof.
  intros Hiff.
  induction before as [|b before IH]; simpl.
  - rewrite (filter2_cons P Q y after) (filter2_cons P Q x after).
    destruct (decide (P y ∧ Q y)) as [Hy|Hy];
      destruct (decide (P x ∧ Q x)) as [Hx|Hx]; simpl; try lia;
      exfalso.
    + apply Hx. apply (proj1 Hiff). exact Hy.
    + apply Hy. apply (proj2 Hiff). exact Hx.
  - rewrite (filter2_cons P Q b (before ++ y :: after)).
    rewrite (filter2_cons P Q b (before ++ x :: after)).
    destruct (decide (P b ∧ Q b)); simpl; lia.
Qed.

Lemma filter2_replace_length_le {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} before after x y :
  (P y ∧ Q y → P x ∧ Q x) →
  length (filter Q (filter P (before ++ y :: after))) ≤
    length (filter Q (filter P (before ++ x :: after))).
Proof.
  intros Himp.
  induction before as [|b before IH]; simpl.
  - rewrite (filter2_cons P Q y after)
      (filter2_cons P Q x after).
    destruct (decide (P y ∧ Q y)) as [Hy|Hy];
      destruct (decide (P x ∧ Q x)) as [Hx|Hx]; simpl; try lia.
    exfalso. apply Hx, Himp, Hy.
  - rewrite (filter2_cons P Q b (before ++ y :: after)).
    rewrite (filter2_cons P Q b (before ++ x :: after)).
    destruct (decide (P b ∧ Q b)); simpl; lia.
Qed.

Lemma filter3_replace_length_le {A} (P Q R : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    `{∀ x, Decision (R x)} before after x y :
  (P y ∧ Q y ∧ R y → P x ∧ Q x ∧ R x) →
  length (filter R (filter Q (filter P (before ++ y :: after)))) ≤
    length (filter R (filter Q (filter P (before ++ x :: after)))).
Proof.
  intros Himp.
  induction before as [|b before IH]; simpl.
  - rewrite (filter3_cons P Q R y after)
      (filter3_cons P Q R x after).
    destruct (decide (P y ∧ Q y ∧ R y)) as [Hy|Hy];
      destruct (decide (P x ∧ Q x ∧ R x)) as [Hx|Hx]; simpl; try lia.
    exfalso. apply Hx, Himp, Hy.
  - rewrite (filter3_cons P Q R b (before ++ y :: after)).
    rewrite (filter3_cons P Q R b (before ++ x :: after)).
    destruct (decide (P b ∧ Q b ∧ R b)); simpl; lia.
Qed.

Lemma filter_append_excluded {A} (P : A → Prop)
    `{∀ x, Decision (P x)} xs x :
  ¬ P x → length (filter P (xs ++ [x])) = length (filter P xs).
Proof.
  intros Hnot. induction xs as [|y xs IH]; simpl.
  - rewrite !filter_cons. destruct (decide (P x)); [contradiction|done].
  - rewrite !filter_cons. destruct (decide (P y)); simpl; lia.
Qed.

Lemma filter2_append_excluded {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} xs x :
  ¬ (P x ∧ Q x) →
  length (filter Q (filter P (xs ++ [x]))) =
    length (filter Q (filter P xs)).
Proof.
  intros Hnot. induction xs as [|y xs IH]; simpl.
  - rewrite (filter2_cons P Q x []). case_decide; [contradiction|done].
  - rewrite (filter2_cons P Q y (xs ++ [x]))
      (filter2_cons P Q y xs).
    destruct (decide (P y ∧ Q y)); simpl; lia.
Qed.

Lemma filter3_append_excluded {A} (P Q R : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    `{∀ x, Decision (R x)} xs x :
  ¬ (P x ∧ Q x ∧ R x) →
  length (filter R (filter Q (filter P (xs ++ [x])))) =
    length (filter R (filter Q (filter P xs))).
Proof.
  intros Hnot. induction xs as [|y xs IH]; simpl.
  - rewrite (filter3_cons P Q R x []). case_decide; [contradiction|done].
  - rewrite (filter3_cons P Q R y (xs ++ [x]))
      (filter3_cons P Q R y xs).
    destruct (decide (P y ∧ Q y ∧ R y)); simpl; lia.
Qed.

Lemma lookup_insert_split {A} (xs : list A) idx x y :
  xs !! idx = Some x →
  ∃ before after,
    xs = before ++ x :: after ∧
    <[idx:=y]> xs = before ++ y :: after.
Proof.
  revert idx. induction xs as [|z xs IH]; intros [|idx] Hlookup;
    simpl in Hlookup; try done.
  - injection Hlookup as ->. exists [], xs. done.
  - destruct (IH idx Hlookup) as (before & after & -> & Hinsert).
    exists (z :: before), after. simpl. split; first done.
    by rewrite Hinsert.
Qed.

Lemma pod_distance_reconcile_desired_step set pods idx pod pod' :
  pods !! idx = Some pod →
  Forall (pod_has_int32_member_key set) pods →
  PodV.key pod' = PodV.key pod →
  pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') =
    pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') →
  pod'.(PodV.Spec') = pod.(PodV.Spec') →
  pod_identity_matches set pod' →
  pod_distance set (living_pods (<[idx:=pod']> pods)) ≤
    pod_distance set (living_pods pods).
Proof.
  intros Hlookup Hmembers Hkey Hdeletion Hspec Hidentity.
  assert (pod_has_int32_member_key set pod) as Hmember.
  { rewrite Forall_forall in Hmembers. apply Hmembers.
    rewrite -list_elem_of_In. by apply list_elem_of_lookup_2 in Hlookup. }
  assert (pod_has_int32_member_key set pod') as Hmember'.
  { eapply pod_has_int32_member_key_of_key_eq; [symmetry; exact Hkey|done]. }
  assert (is_pod_alive pod' ↔ is_pod_alive pod) as Halive.
  { unfold is_pod_alive. rewrite Hdeletion. done. }
  assert (pod_match set pod → pod_match set pod') as Hmatch.
  { intros [_ Himmutable]. split; first exact Hidentity.
    apply (proj1 (pod_immutable_matches_key_spec_eq set pod pod'
      (eq_sym Hkey) (eq_sym Hspec))). exact Himmutable. }
  destruct (lookup_insert_split pods idx pod pod' Hlookup) as
    (before & after & Hpods & Hpods').
  assert (PodV.key <$> living_pods (<[idx:=pod']> pods) =
      PodV.key <$> living_pods pods) as Hkeys.
  { rewrite Hpods' Hpods. unfold living_pods.
    rewrite !list.filter_app /=.
    destruct (decide (is_pod_alive pod')) as [Halive'|Hnot_alive'];
      destruct (decide (is_pod_alive pod)) as [Halive0|Hnot_alive].
    - rewrite (filter_cons_True is_pod_alive pod' after Halive')
        (filter_cons_True is_pod_alive pod after Halive0).
      by rewrite !fmap_app /= Hkey.
    - exfalso. exact (Hnot_alive ((proj1 Halive) Halive')).
    - exfalso. exact (Hnot_alive' ((proj2 Halive) Halive0)).
    - rewrite (filter_cons_False is_pod_alive pod' after Hnot_alive')
        (filter_cons_False is_pod_alive pod after Hnot_alive). done. }
  assert (length (bad_name_pods set (living_pods (<[idx:=pod']> pods))) =
      length (bad_name_pods set (living_pods pods))) as Hbad.
  { rewrite Hpods' Hpods. unfold bad_name_pods, living_pods.
    apply filter2_replace_length_eq.
    split; intros [Halive_now Hnot_member]; split.
    - apply (proj1 Halive). exact Halive_now.
    - intros Hmember_now. exact (Hnot_member Hmember').
    - apply (proj2 Halive). exact Halive_now.
    - intros Hmember_now. exact (Hnot_member Hmember). }
  assert (length (condemned_pods set
        (living_pods (<[idx:=pod']> pods))) =
      length (condemned_pods set (living_pods pods))) as Hcondemned.
  { rewrite Hpods' Hpods. unfold condemned_pods, living_pods.
    apply filter2_replace_length_eq.
    split; intros [Halive_now [Hmember_now Hnot_desired]]; split.
    - apply (proj1 Halive). exact Halive_now.
    - split; first exact Hmember. rewrite -Hkey. exact Hnot_desired.
    - apply (proj2 Halive). exact Halive_now.
    - split; first exact Hmember'. rewrite Hkey. exact Hnot_desired. }
  assert (length (outdated_pods set
        (living_pods (<[idx:=pod']> pods))) ≤
      length (outdated_pods set (living_pods pods))) as Houtdated.
  { rewrite Hpods' Hpods. unfold outdated_pods, needed_pods, living_pods.
    apply filter3_replace_length_le.
    intros [Halive_now [Hdesired Hnot_match]]. split_and!.
    - apply (proj1 Halive). exact Halive_now.
    - rewrite -Hkey. exact Hdesired.
    - intros Hpod_match. apply Hnot_match. by apply Hmatch. }
  unfold pod_distance, missing_pod_keys.
  rewrite Hkeys Hbad Hcondemned. lia.
Qed.

Lemma match_distance_reconcile_desired_step set next pods idx pod pod'
    pvc_map pvc_map' :
  pods !! idx = Some pod →
  Forall (pod_has_int32_member_key set) pods →
  PodV.key pod = desired_pod_key set next →
  PodV.key pod' = PodV.key pod →
  pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') =
    pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') →
  pod'.(PodV.Spec') = pod.(PodV.Spec') →
  pod_identity_matches set pod' →
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  (∀ key claim, pvc_map' !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  dom pvc_map ⊆ dom pvc_map' →
  match_distance set (<[idx:=pod']> pods)
      (pvc_list_of_map pvc_map') ≤
    match_distance set pods (pvc_list_of_map pvc_map).
Proof.
  intros Hlookup Hmembers _ Hkey Hdeletion Hspec Hidentity
    Hwf Hwf' Hdom.
  unfold match_distance.
  pose proof (pod_distance_reconcile_desired_step set pods idx pod pod'
    Hlookup Hmembers Hkey Hdeletion Hspec Hidentity) as Hpods.
  pose proof (pvc_distance_map_mono set pvc_map pvc_map' Hwf Hwf' Hdom)
    as Hpvcs.
  lia.
Qed.

Lemma find_pod_none_desired_key_missing set ordinal pods :
  (ordinal < statefulset_replicas set)%nat →
  find_pod_by_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal pods = None →
  desired_pod_key set ordinal ∈ missing_pod_keys set pods.
Proof.
  intros Hordinal Hfind.
  unfold find_pod_by_ordinal in Hfind.
  apply list_find_None in Hfind.
  rewrite Forall_forall in Hfind.
  unfold missing_pod_keys.
  apply list_elem_of_filter. split.
  - intros Hkey_in.
    apply list_elem_of_fmap_1 in Hkey_in as (pod & Hkey & Hpod_in).
    apply (Hfind pod (proj1 (list_elem_of_In pods pod) Hpod_in)).
    apply (f_equal KKey.Name') in Hkey.
    exact (eq_sym Hkey).
  - apply desired_pod_key_elem_iff. exact Hordinal.
Qed.

Lemma filter_notin_list_set_eq {A B} `{Countable B} (f : A → B)
    (xs : list A) ys zs :
  list_to_set (C:=gset B) ys = list_to_set zs →
  filter (λ x, f x ∉ ys) xs = filter (λ x, f x ∉ zs) xs.
Proof.
  intros Hsets. induction xs as [|x xs IH]; simpl; first done.
  rewrite !filter_cons.
  destruct (decide (f x ∉ ys)) as [Hy|Hy];
    destruct (decide (f x ∉ zs)) as [Hz|Hz]; simpl; try rewrite IH; try done.
  - exfalso. apply Hy.
    assert (f x ∈ zs) as Hin.
    { destruct (decide (f x ∈ zs)); done. }
    assert (f x ∈ list_to_set (C:=gset B) zs) as Hinset.
    { rewrite elem_of_list_to_set. exact Hin. }
    rewrite -Hsets elem_of_list_to_set in Hinset. exact Hinset.
  - exfalso. apply Hz.
    assert (f x ∈ ys) as Hin.
    { destruct (decide (f x ∈ ys)); done. }
    assert (f x ∈ list_to_set (C:=gset B) ys) as Hinset.
    { rewrite elem_of_list_to_set. exact Hin. }
    rewrite Hsets elem_of_list_to_set in Hinset. exact Hinset.
Qed.

Lemma desired_pvc_name_valid set ordinal name :
  input_requirement set →
  (ordinal < statefulset_replicas set)%nat →
  name ∈ pvc_claim_template_names set →
  valid_dns1123_subdomain
    (desired_pvc_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') name ordinal).
Proof.
  intros (_ & _ & Hpvc_valid) Hordinal Hname.
  unfold pvc_claim_template_names in Hname.
  apply list_elem_of_fmap_1 in Hname as (claim & -> & Hclaim).
  rewrite Forall_forall in Hpvc_valid.
  specialize (Hpvc_valid claim
    (proj1 (list_elem_of_In _ _) Hclaim) ordinal Hordinal).
  destruct Hpvc_valid as (_ & Hmeta & _).
  unfold ObjectMetaV.valid_named_create in Hmeta.
  destruct Hmeta as (_ & _ & Hname_valid & _).
  unfold new_persistent_volume_claim in Hname_valid. simpl in Hname_valid.
  unfold valid_name, PersistentVolumeClaimV.kind in Hname_valid.
  destruct Hname_valid as [[Hkind _]|[_ Hsubdomain]].
  - discriminate Hkind.
  - exact Hsubdomain.
Qed.

Lemma storage_claim_volume_valid set ordinal name :
  valid_dns1123_label name →
  valid_dns1123_subdomain
    (desired_pvc_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') name ordinal) →
  VolumeV.valid (storage_claim_volume set ordinal name).
Proof. intros Hname Hclaim. split; done. Qed.

Lemma new_statefulset_pod_requirements set ordinal controller_ref
    claim_template_names :
  StatefulSetV.valid set →
  input_requirement set →
  (ordinal < statefulset_replicas set)%nat →
  OwnerReferenceV.refers_to_controller controller_ref StatefulSetV.kind
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') →
  OwnerReferenceV.valid controller_ref →
  NoDup claim_template_names ∧
    list_to_set (C:=gset go_string) claim_template_names =
      list_to_set (pvc_claim_template_names set) →
  let pod := new_statefulset_pod set ordinal controller_ref
    claim_template_names in
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ∧
  PodV.valid_named_create
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') pod ∧
  obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ∧
  pod_match set pod.
Proof.
  intros Hset_valid Hinput Hordinal Hcontroller Hcontroller_valid
    [Hclaim_names_nodup Hclaim_names].
  destruct Hset_valid as
    (_ & _ & Hset_meta & Hset_spec & _).
  destruct Hset_spec as [Hset_spec_create _].
  destruct Hset_spec_create as
    (_ & _ & Htemplate & Hclaim_name_valid & _ & Hservice_valid).
  destruct Htemplate as
    (Htemplate_labels & Htemplate_annotations & Hpreserved_valid & _).
  destruct Hinput as
    (Hpod_names_valid & Htemplate_finalizers & Hpvc_valid).
  pose proof (Hpod_names_valid ordinal Hordinal) as Hpod_name_valid.
  assert ((ordinal ≤ go_int32_max_nat)%nat) as Hordinal_bound.
  { pose proof (statefulset_replicas_le_go_int32_max set). lia. }
  assert (length (decimal_string ordinal) ≤ 63) as Hdecimal_length.
  { destruct Hpod_name_valid as [_ Hpod_name_length].
    assert (length (decimal_string ordinal) ≤
        length (desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)).
    { unfold desired_pod_name. rewrite !app_length /=. lia. }
    lia. }
  assert (valid_dns1123_label
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name'))
    as Hset_name_valid.
  { pose proof (ObjectMetaV.valid_name_of_valid _ Hset_meta) as Hname.
    unfold valid_name, StatefulSetV.kind in Hname.
    destruct Hname as [[_ Hname]|[Hkind _]]; first exact Hname.
    destruct Hkind as [Hkind|[Hkind|Hkind]]; discriminate Hkind. }
  assert (valid_labels
      (Some
        (<[pod_index_label := decimal_string ordinal]>
          (<[statefulset_pod_name_label :=
              desired_pod_name
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal]>
            (default ∅
              set.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(
                PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels'))))))
    as Hlabels_valid.
  { assert (valid_labels
        (Some
          (<[statefulset_pod_name_label :=
              desired_pod_name
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal]>
            (default ∅
              set.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(
                PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))))
      as Hname_labels.
    { apply valid_labels_insert.
      - exact Htemplate_labels.
      - apply statefulset_pod_name_label_valid.
      - apply valid_label_value_of_valid_dns1123_label.
        exact Hpod_name_valid. }
    pose proof (valid_labels_insert _ pod_index_label
      (decimal_string ordinal) Hname_labels pod_index_label_valid
      (valid_label_value_decimal_string _ Hdecimal_length)) as Hlabels.
    exact Hlabels. }
  assert (valid_owner_references (Some [controller_ref])) as Howners_valid.
  { unfold valid_owner_references. split.
    - intros i1 i2 or1 or2 Hlookup1 Hlookup2 _ _.
      destruct i1 as [|i1], i2 as [|i2]; simpl in *; try done;
        discriminate.
    - intros owner Howner.
      rewrite list_elem_of_In in Howner. destruct Howner as [->|[]].
      exact Hcontroller_valid. }
  destruct Howners_valid as [Howner_unique Howner_each].
  assert (Forall VolumeV.valid
      (init_storage_volumes set
        (init_identity set
          (PodV.update_objectmeta
            (controller.generated_pod
              set.(StatefulSetV.Spec').(StatefulSetSpecV.Template')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (Some [controller_ref]))
            ((controller.generated_pod
              set.(StatefulSetV.Spec').(StatefulSetSpecV.Template')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (Some [controller_ref])).(PodV.ObjectMeta')
              <| ObjectMetaV.Name' :=
                desired_pod_name
                  set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                  ordinal |>)) ordinal)
        ordinal claim_template_names)) as Hvolumes_valid.
  { unfold init_storage_volumes. apply Forall_app. split.
    - apply Forall_fmap. apply Forall_forall.
      intros name Hname.
      assert (name ∈ pvc_claim_template_names set) as Hname_set.
      { assert (name ∈ list_to_set (C:=gset go_string)
            claim_template_names) as Hinset.
        { rewrite elem_of_list_to_set list_elem_of_In. exact Hname. }
        rewrite Hclaim_names elem_of_list_to_set in Hinset. exact Hinset. }
      apply storage_claim_volume_valid.
      + unfold pvc_claim_template_names in Hname_set.
        apply list_elem_of_fmap_1 in Hname_set as
          (claim & -> & Hclaim).
        rewrite Forall_forall in Hclaim_name_valid.
        apply (Hclaim_name_valid claim).
        exact (proj1 (list_elem_of_In _ _) Hclaim).
      + apply desired_pvc_name_valid; try done.
    - unfold init_identity, update_identity, PodV.update_objectmeta,
        controller.generated_pod. simpl.
      rewrite (filter_notin_list_set_eq VolumeV.Name'
        (PodSpecV.volumes_list
          set.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(
            PodTemplateSpecV.Spec'))
        claim_template_names (pvc_claim_template_names set)
        Hclaim_names).
      exact Hpreserved_valid. }
  assert (pod_storage_matches set
      (new_statefulset_pod set ordinal controller_ref claim_template_names))
    as Hstorage_matches.
  { unfold new_statefulset_pod.
    apply init_storage_storage_matches.
    - unfold init_identity, update_identity, PodV.update_objectmeta,
        controller.generated_pod, controller.generated_pod_meta. done.
    - exact Hordinal_bound.
    - exact Hclaim_names_nodup.
    - exact Hclaim_names. }
  split_and!.
  - unfold new_statefulset_pod, init_storage, init_identity,
      update_identity, PodV.update_objectmeta, controller.generated_pod. done.
  - unfold PodV.valid_named_create. split_and!.
    + apply zero_typemeta_valid_create.
    + unfold ObjectMetaV.valid_named_create, new_statefulset_pod,
        init_storage, init_identity, update_identity, PodV.update_objectmeta,
        controller.generated_pod, controller.generated_pod_meta. simpl.
      pose proof (valid_annotations_default _ Htemplate_annotations) as
        [Hannotations_keys Hannotations_size].
      split_and!.
      * intros _. apply valid_generate_name_of_valid_prefix.
        exists set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name').
        split_and!; try done.
        -- intros Hempty. rewrite Hempty in Hset_name_valid.
           destruct Hset_name_valid as [Hsyntax _]. contradiction.
        -- unfold valid_name, PodV.kind. right. split; first tauto.
           apply valid_dns1123_label_subdomain. exact Hset_name_valid.
      * destruct Hpod_name_valid as [Hsyntax _].
        intros Hempty. rewrite Hempty in Hsyntax. contradiction.
      * unfold valid_name, PodV.kind. right. split; first tauto.
        apply valid_dns1123_label_subdomain. exact Hpod_name_valid.
      * right. split.
        -- exact (ObjectMetaV.valid_namespace_of_valid _ Hset_meta).
        -- done.
      * exact Hlabels_valid.
      * exact Hannotations_keys.
      * exact Hannotations_size.
      * exact Howner_unique.
      * exact Howner_each.
      * apply valid_finalizers_default. exact Htemplate_finalizers.
      * apply valid_managed_fields_none.
    + unfold PodSpecV.valid_create, init_storage, new_statefulset_pod.
      simpl. split_and!.
      * exact Hvolumes_valid.
      * right. exact Hpod_name_valid.
      * destruct Hservice_valid as [->|Hservice].
        -- left. done.
        -- right. exact Hservice.
  - destruct Hcontroller as
      (Hcontroller_kind & Hcontroller_name & Hcontroller_uid &
       Hblock & Hcontroller_flag).
    unfold obj_parent_ref_is, KObjectV.objectmeta, meta_parent_ref_is,
      meta_parent_ref, new_statefulset_pod, init_storage, init_identity,
      update_identity, PodV.update_objectmeta, controller.generated_pod,
      controller.generated_pod_meta. simpl.
    rewrite Hcontroller_flag. simpl.
    rewrite Hcontroller_kind Hcontroller_name Hcontroller_uid. done.
  - split.
    + unfold pod_identity_matches, new_statefulset_pod, init_storage,
        init_identity, update_identity, PodV.update_objectmeta,
        controller.generated_pod, controller.generated_pod_meta.
      cbn -[parse_member_name].
      rewrite (parse_member_name_complete
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        (desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
        ordinal eq_refl).
      cbn. split_and!; try done.
      * rewrite lookup_insert_ne.
        -- unfold pod_index_label, statefulset_pod_name_label.
           intros Hlabels. inversion Hlabels.
        -- rewrite lookup_insert_eq. done.
      * rewrite lookup_insert_eq. done.
    + unfold pod_immutable_matches, new_statefulset_pod, init_storage,
        init_identity. simpl. split_and!; try done.
Qed.

Lemma created_statefulset_pod_properties set ordinal pod pod' :
  pod_match set pod →
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    desired_pod_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal →
  ObjectMetaV.named_created
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
    pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') →
  ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec'))
    (ObjectSpecV.PodSpec pod'.(PodV.Spec')) →
  PodV.key pod' = desired_pod_key set ordinal ∧
  is_pod_alive pod' ∧
  pod_has_int32_member_key set pod' ∧
  pod_match set pod'.
Proof.
  intros [Hidentity Himmutable] Hpod_name Hmeta_created Hspec_created.
  unfold ObjectMetaV.named_created in Hmeta_created.
  destruct Hmeta_created as
    (Hnamespace & Hname & Hgenerate_name & Hdeletion & Hannotations &
      Hlabels & Howners & Hfinalizers).
  unfold ObjectSpecV.created in Hspec_created. simpl in Hspec_created.
  unfold PodSpecV.created in Hspec_created.
  assert (pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
    as Hpod_namespace.
  { unfold pod_identity_matches in Hidentity.
    destruct (parse_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')); try contradiction.
    destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'); try contradiction.
    destruct Hidentity as (_ & Hpod_namespace & _). exact Hpod_namespace. }
  assert ((ordinal ≤ go_int32_max_nat)%nat) as Hordinal_bound.
  { unfold pod_identity_matches in Hidentity.
    rewrite (parse_member_name_complete
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ordinal Hpod_name)
      in Hidentity.
    destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'); try contradiction.
    destruct Hidentity as [Hbound _]. exact Hbound. }
  assert (PodV.key pod' = PodV.key pod) as Hkey.
  { unfold PodV.key, PodV.meta_key. simpl.
    rewrite Hnamespace Hpod_namespace Hname. done. }
  split_and!.
  - unfold PodV.key, PodV.meta_key, desired_pod_key. simpl.
    rewrite Hnamespace Hname Hpod_name. done.
  - unfold is_pod_alive. exact Hdeletion.
  - unfold pod_has_int32_member_key. split.
    + exact Hnamespace.
    + exists ordinal. split.
      * exact Hordinal_bound.
      * rewrite Hname Hpod_name. done.
  - split.
    + unfold pod_identity_matches.
      rewrite Hname Hlabels Hnamespace.
      unfold pod_identity_matches in Hidentity.
      rewrite Hpod_namespace in Hidentity. exact Hidentity.
    + apply (proj1 (pod_immutable_matches_key_spec_eq set pod pod'
        (eq_sym Hkey) (eq_sym Hspec_created))).
      exact Himmutable.
Qed.

Lemma pod_distance_append_matching set pods pod :
  PodV.key pod ∈ missing_pod_keys set pods →
  is_pod_alive pod →
  pod_has_int32_member_key set pod →
  pod_match set pod →
  pod_distance set (pods ++ [pod]) < pod_distance set pods.
Proof.
  intros Hmissing Halive Hmember Hmatch.
  apply list_elem_of_filter in Hmissing as [Hnotin Hdesired].
  assert (length (missing_pod_keys set pods) =
      S (length (missing_pod_keys set (pods ++ [pod])))) as Hmissing_len.
  { unfold missing_pod_keys. rewrite fmap_app /=.
    assert (PodV.key pod ∉ ([] : list KKey.t)) as Hnil.
    { intros Hnil. rewrite list_elem_of_In in Hnil. inversion Hnil. }
    pose proof (filter_not_elem_remove_unique
      (desired_pod_keys set) (PodV.key <$> pods) [] (PodV.key pod)
      (desired_pod_keys_nodup set) Hdesired Hnotin Hnil) as Hlen.
    rewrite app_nil_r in Hlen. exact Hlen. }
  assert (length (outdated_pods set (pods ++ [pod])) =
      length (outdated_pods set pods)) as Houtdated.
  { unfold outdated_pods, needed_pods.
    apply filter2_append_excluded. intros [_ Hnot_match].
    apply Hnot_match. exact Hmatch. }
  assert (length (condemned_pods set (pods ++ [pod])) =
      length (condemned_pods set pods)) as Hcondemned.
  { unfold condemned_pods.
    apply filter_append_excluded. intros [_ Hnot_desired].
    apply Hnot_desired. exact Hdesired. }
  assert (length (bad_name_pods set (pods ++ [pod])) =
      length (bad_name_pods set pods)) as Hbad_name.
  { unfold bad_name_pods.
    apply filter_append_excluded. intros Hnot. apply Hnot. exact Hmember. }
  unfold pod_distance.
  rewrite Houtdated Hcondemned Hbad_name. lia.
Qed.

Lemma reconcile_desired_create_progress set local_pods pods pod'
    ordinal pvc_map pvc_map' :
  local_pods_match_stored local_pods pods →
  (ordinal < statefulset_replicas set)%nat →
  desired_pod_key set ordinal ∉ PodV.key <$> local_pods →
  PodV.key pod' = desired_pod_key set ordinal →
  is_pod_alive pod' →
  pod_has_int32_member_key set pod' →
  pod_match set pod' →
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  (∀ key claim, pvc_map' !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  dom pvc_map ⊆ dom pvc_map' →
  pods_progress_observed local_pods (pods ++ [pod']) ∧
  match_distance set (pods ++ [pod']) (pvc_list_of_map pvc_map') <
    match_distance set pods (pvc_list_of_map pvc_map).
Proof.
  intros Hlocal Hordinal Hfresh Hkey Halive Hmember Hmatch Hwf Hwf' Hdom.
  split.
  - unfold pods_progress_observed. left. intros Hsets.
    apply Hfresh.
    assert (desired_pod_key set ordinal ∈
        list_to_set (C:=gset KKey.t) (PodV.key <$> local_pods)) as Hin.
    { rewrite Hsets elem_of_list_to_set fmap_app /=.
      apply elem_of_app. right. rewrite -Hkey. left. }
    rewrite elem_of_list_to_set in Hin. exact Hin.
  - unfold match_distance.
    assert (PodV.key pod' ∈ missing_pod_keys set (living_pods pods))
      as Hmissing.
    { unfold missing_pod_keys. apply list_elem_of_filter. split.
      - intros Hin. apply Hfresh.
        rewrite (local_pods_match_stored_keys _ _ Hlocal) -Hkey.
        apply list_elem_of_fmap_1 in Hin as (pod0 & -> & Hin).
        apply list_elem_of_fmap_2. unfold living_pods in Hin.
        by apply list_elem_of_filter in Hin as [_ Hin].
      - rewrite Hkey. apply desired_pod_key_elem_iff. exact Hordinal. }
    pose proof (pod_distance_append_matching set (living_pods pods) pod'
      Hmissing Halive Hmember Hmatch) as Hpods.
    assert (living_pods (pods ++ [pod']) = living_pods pods ++ [pod'])
      as Hliving_append.
    { unfold living_pods. rewrite list.filter_app /=.
      rewrite (filter_cons_True is_pod_alive pod' [] Halive). done. }
    rewrite Hliving_append.
    pose proof (pvc_distance_map_mono set pvc_map pvc_map' Hwf Hwf' Hdom)
      as Hpvcs.
    lia.
Qed.

Lemma reconcile_loop_exit_ordinal (ordinal end_ordinal : w64) replicas :
  0 ≤ sint.Z ordinal →
  sint.Z ordinal ≤ Z.of_nat replicas →
  sint.Z end_ordinal = Z.of_nat replicas - 1 →
  ¬ sint.Z ordinal ≤ sint.Z end_ordinal →
  sint.nat ordinal = replicas.
Proof.
  intros Hnonnegative Hupper Hend Hnot_le.
  assert (sint.Z ordinal = Z.of_nat replicas) as Hordinal by lia.
  apply Nat2Z.inj.
  rewrite Z2Nat.id; [exact Hnonnegative|exact Hordinal].
Qed.

Lemma desired_pvc_key_elem_elim set key :
  key ∈ desired_pvc_keys set →
  ∃ ordinal name,
    (ordinal < statefulset_replicas set)%nat ∧
    name ∈ dom
      (persistent_volume_claim_templates_by_name
        (StatefulSetSpecV.volume_claim_templates_list
          set.(StatefulSetV.Spec'))) ∧
    key = desired_pvc_key set name ordinal.
Proof.
  intros Hkey.
  unfold desired_pvc_keys in Hkey.
  rewrite elem_of_elements elem_of_list_to_set in Hkey.
  unfold desired_pvc_key_candidates in Hkey.
  rewrite list_elem_of_In in Hkey.
  apply in_concat in Hkey as (keys & Hkeys & Hkey).
  rewrite -list_elem_of_In in Hkeys, Hkey.
  apply list_elem_of_fmap_1 in Hkeys as (ordinal & -> & Hordinal).
  rewrite -list_elem_of_In in Hkey.
  apply list_elem_of_fmap_1 in Hkey as (name & -> & Hname).
  exists ordinal, name. split_and!.
  - unfold statefulset_replicas, desired_ordinals in *.
    apply elem_of_seq in Hordinal. lia.
  - rewrite persistent_volume_claim_templates_by_name_dom
      elem_of_list_to_set.
    exact Hname.
  - done.
Qed.

Lemma desired_prefix_reconciled_complete set pods pvc_map :
  desired_prefix_reconciled set (statefulset_replicas set) pods pvc_map →
  Forall (pod_has_int32_member_key set) pods →
  NoDup (PodV.key <$> pods) →
  (∀ key claim, pvc_map !! key = Some claim →
    PersistentVolumeClaimV.key claim = key) →
  desired_objects_reconciled set pods (pvc_list_of_map pvc_map).
Proof.
  intros Hprefix Hmembers Hnodup Hpvc_wf.
  unfold desired_objects_reconciled.
  split_and!.
  - unfold missing_pod_keys.
    apply filter_none. intros key Hdesired Hmissing.
    unfold desired_pod_keys in Hdesired.
    apply list_elem_of_fmap_1 in Hdesired as
      (ordinal & -> & Hordinal).
    unfold desired_ordinals in Hordinal.
    apply elem_of_seq in Hordinal as [_ Hordinal].
    destruct (Hprefix ordinal Hordinal Hordinal) as
      [[pod [Hpod_in [Hpod_key _]]] _].
    apply Hmissing. rewrite -Hpod_key.
    by apply list_elem_of_fmap_2.
  - unfold missing_pvc_keys.
    apply filter_none. intros key Hdesired Hmissing.
    destruct (desired_pvc_key_elem_elim set key Hdesired) as
      (ordinal & name & Hordinal & Hname & ->).
    destruct (Hprefix ordinal Hordinal Hordinal) as [_ Hpvc].
    apply Hmissing.
    assert (desired_pvc_key set name ordinal ∈
        list_to_set (C:=gset KKey.t)
          (PersistentVolumeClaimV.key <$> pvc_list_of_map pvc_map)) as Hset.
    { rewrite (pvc_list_of_map_key_set _ Hpvc_wf).
      exact (Hpvc name Hname). }
    rewrite elem_of_list_to_set in Hset. exact Hset.
  - apply Forall_forall. intros pod Hpod_in Hdesired.
    unfold pod_key_is_desired, desired_pod_keys in Hdesired.
    apply list_elem_of_fmap_1 in Hdesired as
      (ordinal & Hpod_key & Hordinal).
    unfold desired_ordinals in Hordinal.
    apply elem_of_seq in Hordinal as [_ Hordinal].
    destruct (Hprefix ordinal Hordinal Hordinal) as
      [[reconciled [Hreconciled_in
        [Hreconciled_key [Halive Hidentity]]]] _].
    rewrite -list_elem_of_In in Hpod_in.
    assert (pod = reconciled) as ->.
    { eapply (NoDup_fmap_inj_on PodV.key pods).
      - exact Hnodup.
      - exact Hpod_in.
      - exact Hreconciled_in.
      - exact (eq_trans Hpod_key (eq_sym Hreconciled_key)). }
    done.
Qed.

Lemma wp_reconcileDesiredPods γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods : list PodV.t) (pvcs : list PersistentVolumeClaimV.t)
    dq_set dq_pods phase :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set pods,
        own_available_frag γ key) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set pvcs,
        own_available_frag γ key) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hpending_empty" ∷ ⌜ filter (pending_pod set) pods = [] ⌝ ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement set ⌝
  }}}
    @! statefulset.reconcileDesiredPods #set_l #pods_sl
  {{{ (continue : bool) (pods' : list PodV.t)
      (pvcs' : list PersistentVolumeClaimV.t),
      RET (#continue, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods' ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs' ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods')) ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "Hreserved_pods" ∷ own_missing_pod_reservations γ set pods' ∗
      "Hreserved_pvcs" ∷ own_missing_pvc_reservations γ set pvcs' ∗
      "%Hdistance" ∷ ⌜
        match_distance set pods' pvcs' ≤ match_distance set pods pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      ( (⌜ continue = true ⌝ ∗
          ⌜ local_pods_match_stored pods pods' ⌝ ∗
          ⌜ desired_objects_reconciled set pods' pvcs' ⌝)
        ∨
        (⌜ continue = false ⌝ ∗
          ⌜ progress_or_complete set pods pvcs pods' pvcs' ⌝))
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
  iPoseProof (kview.own_meta_list_no_dup
    PersistentVolumeClaimV.key PersistentVolumeClaimV.ObjectMeta'
    with "Hown_pvcs") as "%Hpvc_keys_nodup".
  iCombine "Hown_pvcs Hoccupied_pvcs" as "Hown_pvcs".
  iEval (rewrite /own_occupied_pvcs -big_sepL_sep) in "Hown_pvcs".
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
  assert (NoDup (missing_pod_keys set pods)) as Hinitial_reserved_pods_nodup.
  { unfold missing_pod_keys. apply list.NoDup_filter. apply desired_pod_keys_nodup. }
  iEval (rewrite -(big_sepS_list_to_set _ _ Hinitial_reserved_pods_nodup)) in "Hreserved_pods".
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
  iIntros (end_ordinal) "[%Hend_ordinal Hset]".
  wp_auto.
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
    "Hown_pods" ∷ ([∗ list] pod ∈ current_pods,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "Hoccupied_pods" ∷ own_occupied_pods γ current_pods ∗
    "Hown_pvcs" ∷ own_pvc_map γ pvc_map ∗
    "Hown_children" ∷ own_children_frag γ
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> current_pods)) ∗
    "Hterminating_children_frag" ∷ own_terminating_children_frag γ
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
    "Hreserved_pods" ∷ ([∗ set] key ∈
      list_to_set (C:=gset KKey.t) (missing_pod_keys set current_pods), own_available_frag γ key) ∗
    "Hreserved_pvcs" ∷ ([∗ list] key ∈ reserved_pvcs,
      own_available_frag γ key) ∗
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
    "%Hdistance" ∷ ⌜ match_distance set current_pods
      (pvc_list_of_map pvc_map) ≤ match_distance set pods pvcs ⌝)%I.
  iAssert I with "[Hset Hpods_sl Hpods Hown_pods Hoccupied_pods Hown_pvcs
      Hown_children Hterminating_children_frag Hreserved_pods Hreserved_pvcs
      ordinal end set pods]"
    as "Hloop".
  { iExists (W64 0), pods, initial_pvc_map,
      (missing_pvc_keys set pvcs).
    iFrame.
    iPureIntro. split_and!.
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
        rewrite Hmap_keys in Hkeys_perm'.
        exact Hkeys_perm'. }
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
  wp_for "Hloop".
  wp_if_destruct.
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
      (sint.nat ordinal) pods) as [[pod_idx local_pod]|] eqn:Hfind_pod.
    + simpl in Hfind.
      apply list_find_Some in Hfind_pod as
        (Hlocal_lookup & Hlocal_name & _).
      pose proof (local_pods_match_stored_lookup
        pods current_pods pod_idx local_pod Hlocal_stored Hlocal_lookup)
        as (stored_pod & Hstored_lookup & Hlocal_stored_pod).
      assert (pod_has_int32_member_key set local_pod) as Hlocal_member.
      { rewrite Forall_forall in Hpods_members. apply Hpods_members.
        apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
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
      assert (is_pod_alive local_pod) as Hlocal_alive.
      { pose proof (pending_pods_empty_alive set pods
          Hpending_empty Hpods_members) as Halive.
        rewrite Forall_forall in Halive. apply Halive.
        apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
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
      { exfalso. apply (proj1 Hterminating eq_refl). exact Hlocal_alive. }
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
        apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
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
      iEval (rewrite big_sepL_sep Hcurrent_decomp
        !big_sepL_app !big_sepL_cons) in "Hown_pods".
      iDestruct "Hown_pods" as
        "[[Hmeta_before [Hlocal_meta Hmeta_after]]
          [Hspec_before [Hlocal_spec Hspec_after]]]".
      iEval (rewrite /own_occupied_pods Hcurrent_decomp
        big_sepL_app big_sepL_cons) in "Hoccupied_pods".
      iDestruct "Hoccupied_pods" as
        "[Hoccupied_before [Hlocal_occupied Hoccupied_after]]".
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
      iAssert (([∗ list] pod ∈
          current_before ++ stored_pod' :: current_after,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta')))%I
        with "[Hmeta_before Hupdate_Hown_meta Hmeta_after]" as "Hown_meta".
      { rewrite big_sepL_app big_sepL_cons.
        rewrite Hupdate_Hpod_key Hupdate_Hpod_uid. iFrame. }
      iAssert (([∗ list] pod ∈
          current_before ++ stored_pod' :: current_after,
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
        with "[Hspec_before Hupdate_Hown_spec Hspec_after]" as "Hown_spec".
      { rewrite big_sepL_app big_sepL_cons.
        rewrite Hupdate_Hpod_key Hupdate_Hpod_uid. iFrame. }
      iCombine "Hown_meta Hown_spec" as "Hown_pods".
      iEval (rewrite -big_sepL_sep) in "Hown_pods".
      iAssert (own_occupied_pods γ
          (current_before ++ stored_pod' :: current_after))
        with "[Hoccupied_before Hlocal_occupied Hoccupied_after]"
        as "Hoccupied_pods".
      { rewrite /own_occupied_pods big_sepL_app big_sepL_cons
          Hupdate_Hpod_key Hupdate_Hpod_uid. iFrame. }
      iAssert (own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (list_to_set (PodV.key <$>
            (current_before ++ stored_pod' :: current_after))))
        with "[Hown_children]" as "Hown_children".
      { pose proof (f_equal (λ xs, PodV.key <$> xs) Hcurrent_decomp)
          as Hkey_decomp.
        rewrite !fmap_app /= in Hkey_decomp.
        rewrite !fmap_app /= Hupdate_Hpod_key -Hkey_decomp.
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
      assert (list_to_set (C:=gset KKey.t) (missing_pod_keys set current_pods) =
          list_to_set (missing_pod_keys set current_pods')) as Hmissing_set.
      { apply missing_pod_key_set_fmap_eq. rewrite Hcurrent_insert. symmetry. exact Hcurrent_keys. }
      iEval (rewrite Hmissing_set) in "Hreserved_pods".
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
      wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "HΦ".
      iExists (word.add ordinal (W64 1)), current_pods', pvc_map',
        reserved_pvcs'.
      iFrame.
      rewrite Hnext_nat.
      iPureIntro. split_and!.
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
          missing_pod_keys set current_pods) as Hmissing_current.
      { unfold missing_pod_keys. apply list_elem_of_filter. split; last exact Hmissing_pod_desired.
        rewrite -(local_pods_match_stored_keys pods current_pods Hlocal_stored).
        exact Hmissing_pod_notin. }
      assert (desired_pod_key set (sint.nat ordinal) ∈
          list_to_set (C:=gset KKey.t) (missing_pod_keys set current_pods)) as Hmissing_current_set.
      { by rewrite elem_of_list_to_set. }
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
      wp_apply (wp_createStatefulPod γ model_l set_l new_pod_l
        set new_pod (sint.nat ordinal)
        (list_to_set (PodV.key <$> current_pods)) dq_set
        with "[$Hset $Hnew_pod $Hpod_reserved $Hown_children
          $Hpvc_states]").
      { iFrame "#". iPureIntro.
        pose proof Hset_meta_valid as
          (_ & _ & _ & Hnamespace_nonempty & Hnamespace_valid & _).
        split_and!; done. }
      iIntros (stored_pod' uid) "Hcreate".
      iNamedPrefix "Hcreate" "Hcreate_".
      iEval (rewrite /pvc_done) in "Hcreate_Hpvc_states".
      iEval (rewrite persistent_volume_claim_templates_by_name_dom
        /pvc_claim_template_names) in "Hpvc_finish".
      iDestruct ("Hpvc_finish" with "Hcreate_Hpvc_states") as
        (pvc_map' reserved_pvcs')
        "(Hown_pvcs & Hreserved_pvcs & %Hpvc_result)".
      destruct Hpvc_result as
        (Hpvc_wf' & Hreserved_pvcs_nodup' & Hpvc_coverage' &
          Hpvc_dom_mono & Hordinal_pvcs).
      pose proof (created_statefulset_pod_properties set
        (sint.nat ordinal) new_pod stored_pod'
        Hnew_pod_match Hnew_pod_name Hcreate_Hpod_meta_created
        Hcreate_Hpod_spec_created) as
        (Hstored_pod_key & Hstored_pod_alive & Hstored_pod_member &
          Hstored_pod_match).
      set current_pods' := current_pods ++ [stored_pod'].
      assert (pods_progress_observed pods current_pods' ∧
          match_distance set current_pods' (pvc_list_of_map pvc_map') <
            match_distance set current_pods (pvc_list_of_map pvc_map))
        as (Hprogress & Hdistance_strict).
      { unfold current_pods'.
        eapply reconcile_desired_create_progress;
          [exact Hlocal_stored|exact Hordinal_lt|exact Hmissing_pod_notin|
           exact Hstored_pod_key|exact Hstored_pod_alive|
           exact Hstored_pod_member|exact Hstored_pod_match|exact Hpvc_wf|
           exact Hpvc_wf'|exact Hpvc_dom_mono]. }
      iAssert (([∗ list] pod ∈ current_pods',
          own_meta_frag γ (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
        with "[Hown_pods Hcreate_Hpod_meta Hcreate_Hpod_spec]"
        as "Hown_pods".
      { unfold current_pods'. rewrite big_sepL_app big_sepL_singleton.
        rewrite -Hcreate_Hpod_key -Hcreate_Huid. iFrame. }
      iAssert (own_occupied_pods γ current_pods')
        with "[Hoccupied_pods Hcreate_Hpod_reserved]"
        as "Hoccupied_pods".
      { unfold current_pods'.
        rewrite /own_occupied_pods big_sepL_app big_sepL_singleton.
        rewrite -Hcreate_Hpod_key -Hcreate_Huid. iFrame. }
      iAssert (own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (list_to_set (PodV.key <$> current_pods')))
        with "[Hcreate_Hown_children]" as "Hown_children".
      { unfold current_pods'.
        rewrite fmap_app /= list_to_set_app_L list_to_set_singleton_L.
        rewrite Hcreate_Hpod_key. iExact "Hcreate_Hown_children". }
      iEval (rewrite (own_pvc_map_as_list γ pvc_map' Hpvc_wf'))
        in "Hown_pvcs".
      iEval (rewrite big_sepL_sep) in "Hown_pvcs".
      iDestruct "Hown_pvcs" as "[Hown_pvcs Hoccupied_pvcs]".
      assert (match_distance set current_pods'
          (pvc_list_of_map pvc_map') ≤ match_distance set pods pvcs)
        as Hdistance'.
      { etrans; first exact (Z.lt_le_incl _ _ Hdistance_strict).
        exact Hdistance. }
      assert (match_distance set current_pods'
          (pvc_list_of_map pvc_map') < match_distance set pods pvcs)
        as Hdistance_strict'.
      { exact (Z.lt_le_trans _ _ _ Hdistance_strict Hdistance). }
      assert (Forall (pod_has_int32_member_key set) current_pods')
        as Hcurrent_members'.
      { unfold current_pods'. apply Forall_app. split;
          first exact Hcurrent_members.
        constructor; done. }
      assert (PodV.key stored_pod' ∉ PodV.key <$> current_pods) as Hstored_fresh.
      { unfold missing_pod_keys in Hmissing_current.
        apply list_elem_of_filter in Hmissing_current as [Hfresh _].
        by rewrite Hstored_pod_key. }
      assert (list_to_set (C:=gset KKey.t)
          (missing_pod_keys set current_pods') =
          list_to_set (missing_pod_keys set current_pods) ∖
            {[PodV.key stored_pod']}) as Hmissing_snoc.
      { unfold current_pods'. apply missing_pod_key_set_snoc.
        - by rewrite Hstored_pod_key.
        - exact Hstored_fresh. }
      iAssert (own_missing_pod_reservations γ set current_pods')
        with "[Hreserved_pods]" as "Hreserved_pods".
      { rewrite /own_missing_pod_reservations Hmissing_snoc.
        rewrite Hstored_pod_key. iApply (big_sepS_mono with "Hreserved_pods").
        iIntros (key Hkey) "Hkey". by iLeft. }
      iPoseProof (own_reserved_pvcs_finish γ set pvc_map' reserved_pvcs'
        Hpvc_wf' Hreserved_pvcs_nodup' Hpvc_coverage' with "Hreserved_pvcs") as "Hreserved_pvcs".
      wp_auto.
      iApply wp_for_post_return. wp_auto.
      iApply ("HΦ" $! false current_pods' (pvc_list_of_map pvc_map')).
      iFrame. iPureIntro. split; first exact Hdistance'.
      split; first exact Hcurrent_members'.
      right. split; first done. right. split; done.
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
    iEval (rewrite (own_pvc_map_as_list γ pvc_map Hpvc_wf))
      in "Hown_pvcs".
    iEval (rewrite big_sepL_sep) in "Hown_pvcs".
    iDestruct "Hown_pvcs" as "[Hown_pvcs Hoccupied_pvcs]".
    iPoseProof (own_available_missing_to_missing γ set current_pods
      with "Hreserved_pods") as "Hreserved_pods".
    iPoseProof (own_reserved_pvcs_finish γ set pvc_map reserved_pvcs
      Hpvc_wf Hreserved_pvcs_nodup Hpvc_coverage with "Hreserved_pvcs") as "Hreserved_pvcs".
    iApply ("HΦ" $! true current_pods (pvc_list_of_map pvc_map)).
    iFrame. iPureIntro. split; first exact Hdistance.
    split; first exact Hcurrent_members.
    left. split_and!; done.
Qed.

Lemma wp_reconcileCondemnedPod γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (local_pods pods : list PodV.t)
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
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hlocal_pods_valid" ∷ ⌜ Forall PodV.valid local_pods ⌝ ∗
      "%Hlocal_pods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) local_pods ⌝ ∗
      "%Hlocal_pods_nodup" ∷
        ⌜ NoDup (PodV.key <$> local_pods) ⌝ ∗
      "%Hlocal_stored" ∷
        ⌜ local_pods_match_stored local_pods pods ⌝ ∗
      "%Hpending_empty" ∷
        ⌜ filter (pending_pod set) local_pods = [] ⌝ ∗
      "%Hdistance_le" ∷ ⌜
        match_distance set pods pvcs ≤
          match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hdesired_reconciled" ∷
        ⌜ desired_objects_reconciled set pods pvcs ⌝
  }}}
    @! statefulset.reconcileCondemnedPod #set_l #pods_sl
  {{{ (continue : bool) (pods' : list PodV.t)
      (deletion : option (KKey.t * types.UID.t)),
      RET (#continue, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;local_pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods' ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods')) ∗
      "Hstarted_deletion" ∷ own_started_deletion γ deletion ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        (phase_after_deletion phase deletion) ∗
      "%Hdeletion_retiring" ∷ ⌜ match deletion with
        | None => True
        | Some (key, _) => key ∉ desired_pod_keys set
        end ⌝ ∗
      "%Hdistance" ∷ ⌜
        match_distance set pods' pvcs ≤
          match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      "%Hdesired_reconciled" ∷
        ⌜ desired_objects_reconciled set pods' pvcs ⌝ ∗
      ( (⌜ continue = true ⌝ ∗
          ⌜ deletion = None ⌝ ∗
          ⌜ pods' = pods ⌝ ∗
          ⌜ Forall (λ pod, ¬ pod_is_condemned set pod) pods' ⌝)
        ∨
        (⌜ continue = false ⌝ ∗
          ⌜ is_Some deletion ⌝ ∗
          ⌜ progress_or_complete set local_pods initial_pvcs pods' pvcs ⌝))
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
  pose proof (pending_pods_empty_alive set local_pods
    Hpending_empty Hlocal_pods_members) as Hlocal_alive.
  wp_apply (wp_firstCondemnedPod set_l pods_sl set ptrs local_pods
    dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
  { iPureIntro. split_and!; done. }
  iIntros (condemned_l)
    "(Hset & Hpods_sl & Hpods & %Hcondemned)".
  destruct Hcondemned as
    [[-> Hnone_local]|(idx & local_pod & Hptr_lookup & Hlocal_lookup &
      Hlocal_condemned)].
  - wp_auto.
    assert (Forall (λ pod, ¬ pod_is_condemned set pod) pods)
      as Hnone_stored.
    { eapply local_pods_match_stored_no_condemned; done. }
    assert (Forall (pod_has_int32_member_key set) pods)
      as Hstored_members.
    { eapply local_pods_match_stored_members; done. }
    assert (Forall is_pod_alive pods) as Hstored_alive.
    { eapply local_pods_match_stored_alive_all; done. }
    assert (living_pods pods = pods) as Hliving.
    { unfold living_pods. apply filter_all.
      rewrite Forall_forall in Hstored_alive.
      intros pod Hpod. apply Hstored_alive.
      by rewrite -list_elem_of_In. }
    iApply ("HΦ" $! true pods None).
    rewrite /own_started_deletion /phase_after_deletion /=.
    iFrame. iPureIntro. split; first done.
    split; first exact Hdistance_le.
    split; first exact Hstored_members.
    split.
    { rewrite -(local_pods_match_stored_keys _ _ Hlocal_stored).
      exact Hlocal_pods_nodup. }
    split; first exact Hdesired_reconciled.
    left. split_and!; done.
  - pose proof (local_pods_match_stored_lookup
      local_pods pods idx local_pod Hlocal_stored Hlocal_lookup)
      as (stored_pod & Hstored_lookup & Hlocal_stored_pod).
    pose proof Hlocal_stored_pod as
      (Hlocal_key & Hlocal_uid & Hlocal_deletion & Hlocal_spec).
    assert (is_pod_alive local_pod) as Hlocal_pod_alive.
    { rewrite Forall_forall in Hlocal_alive. apply Hlocal_alive.
      apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
    assert (is_pod_alive stored_pod) as Hstored_pod_alive.
    { apply (proj1
        (local_pod_matches_stored_alive _ _ Hlocal_stored_pod)).
      exact Hlocal_pod_alive. }
    assert (pod_is_condemned set stored_pod) as Hstored_condemned.
    { apply (proj1
        (local_pod_matches_stored_condemned set _ _
          Hlocal_stored_pod)).
      exact Hlocal_condemned. }
    assert (pod_has_int32_member_key set stored_pod) as Hstored_member.
    { rewrite Forall_forall in Hlocal_pods_members.
      eapply pod_has_int32_member_key_of_key_eq; first exact Hlocal_key.
      apply Hlocal_pods_members.
      apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
    assert (¬ pod_key_is_desired set (PodV.key stored_pod))
      as Hnot_desired.
    { apply (proj1
        (pod_int32_member_condemned_iff set stored_pod Hstored_member)).
      exact Hstored_condemned. }
    assert (NoDup (PodV.key <$> pods)) as Hstored_nodup.
    { rewrite -(local_pods_match_stored_keys _ _ Hlocal_stored).
      exact Hlocal_pods_nodup. }
    assert (Forall (pod_has_int32_member_key set) pods)
      as Hstored_members.
    { eapply local_pods_match_stored_members; done. }
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
    { exfalso. apply (proj1 Hterminating eq_refl).
      exact Hlocal_pod_alive. }
    wp_auto.

    set before := take idx pods.
    set after := drop (S idx) pods.
    assert (pods = before ++ stored_pod :: after) as Hpods_decomp.
    { unfold before, after. symmetry.
      by apply take_drop_middle. }
    iEval (rewrite big_sepL_sep) in "Hown_pods".
    iDestruct "Hown_pods" as "[Hown_meta Hown_spec]".
    iEval (rewrite Hpods_decomp big_sepL_app big_sepL_cons) in
      "Hown_meta Hown_spec".
    iDestruct "Hown_meta" as
      "[Hmeta_before [Hstored_meta Hmeta_after]]".
    iDestruct "Hown_spec" as
      "[Hspec_before [Hstored_spec Hspec_after]]".
    iEval (rewrite /own_occupied_pods Hpods_decomp
      big_sepL_app big_sepL_cons) in "Hoccupied_pods".
    iDestruct "Hoccupied_pods" as
      "[Hoccupied_before [Hstored_occupied Hoccupied_after]]".
    assert (PodV.key stored_pod ∈
        list_to_set (C:=gset KKey.t) (PodV.key <$> pods)) as Hkey_in.
    { apply elem_of_list_to_set. apply list_elem_of_fmap_2.
      by apply list_elem_of_lookup_2 in Hstored_lookup. }
    wp_apply (wp_deletePod γ model_l condemned_l
      local_pod stored_pod (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
      (list_to_set (PodV.key <$> pods)) phase dq_pods
      with "[$Hlocal_pod $Hstored_meta $Hstored_spec $Hstored_occupied
        $Hown_children $Hterminating_children_frag]").
    { iFrame "#". iPureIntro. split_and!; done. }
    iIntros "Hdelete". iNamedPrefix "Hdelete" "Hdelete_".
    iSpecialize ("Hlocal_pod_restore" with "Hdelete_Hpod").
    iRename "Hlocal_pod_restore" into "Hpods".
    iAssert (([∗ list] pod0 ∈ before ++ after,
        own_meta_frag γ (PodV.key pod0)
          pod0.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod0.(PodV.ObjectMeta')))%I
      with "[Hmeta_before Hmeta_after]" as "Hown_meta".
    { rewrite big_sepL_app. iFrame. }
    iAssert (([∗ list] pod0 ∈ before ++ after,
        own_spec_frag γ (PodV.key pod0)
          pod0.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod0.(PodV.Spec'))))%I
      with "[Hspec_before Hspec_after]" as "Hown_spec".
    { rewrite big_sepL_app. iFrame. }
    iCombine "Hown_meta Hown_spec" as "Hown_pods".
    iEval (rewrite -big_sepL_sep) in "Hown_pods".
    assert (Forall is_pod_alive pods) as Hstored_alive.
    { eapply local_pods_match_stored_alive_all; done. }
    assert (living_pods (before ++ after) = before ++ after) as Hliving.
    { unfold living_pods. apply filter_all. intros pod Hpod.
      rewrite Forall_forall in Hstored_alive. apply Hstored_alive.
      rewrite Hpods_decomp -list_elem_of_In.
      apply elem_of_app in Hpod as [Hpod|Hpod].
      - apply elem_of_app. left. exact Hpod.
      - apply elem_of_app. right. apply elem_of_cons. right. exact Hpod. }
    iAssert (own_occupied_pods γ (before ++ after))
      with "[Hoccupied_before Hoccupied_after]" as "Hoccupied_pods".
    { rewrite /own_occupied_pods big_sepL_app. iFrame. }
    assert (NoDup (PodV.key <$> (before ++ stored_pod :: after)))
      as Hdecomp_nodup.
    { rewrite -Hpods_decomp. exact Hstored_nodup. }
    iAssert (own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> (before ++ after))))
      with "[Hdelete_Hown_children]" as "Hown_children".
    { rewrite (list_to_set_pod_keys_remove before stored_pod after
        Hdecomp_nodup).
      rewrite -Hpods_decomp.
      iExact "Hdelete_Hown_children". }
    assert (desired_objects_reconciled set (before ++ after) pvcs)
      as Hdesired'.
    { apply (desired_objects_reconciled_remove_condemned set before
        stored_pod after pvcs);
        [rewrite -Hpods_decomp; exact Hdesired_reconciled
        |exact Hstored_member|exact Hstored_condemned]. }
    assert (match_distance set (before ++ after) pvcs <
        match_distance set pods pvcs) as Hdistance'.
    { rewrite Hpods_decomp.
      eapply match_distance_remove_condemned;
        [rewrite -Hpods_decomp; exact Hstored_members
        |exact Hstored_condemned|exact Hstored_pod_alive]. }
    assert (pods_progress_observed local_pods (before ++ after))
      as Hprogress'.
    { eapply pods_progress_observed_remove_local; done. }
    assert (match_distance set (before ++ after) pvcs <
        match_distance set local_pods initial_pvcs) as Hdistance_local by lia.
    assert (Forall (pod_has_int32_member_key set) (before ++ after))
      as Hmembers'.
    { apply (pod_members_remove set before stored_pod after).
      rewrite -Hpods_decomp. exact Hstored_members. }
    assert (NoDup (PodV.key <$> (before ++ after))) as Hnodup'.
    { apply (pod_keys_nodup_remove before stored_pod after Hdecomp_nodup). }
    wp_auto.
    iApply ("HΦ" $! false (before ++ after)
      (Some (PodV.key stored_pod,
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')))).
    rewrite /own_started_deletion /phase_after_deletion /=.
    iFrame. iPureIntro. split; first exact Hnot_desired.
    split; first lia.
    split; first exact Hmembers'.
    split; first exact Hnodup'.
    split; first exact Hdesired'.
    right. split; first done. split; first by eexists.
    right. split; done.
Qed.

Lemma wp_reconcileOutdatedPod γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (local_pods pods : list PodV.t)
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
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hlocal_pods_valid" ∷ ⌜ Forall PodV.valid local_pods ⌝ ∗
      "%Hlocal_pods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) local_pods ⌝ ∗
      "%Hlocal_pods_nodup" ∷
        ⌜ NoDup (PodV.key <$> local_pods) ⌝ ∗
      "%Hlocal_stored" ∷
        ⌜ local_pods_match_stored local_pods pods ⌝ ∗
      "%Hpending_empty" ∷
        ⌜ filter (pending_pod set) local_pods = [] ⌝ ∗
      "%Hdistance_le" ∷ ⌜
        match_distance set pods pvcs ≤
          match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hdesired_reconciled" ∷
        ⌜ desired_objects_reconciled set pods pvcs ⌝ ∗
      "%Hno_condemned" ∷
        ⌜ Forall (λ pod, ¬ pod_is_condemned set pod) pods ⌝
  }}}
    @! statefulset.reconcileOutdatedPod #set_l #pods_sl
  {{{ (pods' : list PodV.t) (deletion : option (KKey.t * types.UID.t)), RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;local_pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods' ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods')) ∗
      "Hstarted_deletion" ∷ own_started_deletion γ deletion ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        (phase_after_deletion phase deletion) ∗
      "%Hdeletion_desired" ∷ ⌜ match deletion with
        | None => True
        | Some (key, _) => key ∈ desired_pod_keys set
        end ⌝ ∗
      "%Hdistance" ∷ ⌜
        match_distance set pods' pvcs ≤
          match_distance set local_pods initial_pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      "%Hmissing_pods" ∷ ⌜
        list_to_set (C:=gset KKey.t) (missing_pod_keys set pods') =
          match deletion with
          | None => ∅
          | Some (key, _) => {[key]}
          end ⌝ ∗
      ⌜ (deletion = None ∧ current_state_matches set pods' pvcs) ∨
        (is_Some deletion ∧ pods_progress_observed local_pods pods' ∧
          match_distance set pods' pvcs <
            match_distance set local_pods initial_pvcs) ⌝
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
  assert (Forall (λ pod,
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
      local_pods) as Hlocal_name_len.
  { apply Forall_forall. intros pod Hpod.
    rewrite Forall_forall in Hlocal_pods_valid.
    apply pod_name_length_le_go_int_max_of_valid.
    exact (Hlocal_pods_valid pod Hpod). }
  pose proof (pod_names_nodup_of_key_nodup set local_pods
    Hlocal_pods_members Hlocal_pods_nodup) as Hlocal_names_nodup.
  pose proof (pending_pods_empty_alive set local_pods
    Hpending_empty Hlocal_pods_members) as Hlocal_alive.
  wp_apply (wp_largestOutdatedPod set_l pods_sl set ptrs local_pods
    dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
  { iPureIntro. split_and!; done. }
  iIntros (outdated_l) "(Hset & Hpods_sl & Hpods & %Houtdated)".
  destruct Houtdated as
    [[-> Hnone_local]|(idx & local_pod & Hptr_lookup & Hlocal_lookup &
      Hlocal_outdated)].
  - assert (Forall (λ pod, ¬ pod_is_outdated set pod) pods)
      as Hnone_stored.
    { eapply local_pods_match_stored_no_outdated; done. }
    assert (Forall (pod_has_int32_member_key set) pods)
      as Hstored_members.
    { eapply local_pods_match_stored_members; done. }
    assert (Forall is_pod_alive pods) as Hstored_alive.
    { eapply local_pods_match_stored_alive_all; done. }
    assert (match_distance set pods pvcs = 0%nat) as Hdistance_zero.
    { eapply desired_objects_reconciled_distance_zero; done. }
    iEval (rewrite big_sepL_sep) in "Hown_pods".
    iDestruct "Hown_pods" as "[Hown_meta Hown_spec]".
    iPoseProof (match_distance_zero_matches γ set pods pvcs
      ltac:(intros pod Hpod; rewrite Forall_forall in Hstored_alive;
        apply Hstored_alive; by rewrite -list_elem_of_In)
      with "Hown_meta") as "%Hzero_matches".
    assert (current_state_matches set pods pvcs) as Hmatches.
    { apply (proj1 Hzero_matches). exact Hdistance_zero. }
    iCombine "Hown_meta Hown_spec" as "Hown_pods".
    iEval (rewrite -big_sepL_sep) in "Hown_pods".
    assert (living_pods pods = pods) as Hliving.
    { unfold living_pods. apply filter_all.
      rewrite Forall_forall in Hstored_alive.
      intros pod Hpod. apply Hstored_alive.
      by rewrite -list_elem_of_In. }
    wp_auto.
    iApply ("HΦ" $! pods None).
    rewrite /own_started_deletion /phase_after_deletion /=.
    iFrame. iPureIntro. split; first done.
    split; first lia. split; first exact Hstored_members.
    split.
    { rewrite -(local_pods_match_stored_keys _ _ Hlocal_stored).
      exact Hlocal_pods_nodup. }
    split.
    { destruct Hdesired_reconciled as (Hmissing & _ & _).
      by rewrite Hmissing. }
    left. split; done.
  - pose proof (local_pods_match_stored_lookup
      local_pods pods idx local_pod Hlocal_stored Hlocal_lookup)
      as (stored_pod & Hstored_lookup & Hlocal_stored_pod).
    pose proof Hlocal_stored_pod as
      (Hlocal_key & Hlocal_uid & Hlocal_deletion & Hlocal_spec).
    assert (is_pod_alive local_pod) as Hlocal_pod_alive.
    { rewrite Forall_forall in Hlocal_alive. apply Hlocal_alive.
      apply list_elem_of_In. by apply list_elem_of_lookup_2 in Hlocal_lookup. }
    assert (is_pod_alive stored_pod) as Hstored_pod_alive.
    { apply (proj1
        (local_pod_matches_stored_alive _ _ Hlocal_stored_pod)).
      exact Hlocal_pod_alive. }
    assert (pod_is_outdated set stored_pod) as Hstored_outdated.
    { apply (proj1
        (local_pod_matches_stored_outdated set _ _
          Hlocal_stored_pod)).
      exact Hlocal_outdated. }
    assert (NoDup (PodV.key <$> pods)) as Hstored_nodup.
    { rewrite -(local_pods_match_stored_keys _ _ Hlocal_stored).
      exact Hlocal_pods_nodup. }
    assert (Forall (pod_has_int32_member_key set) pods)
      as Hstored_members.
    { eapply local_pods_match_stored_members; done. }
    iDestruct (big_sepL2_lookup_acc with "Hpods") as
      "[Hlocal_pod Hlocal_pod_restore]";
      [exact Hptr_lookup|exact Hlocal_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hlocal_pod") as
      "(%Houtdated_not_null & Hlocal_typemeta & Hlocal_meta &
        Hlocal_spec & Hlocal_status)".
    iPoseProof (PodV.deepown_l_restore _ _ _ Houtdated_not_null
      with "[$Hlocal_typemeta $Hlocal_meta $Hlocal_spec $Hlocal_status]")
      as "Hlocal_pod".
    wp_auto. wp_if_destruct; first contradiction.
    wp_apply (wp_isTerminating outdated_l local_pod dq_pods
      with "Hlocal_pod").
    iIntros (terminating) "[%Hterminating Hlocal_pod]".
    destruct terminating.
    { exfalso. apply (proj1 Hterminating eq_refl).
      exact Hlocal_pod_alive. }
    wp_auto.

    set before := take idx pods.
    set after := drop (S idx) pods.
    assert (pods = before ++ stored_pod :: after) as Hpods_decomp.
    { unfold before, after. symmetry.
      by apply take_drop_middle. }
    iEval (rewrite big_sepL_sep) in "Hown_pods".
    iDestruct "Hown_pods" as "[Hown_meta Hown_spec]".
    iEval (rewrite Hpods_decomp big_sepL_app big_sepL_cons) in
      "Hown_meta Hown_spec".
    iDestruct "Hown_meta" as
      "[Hmeta_before [Hstored_meta Hmeta_after]]".
    iDestruct "Hown_spec" as
      "[Hspec_before [Hstored_spec Hspec_after]]".
    iEval (rewrite /own_occupied_pods Hpods_decomp
      big_sepL_app big_sepL_cons) in "Hoccupied_pods".
    iDestruct "Hoccupied_pods" as
      "[Hoccupied_before [Hstored_occupied Hoccupied_after]]".
    assert (pod_has_int32_member_key set stored_pod) as Hstored_member.
    { rewrite Forall_forall in Hstored_members. apply Hstored_members.
      rewrite Hpods_decomp -list_elem_of_In.
      apply elem_of_app. right. by left. }
    pose proof (proj1 (pod_int32_member_outdated_iff set stored_pod
      Hstored_member) Hstored_outdated) as [Hdesired _].
    assert (PodV.key stored_pod ∈
        list_to_set (C:=gset KKey.t) (PodV.key <$> pods)) as Hkey_in.
    { apply elem_of_list_to_set. apply list_elem_of_fmap_2.
      by apply list_elem_of_lookup_2 in Hstored_lookup. }
    wp_apply (wp_deletePod γ model_l outdated_l
      local_pod stored_pod (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
      (list_to_set (PodV.key <$> pods)) phase dq_pods
      with "[$Hlocal_pod $Hstored_meta $Hstored_spec $Hstored_occupied
        $Hown_children $Hterminating_children_frag]").
    { iFrame "#". iPureIntro. split_and!; done. }
    iIntros "Hdelete". iNamedPrefix "Hdelete" "Hdelete_".
    iSpecialize ("Hlocal_pod_restore" with "Hdelete_Hpod").
      iRename "Hlocal_pod_restore" into "Hpods".
      iAssert (([∗ list] pod0 ∈ before ++ after,
          own_meta_frag γ (PodV.key pod0)
            pod0.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod0.(PodV.ObjectMeta')))%I
        with "[Hmeta_before Hmeta_after]" as "Hown_meta".
      { rewrite big_sepL_app. iFrame. }
      iAssert (([∗ list] pod0 ∈ before ++ after,
          own_spec_frag γ (PodV.key pod0)
            pod0.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod0.(PodV.Spec'))))%I
        with "[Hspec_before Hspec_after]" as "Hown_spec".
      { rewrite big_sepL_app. iFrame. }
      iCombine "Hown_meta Hown_spec" as "Hown_pods".
      iEval (rewrite -big_sepL_sep) in "Hown_pods".
      assert (Forall is_pod_alive pods) as Hstored_alive.
      { eapply local_pods_match_stored_alive_all; done. }
      assert (living_pods (before ++ after) = before ++ after) as Hliving.
      { unfold living_pods. apply filter_all. intros pod Hpod.
        rewrite Forall_forall in Hstored_alive. apply Hstored_alive.
        rewrite Hpods_decomp -list_elem_of_In.
        apply elem_of_app in Hpod as [Hpod|Hpod].
        - apply elem_of_app. left. exact Hpod.
        - apply elem_of_app. right. apply elem_of_cons. right. exact Hpod. }
      iAssert (own_occupied_pods γ (before ++ after))
        with "[Hoccupied_before Hoccupied_after]" as "Hoccupied_pods".
      { rewrite /own_occupied_pods big_sepL_app. iFrame. }
      assert (NoDup (PodV.key <$> (before ++ stored_pod :: after)))
        as Hdecomp_nodup.
      { rewrite -Hpods_decomp. exact Hstored_nodup. }
      iAssert (own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (list_to_set (PodV.key <$> (before ++ after))))
        with "[Hdelete_Hown_children]" as "Hown_children".
      { rewrite (list_to_set_pod_keys_remove before stored_pod after
          Hdecomp_nodup) -Hpods_decomp.
        iExact "Hdelete_Hown_children". }
      assert (match_distance set (before ++ after) pvcs <
          match_distance set pods pvcs) as Hdistance'.
      { rewrite Hpods_decomp.
        apply (match_distance_remove_outdated set before stored_pod after
          pvcs);
          [rewrite -Hpods_decomp; exact Hstored_members
          |exact Hdecomp_nodup|exact Hstored_outdated
          |exact Hstored_pod_alive]. }
      assert (pods_progress_observed local_pods (before ++ after))
        as Hprogress'.
      { eapply pods_progress_observed_remove_local; done. }
      assert (match_distance set (before ++ after) pvcs <
          match_distance set local_pods initial_pvcs) as Hdistance_local by lia.
      assert (Forall (pod_has_int32_member_key set) (before ++ after))
        as Hmembers'.
      { apply (pod_members_remove set before stored_pod after).
        rewrite -Hpods_decomp. exact Hstored_members. }
      assert (NoDup (PodV.key <$> (before ++ after))) as Hnodup'.
      { apply (pod_keys_nodup_remove before stored_pod after Hdecomp_nodup). }
      assert (list_to_set (C:=gset KKey.t)
          (missing_pod_keys set (before ++ after)) =
          {[PodV.key stored_pod]}) as Hmissing'.
      { apply (desired_objects_reconciled_remove_desired_missing_pod_keys
          set before stored_pod after pvcs).
        - rewrite -Hpods_decomp. exact Hdesired_reconciled.
        - exact Hdecomp_nodup.
        - exact Hdesired. }
      wp_auto.
      iApply ("HΦ" $! (before ++ after)
        (Some (PodV.key stored_pod,
          stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')))).
      rewrite /own_started_deletion /phase_after_deletion /=.
      iFrame. iPureIntro. split; first exact Hdesired.
      split; first lia.
      split; first exact Hmembers'.
      split; first exact Hnodup'.
      split; first exact Hmissing'. right.
      split; first by eexists. split; done.
Qed.

(* The composition of the three stages above. This uses the same logical
   starting state as the top-level progress theorem, after Get, owner filtering,
   and bad-name release have produced the local StatefulSet and Pod slice. *)
Lemma wp_reconcileReplicas_progress γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods : list PodV.t) (pvcs : list PersistentVolumeClaimV.t)
    dq_set dq_pods phase :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') phase ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys set pods,
        own_available_frag γ key) ∗
      "Hreserved_pvcs" ∷ ([∗ list] key ∈ missing_pvc_keys set pvcs,
        own_available_frag γ key) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods ⌝ ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hpending_empty" ∷ ⌜ filter (pending_pod set) pods = [] ⌝ ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement set ⌝
  }}}
    @! statefulset.reconcileReplicas #set_l #pods_sl
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t)
      (deletion : option (KKey.t * types.UID.t)),
      RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods' ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
          pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs' ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods')) ∗
      "Hreserved_pods" ∷ own_missing_pod_reservations γ set pods' ∗
      "Hreserved_pvcs" ∷ own_missing_pvc_reservations γ set pvcs' ∗
      "Hterminating_children_frag" ∷ own_terminating_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        (phase_after_deletion phase deletion) ∗
      "%Hdeletion_classified" ∷ ⌜ match deletion with
        | None => True
        | Some (key, _) => key ∈ desired_pod_keys set ∨
            key ∉ desired_pod_keys set
        end ⌝ ∗
      "%Hdistance" ∷ ⌜
        match_distance set pods' pvcs' ≤ match_distance set pods pvcs ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall
        (pod_has_int32_member_key set) pods' ⌝ ∗
      "%Hprogress" ∷ ⌜ progress_or_complete set pods pvcs pods' pvcs' ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_reconcileDesiredPods γ model_l set_l pods_sl set ptrs pods
    pvcs dq_set dq_pods phase with
    "[$Hset $Hpods_sl $Hpods $Hown_pods $Hoccupied_pods $Hown_pvcs
      $Hoccupied_pvcs $Hown_children $Hterminating_children_frag $Hreserved_pods
      $Hreserved_pvcs]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (continue_desired pods1 pvcs1)
    "(Hset & Hpods_sl & Hpods & Hown_pods & Hoccupied_pods &
      Hown_pvcs & Hoccupied_pvcs & Hown_children & Hterminating_children_frag &
      Hreserved_pods & Hreserved_pvcs & %Hdistance1 & %Hmembers1 & Hdesired_result)".
  iDestruct "Hdesired_result" as "[Hdesired_continue|Hdesired_stop]".
  - iDestruct "Hdesired_continue" as
      "(%Hcontinue_desired & %Hlocal_stored & %Hdesired_reconciled)".
    subst continue_desired. wp_auto.
    wp_apply (wp_reconcileCondemnedPod γ model_l set_l pods_sl set ptrs
      pods pods1 pvcs1 pvcs dq_set dq_pods phase with
      "[$Hset $Hpods_sl $Hpods $Hown_pods $Hoccupied_pods $Hown_pvcs
        $Hown_children $Hterminating_children_frag]").
    { iFrame "#". iPureIntro. split_and!.
      - exact Hset_valid.
      - exact Hpods_valid.
      - exact Hpods_members.
      - exact Hpods_nodup.
      - exact Hlocal_stored.
      - exact Hpending_empty.
      - exact Hdistance1.
      - exact Hdesired_reconciled. }
    iIntros (continue_condemned pods2 deletion2)
      "(Hset & Hpods_sl & Hpods & Hown_pods & Hoccupied_pods &
        Hown_pvcs & Hown_children & Hstarted_deletion &
        Hterminating_children_frag & %Hdeletion_retiring & %Hdistance2 &
        %Hmembers2 & %Hnodup2 & %Hdesired_reconciled2 & Hcondemned_result)".
    iDestruct "Hcondemned_result" as
      "[Hcondemned_continue|Hcondemned_stop]".
    + iDestruct "Hcondemned_continue" as
        "(%Hcontinue_condemned & %Hdeletion2 & %Hpods2 & %Hno_condemned)".
      subst continue_condemned. subst deletion2. subst pods2. wp_auto.
      iClear "Hstarted_deletion".
      wp_apply (wp_reconcileOutdatedPod γ model_l set_l pods_sl set ptrs
        pods pods1 pvcs1 pvcs dq_set dq_pods phase with
        "[$Hset $Hpods_sl $Hpods $Hown_pods $Hoccupied_pods $Hown_pvcs
          $Hown_children $Hterminating_children_frag]").
      { iFrame "#". iPureIntro. split_and!; done. }
      iIntros (pods3 deletion3)
        "(Hset & Hpods_sl & Hpods & Hown_pods & Hoccupied_pods &
          Hown_pvcs & Hown_children & Hstarted_deletion &
          Hterminating_children_frag & %Hdeletion_desired & %Hdistance3 &
          %Hmembers3 & %Hnodup3 & %Hmissing_pods3 & %Hprogress3)".
      iClear "Hreserved_pods".
      iAssert (own_missing_pod_reservations γ set pods3)
        with "[Hstarted_deletion]" as "Hreserved_pods".
      { rewrite /own_missing_pod_reservations Hmissing_pods3.
        destruct deletion3 as [[key uid]|]; simpl.
        - rewrite big_sepS_singleton /own_started_deletion /=.
          iRight. by iExists uid.
        - rewrite big_sepS_empty /own_started_deletion. done. }
      wp_auto. iApply ("HΦ" $! pods3 pvcs1 deletion3). iFrame.
      iPureIntro. split.
      { destruct deletion3 as [[key uid]|]; simpl in *; [by left|done]. }
      split; first exact Hdistance3.
      split; first exact Hmembers3.
      unfold progress_or_complete.
      destruct Hprogress3 as [[_ Hcomplete]|(_ & Hprogress)];
        [by left|by right].
    + iDestruct "Hcondemned_stop" as
        "(%Hcontinue_condemned & %Hdeletion2_some & %Hprogress2)".
      subst continue_condemned. wp_auto.
      iClear "Hstarted_deletion".
      iAssert (own_missing_pod_reservations γ set pods2)
        with "[Hreserved_pods]" as "Hreserved_pods".
      { destruct Hdesired_reconciled as (Hmissing1 & _ & _).
        destruct Hdesired_reconciled2 as (Hmissing2 & _ & _).
        rewrite /own_missing_pod_reservations Hmissing1 Hmissing2. iFrame. }
      iApply ("HΦ" $! pods2 pvcs1 deletion2). iFrame.
      iPureIntro. split.
      { destruct deletion2 as [[key uid]|]; simpl in *; [by right|done]. }
      split; first exact Hdistance2.
      split; first exact Hmembers2. exact Hprogress2.
  - iDestruct "Hdesired_stop" as
      "(%Hcontinue_desired & %Hprogress1)".
    subst continue_desired. wp_auto.
    iApply ("HΦ" $! pods1 pvcs1 None).
    rewrite /own_started_deletion /phase_after_deletion /=.
    iFrame. iPureIntro. split; first done.
    split; first exact Hdistance1.
    split; first exact Hmembers1. exact Hprogress1.
Qed.

End proof.
