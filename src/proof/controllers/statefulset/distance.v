From New.proof.controllers.statefulset Require Export pod.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
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

Lemma filter_filter_absorb {A} (P Q : A → Prop)
    `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} (xs : list A) :
  (∀ x, P x → Q x) →
  filter P (filter Q xs) = filter P xs.
Proof.
  intros HPQ.
  induction xs as [|x xs IH]; simpl; first done.
  rewrite !filter_cons.
  destruct (decide (P x)) as [HP|HnotP];
    destruct (decide (Q x)) as [HQ|HnotQ]; simpl.
  - rewrite (filter_cons_True P x (filter Q xs) HP).
    by rewrite IH.
  - exfalso. apply HnotQ. by apply HPQ.
  - rewrite (filter_cons_False P x (filter Q xs) HnotP).
    exact IH.
  - exact IH.
Qed.

Lemma NoDup_fmap_inj_on {A B} (f : A → B) (xs : list A) x y :
  NoDup (f <$> xs) →
  x ∈ xs →
  y ∈ xs →
  f x = f y →
  x = y.
Proof.
  intros Hnodup Hx Hy Hf.
  apply list_elem_of_lookup_1 in Hx as (i & Hx).
  apply list_elem_of_lookup_1 in Hy as (j & Hy).
  assert ((f <$> xs) !! i = Some (f x)) as Hfx.
  { by rewrite list_lookup_fmap Hx. }
  assert ((f <$> xs) !! j = Some (f x)) as Hfy.
  { rewrite list_lookup_fmap Hy. by rewrite Hf. }
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hfx Hfy) as ->.
  rewrite Hx in Hy. by inversion Hy.
Qed.

Lemma list_to_set_fmap_filter_difference {A B}
    `{Countable B} (f : A → B) (P : A → Prop)
    `{!∀ x, Decision (P x)} (xs : list A) :
  NoDup (f <$> xs) →
  list_to_set (C:=gset B) (f <$> xs) ∖
      list_to_set (C:=gset B) (f <$> filter (λ x, ¬ P x) xs) =
    list_to_set (C:=gset B) (f <$> filter P xs).
Proof.
  intros Hnodup. apply set_eq. intros key.
  rewrite elem_of_difference !elem_of_list_to_set.
  split.
  - intros [Hall Hnot_bad].
    apply list_elem_of_fmap_1 in Hall as (x & -> & Hx).
    apply list_elem_of_fmap_2.
    apply list_elem_of_filter. split; last exact Hx.
    destruct (decide (P x)) as [HP|HnotP]; first done.
    exfalso. apply Hnot_bad. apply list_elem_of_fmap_2.
    apply list_elem_of_filter. split; done.
  - intros Hgood. split.
    + apply list_elem_of_fmap_1 in Hgood as (x & -> & Hx).
      apply list_elem_of_filter in Hx as [_ Hx].
      by apply list_elem_of_fmap_2.
    + intros Hbad.
      apply list_elem_of_fmap_1 in Hgood as
        (x & Hkey_x & Hx_good).
      apply list_elem_of_fmap_1 in Hbad as
        (y & Hkey_y & Hy_bad).
      apply list_elem_of_filter in Hx_good as [HPx Hx].
      apply list_elem_of_filter in Hy_bad as [HnotPy Hy].
      assert (x = y) as ->.
      { eapply NoDup_fmap_inj_on; try exact Hnodup; try done.
        exact (eq_trans (eq_sym Hkey_x) Hkey_y). }
      contradiction.
Qed.

Lemma Forall_fmap_list_to_set {A B} `{Countable B}
    (f : A → B) (xs : list A) :
  Forall (λ x, f x ∈ list_to_set (C:=gset B) (f <$> xs)) xs.
Proof.
  induction xs as [|x xs IH]; constructor.
  - rewrite elem_of_list_to_set. left.
  - eapply Forall_impl; last exact IH.
    intros y Hy. rewrite !elem_of_list_to_set in Hy |- *.
    right. exact Hy.
Qed.

Lemma statefulset_replicas_le_go_int32_max sts :
  (statefulset_replicas sts ≤ go_int32_max_nat)%nat.
Proof.
  unfold statefulset_replicas.
  destruct sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') as
    [replicas|].
  - unfold sint.nat, go_int32_max_nat.
    destruct (decide (0 ≤ sint.Z replicas)%Z) as
      [Hnonnegative|Hnegative].
    + apply Z2Nat.inj_le.
      * exact Hnonnegative.
      * unfold go_int32_max. lia.
      * unfold go_int32_max.
        pose proof (word.signed_range replicas).
        lia.
    + destruct (sint.Z replicas); simpl in *; lia.
  - unfold go_int32_max_nat.
    assert (0 ≤ go_int32_max)%Z as Hmax_nonnegative.
    { unfold go_int32_max. lia. }
    pose proof (Z2Nat.inj_le 1 go_int32_max ltac:(lia)
      Hmax_nonnegative) as Hbound.
    apply (proj1 Hbound). unfold go_int32_max. lia.
Qed.

Definition pod_has_int32_member_key
    (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  pod_has_int32_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').

#[global] Instance pod_has_int32_member_key_decision sts pod :
    Decision (pod_has_int32_member_key sts pod).
Proof. unfold pod_has_int32_member_key. apply _. Defined.

Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).

Definition needed_pods sts pods : list PodV.t :=
  filter (λ pod, pod_key_is_desired sts (PodV.key pod)) pods.

Definition outdated_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_match sts pod) (needed_pods sts pods).

Definition bad_name_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_has_int32_member_key sts pod) pods.

Definition condemned_pods sts pods : list PodV.t :=
  filter (λ pod,
    pod_has_int32_member_key sts pod ∧
    ¬ pod_key_is_desired sts (PodV.key pod)) pods.

(* The progress metric gives an outdated desired Pod cost 2 and a missing
   desired Pod cost 1, so deleting one outdated Pod strictly reduces the
   distance even though the desired replacement Pod is created by a later run.
   Once the delete only sets DeletionTimestamp, the Pod is no longer alive and
   should not keep contributing to the outdated-Pod distance. *)
Definition pod_distance sts pods : nat :=
  length (missing_pod_keys sts pods) +
  2 * length (filter is_pod_alive (outdated_pods sts pods)) +
  length (filter is_pod_alive (condemned_pods sts pods)) +
  length (bad_name_pods sts pods).

Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) : list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs).

Definition match_distance sts pods pvcs : nat :=
  pod_distance sts pods + pvc_distance sts pvcs.

Definition statefulset_storage_view (sts : StatefulSetV.t) :
    ObjectMetaV.t * StatefulSetSpecV.t :=
  (ObjectMetaV.without_resource_version
    sts.(StatefulSetV.ObjectMeta'), sts.(StatefulSetV.Spec')).

Definition pod_view_meta
    (view : ObjectMetaV.t * ObjectSpecV.t) : ObjectMetaV.t := view.1.

Definition pod_view_key
    (view : ObjectMetaV.t * ObjectSpecV.t) : KKey.t :=
  PodV.meta_key (pod_view_meta view).

Definition pod_view_alive
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  (pod_view_meta view).(ObjectMetaV.DeletionTimestamp') = None.

#[global] Instance pod_view_alive_decision view :
    Decision (pod_view_alive view).
Proof. unfold pod_view_alive. apply _. Defined.

Definition pod_view_has_member_key sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  (pod_view_meta view).(ObjectMetaV.Namespace') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  pod_has_int32_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (pod_view_meta view).(ObjectMetaV.Name').

#[global] Instance pod_view_has_member_key_decision sts view :
    Decision (pod_view_has_member_key sts view).
Proof.
  unfold pod_view_has_member_key. apply _.
Defined.

Definition pod_view_key_is_desired sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  pod_view_key view ∈ desired_pod_keys sts.

#[global] Instance pod_view_key_is_desired_decision sts view :
    Decision (pod_view_key_is_desired sts view).
Proof. unfold pod_view_key_is_desired. apply _. Defined.

Definition pod_view_identity_matches sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  match parse_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (pod_view_meta view).(ObjectMetaV.Name'),
    (pod_view_meta view).(ObjectMetaV.Labels') with
  | Some ordinal, Some labels =>
      (ordinal <= go_int32_max_nat)%nat ∧
      (pod_view_meta view).(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      labels !! statefulset_pod_name_label =
        Some (pod_view_meta view).(ObjectMetaV.Name') ∧
      labels !! pod_index_label = Some (decimal_string ordinal)
  | _, _ => False
  end.

Definition pod_view_storage_matches sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  match view.2 with
  | ObjectSpecV.PodSpec spec =>
      match parse_pod_ordinal
          (pod_view_meta view).(ObjectMetaV.Name') with
      | Some ordinal =>
          (ordinal <= go_int32_max_nat)%nat ∧
          Forall
            (pod_volume_claim_matches
              (pod_volumes_map_of_list spec.(PodSpecV.Volumes'))
              sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
            (pvc_claim_template_names sts)
      | None => False
      end
  | _ => False
  end.

Definition pod_view_immutable_matches sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  match view.2 with
  | ObjectSpecV.PodSpec spec =>
      spec.(PodSpecV.Hostname') =
        (pod_view_meta view).(ObjectMetaV.Name') ∧
      spec.(PodSpecV.Subdomain') =
        sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
      pod_view_storage_matches sts view ∧
      without_statefulset_fields spec =
        without_statefulset_fields
          sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(
            PodTemplateSpecV.Spec')
  | _ => False
  end.

Definition pod_view_match sts
    (view : ObjectMetaV.t * ObjectSpecV.t) : Prop :=
  pod_view_identity_matches sts view ∧
  pod_view_immutable_matches sts view.

#[global] Instance pod_view_identity_matches_decision sts view :
    Decision (pod_view_identity_matches sts view).
Proof.
  unfold pod_view_identity_matches.
  destruct parse_member_name,
    ((pod_view_meta view).(ObjectMetaV.Labels')); apply _.
Defined.

#[global] Instance pod_view_storage_matches_decision sts view :
    Decision (pod_view_storage_matches sts view).
Proof.
  unfold pod_view_storage_matches.
  destruct view as [meta spec]. simpl.
  destruct spec; try (right; tauto).
  destruct parse_pod_ordinal; apply _.
Defined.

#[global] Instance pod_view_immutable_matches_decision sts view :
    Decision (pod_view_immutable_matches sts view).
Proof.
  unfold pod_view_immutable_matches.
  destruct view as [meta spec]. simpl.
  destruct spec; try (right; tauto).
  destruct (decide
    (p.(PodSpecV.Hostname') = meta.(ObjectMetaV.Name')))
    as [Hhostname|Hhostname].
  2: { right. intros (H & _). contradiction. }
  destruct (decide
    (p.(PodSpecV.Subdomain') =
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName')))
    as [Hsubdomain|Hsubdomain].
  2: { right. intros (_ & H & _). contradiction. }
  destruct (decide (pod_view_storage_matches sts
    (meta, ObjectSpecV.PodSpec p))) as [Hstorage|Hstorage].
  2: { right. intros (_ & _ & H & _). contradiction. }
  left. split_and!; try done.
Defined.

#[global] Instance pod_view_match_decision sts view :
    Decision (pod_view_match sts view).
Proof. unfold pod_view_match. apply _. Defined.

Definition needed_pod_views sts views :
    list (ObjectMetaV.t * ObjectSpecV.t) :=
  filter (pod_view_key_is_desired sts) views.

Definition outdated_pod_views sts views :
    list (ObjectMetaV.t * ObjectSpecV.t) :=
  filter (λ view, ¬ pod_view_match sts view)
    (needed_pod_views sts views).

Definition bad_name_pod_views sts views :
    list (ObjectMetaV.t * ObjectSpecV.t) :=
  filter (λ view, ¬ pod_view_has_member_key sts view) views.

Definition condemned_pod_views sts views :
    list (ObjectMetaV.t * ObjectSpecV.t) :=
  filter (λ view,
    pod_view_has_member_key sts view ∧
    ¬ pod_view_key_is_desired sts view) views.

Definition pod_view_distance sts views : nat :=
  length (filter
    (λ key, key ∉ pod_view_key <$> views) (desired_pod_keys sts)) +
  2 * length (filter pod_view_alive (outdated_pod_views sts views)) +
  length (filter pod_view_alive (condemned_pod_views sts views)) +
  length (bad_name_pod_views sts views).

Lemma pod_view_desired_is_member sts view :
  pod_view_key_is_desired sts view →
  pod_view_has_member_key sts view.
Proof.
  intros Hdesired.
  unfold pod_view_key_is_desired, desired_pod_keys in Hdesired.
  apply list_elem_of_fmap_1 in Hdesired as
    (ordinal & Hkey & Hordinal).
  unfold pod_view_has_member_key, pod_has_int32_member_name.
  split.
  - apply (f_equal KKey.Namespace') in Hkey. exact Hkey.
  - exists ordinal. split.
    + unfold desired_ordinals in Hordinal.
      apply elem_of_seq in Hordinal as [_ Hordinal].
      pose proof (statefulset_replicas_le_go_int32_max sts).
      lia.
    + apply (f_equal KKey.Name') in Hkey. exact Hkey.
Qed.

Lemma pod_key_desired_is_int32_member sts pod :
  pod_key_is_desired sts (PodV.key pod) →
  pod_has_int32_member_key sts pod.
Proof.
  intros Hdesired.
  unfold pod_key_is_desired, desired_pod_keys in Hdesired.
  apply list_elem_of_fmap_1 in Hdesired as
    (ordinal & Hkey & Hordinal).
  unfold pod_has_int32_member_key, pod_has_int32_member_name.
  split.
  - apply (f_equal KKey.Namespace') in Hkey. exact Hkey.
  - exists ordinal. split.
    + unfold desired_ordinals in Hordinal.
      apply elem_of_seq in Hordinal as [_ Hordinal].
      pose proof (statefulset_replicas_le_go_int32_max sts).
      lia.
    + apply (f_equal KKey.Name') in Hkey. exact Hkey.
Qed.

Lemma missing_pod_keys_filter_int32_members sts pods :
  missing_pod_keys sts (filter (pod_has_int32_member_key sts) pods) =
  missing_pod_keys sts pods.
Proof.
  assert (Hactual : ∀ key,
      key ∈ desired_pod_keys sts →
      (key ∈ PodV.key <$> pods ↔
       key ∈ PodV.key <$> filter (pod_has_int32_member_key sts) pods)).
  { intros key Hdesired. split.
    - intros Hactual.
      apply list_elem_of_fmap_1 in Hactual as (pod & Hkey & Hpod).
      rewrite Hkey. apply list_elem_of_fmap_2.
      apply list_elem_of_filter. split;
        last exact Hpod.
      apply pod_key_desired_is_int32_member.
      unfold pod_key_is_desired. rewrite -Hkey. exact Hdesired.
    - intros Hactual.
      apply list_elem_of_fmap_1 in Hactual as (pod & Hkey & Hpod).
      apply list_elem_of_filter in Hpod as [_ Hpod].
      rewrite Hkey. by apply list_elem_of_fmap_2. }
  unfold missing_pod_keys.
  induction (desired_pod_keys sts) as [|key keys IH]; simpl; first done.
  assert (Hactual_tail : ∀ key', key' ∈ keys →
      (key' ∈ PodV.key <$> pods ↔
       key' ∈ PodV.key <$> filter (pod_has_int32_member_key sts) pods)).
  { intros key' Hkey'. apply Hactual. by right. }
  specialize (IH Hactual_tail).
  assert (Hactual_head := Hactual key ltac:(left)).
  rewrite !filter_cons.
  destruct (decide
      (key ∉ PodV.key <$> filter (pod_has_int32_member_key sts) pods)) as
      [Hnot_member|Hin_member];
    destruct (decide (key ∉ PodV.key <$> pods)) as
      [Hnot_all|Hin_all]; simpl.
  - f_equal. exact IH.
  - exfalso. apply Hin_all.
    intros Hall. apply Hnot_member. by apply (proj1 Hactual_head).
  - exfalso. apply Hin_member.
    intros Hfiltered. apply Hnot_all. by apply (proj2 Hactual_head).
  - exact IH.
Qed.

Lemma pod_view_distance_filter_members sts views :
  pod_view_distance sts views =
    (pod_view_distance sts
      (filter (pod_view_has_member_key sts) views) +
    length (filter (λ view, ¬ pod_view_has_member_key sts view) views))%nat.
Proof.
  set member_views := filter (pod_view_has_member_key sts) views.
  assert (Hactual : ∀ key,
      key ∈ desired_pod_keys sts →
      (key ∈ pod_view_key <$> views ↔
       key ∈ pod_view_key <$> member_views)).
  { intros key Hdesired. split.
    - intros Hactual.
      apply list_elem_of_fmap_1 in Hactual as
        (view & Hkey & Hview).
      rewrite Hkey. apply list_elem_of_fmap_2.
      unfold member_views.
      apply list_elem_of_filter. split; last exact Hview.
      apply pod_view_desired_is_member.
      unfold pod_view_key_is_desired. rewrite -Hkey. exact Hdesired.
    - intros Hactual.
      apply list_elem_of_fmap_1 in Hactual as
        (view & Hkey & Hview).
      rewrite Hkey. apply list_elem_of_fmap_2.
      unfold member_views in Hview.
      apply list_elem_of_filter in Hview as [_ Hview]. exact Hview. }
  assert (Hmissing :
      filter (λ key, key ∉ pod_view_key <$> member_views)
        (desired_pod_keys sts) =
      filter (λ key, key ∉ pod_view_key <$> views)
        (desired_pod_keys sts)).
  { induction (desired_pod_keys sts) as [|key keys IH]; simpl; first done.
    assert (Hactual_tail : ∀ key', key' ∈ keys →
        (key' ∈ pod_view_key <$> views ↔
         key' ∈ pod_view_key <$> member_views)).
    { intros key' Hkey'. apply Hactual. by right. }
    specialize (IH Hactual_tail).
    assert (Hactual_head := Hactual key ltac:(left)).
    rewrite !filter_cons.
    destruct (decide (key ∉ pod_view_key <$> member_views)) as
      [Hnot_member|Hin_member];
      destruct (decide (key ∉ pod_view_key <$> views)) as
      [Hnot_all|Hin_all]; simpl.
    - by rewrite IH.
    - exfalso. apply Hin_all.
      intros Hall. apply Hnot_member. by apply (proj1 Hactual_head).
    - exfalso. apply Hin_member.
      intros Hfiltered. apply Hnot_all. by apply (proj2 Hactual_head).
    - exact IH. }
  assert (Hneeded : needed_pod_views sts member_views =
      needed_pod_views sts views).
  { unfold needed_pod_views, member_views.
    apply filter_filter_absorb.
    exact (pod_view_desired_is_member sts). }
  assert (Houtdated : outdated_pod_views sts member_views =
      outdated_pod_views sts views).
  { unfold outdated_pod_views. by rewrite Hneeded. }
  assert (Hcondemned : condemned_pod_views sts member_views =
      condemned_pod_views sts views).
  { unfold condemned_pod_views, member_views.
    apply filter_filter_absorb. intros view [Hmember _]. exact Hmember. }
  assert (Hbad : bad_name_pod_views sts member_views = []).
  { unfold bad_name_pod_views, member_views.
    apply filter_none. intros view Hview Hnot_member.
    apply list_elem_of_filter in Hview as [Hmember _]. contradiction. }
  unfold pod_view_distance.
  rewrite Hmissing Houtdated Hcondemned Hbad.
  simpl. unfold bad_name_pod_views. lia.
Qed.

Lemma pod_storage_view_observations pod :
  pod_view_key (pod_storage_view pod) = PodV.key pod ∧
  (pod_view_alive (pod_storage_view pod) ↔ is_pod_alive pod) ∧
  (∀ sts,
    (pod_view_has_member_key sts (pod_storage_view pod) ↔
      pod_has_int32_member_key sts pod) ∧
    (pod_view_key_is_desired sts (pod_storage_view pod) ↔
      pod_key_is_desired sts (PodV.key pod)) ∧
    (pod_view_match sts (pod_storage_view pod) ↔ pod_match sts pod)).
Proof.
  destruct pod as [typemeta meta spec status].
  destruct meta; simpl.
  split_and!; done.
Qed.

Lemma pod_distance_as_storage_views sts pods :
  pod_distance sts pods =
    pod_view_distance sts (pod_storage_view <$> pods).
Proof.
  pose proof (λ pod, pod_storage_view_observations pod) as Hobs.
  assert (Hkeys : pod_view_key <$> (pod_storage_view <$> pods) =
      PodV.key <$> pods).
  { induction pods as [|pod pods IH]; simpl; first done.
    f_equal. exact IH. }
  assert (Hneeded :
      needed_pod_views sts (pod_storage_view <$> pods) =
        pod_storage_view <$> needed_pods sts pods).
  { apply filter_fmap_comm.
    intros pod.
    pose proof ((proj2 (proj2 (Hobs pod))) sts) as Hfacts.
    tauto. }
  assert (Houtdated :
      outdated_pod_views sts (pod_storage_view <$> pods) =
        pod_storage_view <$> outdated_pods sts pods).
  { unfold outdated_pod_views, outdated_pods.
    rewrite Hneeded.
    apply filter_fmap_comm.
    intros pod.
    pose proof ((proj2 (proj2 (Hobs pod))) sts) as Hfacts.
    tauto. }
  assert (Hcondemned :
      condemned_pod_views sts (pod_storage_view <$> pods) =
        pod_storage_view <$> condemned_pods sts pods).
  { unfold condemned_pod_views, condemned_pods.
    apply filter_fmap_comm. intros pod.
    pose proof ((proj2 (proj2 (Hobs pod))) sts) as Hpod.
    tauto. }
  assert (Hbad :
      bad_name_pod_views sts (pod_storage_view <$> pods) =
        pod_storage_view <$> bad_name_pods sts pods).
  { unfold bad_name_pod_views, bad_name_pods.
    apply filter_fmap_comm. intros pod.
    pose proof ((proj2 (proj2 (Hobs pod))) sts) as Hpod.
    tauto. }
  assert (Halive_outdated :
      filter pod_view_alive
        (outdated_pod_views sts (pod_storage_view <$> pods)) =
      pod_storage_view <$>
        filter is_pod_alive (outdated_pods sts pods)).
  { rewrite Houtdated. apply filter_fmap_comm.
    intros pod. symmetry. exact (proj1 (proj2 (Hobs pod))). }
  assert (Halive_condemned :
      filter pod_view_alive
        (condemned_pod_views sts (pod_storage_view <$> pods)) =
      pod_storage_view <$>
        filter is_pod_alive (condemned_pods sts pods)).
  { rewrite Hcondemned. apply filter_fmap_comm.
    intros pod. symmetry. exact (proj1 (proj2 (Hobs pod))). }
  unfold pod_distance, pod_view_distance.
  rewrite Hkeys Halive_outdated Halive_condemned Hbad !map_length.
  done.
Qed.

Lemma pod_storage_view_filter_int32_members sts (pods : list PodV.t) :
  pod_storage_view <$> filter (pod_has_int32_member_key sts) pods =
  filter (pod_view_has_member_key sts) (pod_storage_view <$> pods).
Proof.
  symmetry. apply filter_fmap_comm. intros pod.
  pose proof (pod_storage_view_observations pod) as Hobs.
  exact (proj1 ((proj2 (proj2 Hobs)) sts)).
Qed.

Lemma pod_distance_filter_int32_members sts pods :
  pod_distance sts pods =
    (pod_distance sts (filter (pod_has_int32_member_key sts) pods) +
    length (bad_name_pods sts pods))%nat.
Proof.
  rewrite !pod_distance_as_storage_views.
  rewrite pod_storage_view_filter_int32_members.
  rewrite pod_view_distance_filter_members.
  unfold bad_name_pods.
  assert (filter (λ view, ¬ pod_view_has_member_key sts view)
      (pod_storage_view <$> pods) =
    pod_storage_view <$>
      filter (λ pod, ¬ pod_has_int32_member_key sts pod) pods) as Hbad.
  { apply filter_fmap_comm. intros pod.
    pose proof (pod_storage_view_observations pod) as Hobs.
    pose proof (proj1 ((proj2 (proj2 Hobs)) sts)) as Hmember.
    tauto. }
  rewrite Hbad map_length. done.
Qed.

Lemma filter_int32_member_names_eq sts pods :
  Forall
    (λ pod,
      pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) pods →
  filter
    (λ pod,
      pod_has_int32_member_name
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods =
  filter (pod_has_int32_member_key sts) pods.
Proof.
  intros Hnamespaces.
  induction Hnamespaces as [|pod pods Hnamespace Hnamespaces IH];
    simpl; first done.
  rewrite !filter_cons.
  destruct (decide (pod_has_int32_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [Hname|Hname];
    destruct (decide (pod_has_int32_member_key sts pod)) as
      [Hmember|Hmember]; simpl.
  - by rewrite IH.
  - exfalso. apply Hmember. split; done.
  - exfalso. apply Hname. exact (proj2 Hmember).
  - exact IH.
Qed.

Lemma filter_bad_int32_member_names_eq sts pods :
  Forall
    (λ pod,
      pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) pods →
  filter
    (λ pod,
      ¬ pod_has_int32_member_name
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods =
  bad_name_pods sts pods.
Proof.
  intros Hnamespaces.
  unfold bad_name_pods.
  induction Hnamespaces as [|pod pods Hnamespace Hnamespaces IH];
    simpl; first done.
  rewrite !filter_cons.
  destruct (decide (¬ pod_has_int32_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [Hname|Hname];
    destruct (decide (¬ pod_has_int32_member_key sts pod)) as
      [Hmember|Hmember]; simpl.
  - by rewrite IH.
  - exfalso. apply Hmember. intros Hactual.
    apply Hname. exact (proj2 Hactual).
  - exfalso. apply Hname. intros Hgood_name.
    apply Hmember. split; done.
  - exact IH.
Qed.

Lemma pod_view_distance_perm sts views1 views2 :
  views1 ≡ₚ views2 →
  pod_view_distance sts views1 = pod_view_distance sts views2.
Proof.
  intros Hperm.
  assert (Hkeys : pod_view_key <$> views1 ≡ₚ
      pod_view_key <$> views2) by (apply Permutation_map; exact Hperm).
  assert (Hmissing :
      filter (λ key, key ∉ pod_view_key <$> views1)
        (desired_pod_keys sts) =
      filter (λ key, key ∉ pod_view_key <$> views2)
        (desired_pod_keys sts)).
  { induction (desired_pod_keys sts) as [|key keys IH]; simpl; first done.
    rewrite !filter_cons.
    destruct (decide (key ∉ pod_view_key <$> views1)) as [Hnot1|Hin1];
      destruct (decide (key ∉ pod_view_key <$> views2)) as [Hnot2|Hin2];
      simpl.
    - by rewrite IH.
    - exfalso. apply Hin2. rewrite -Hkeys. exact Hnot1.
    - exfalso. apply Hin1. rewrite Hkeys. exact Hnot2.
    - exact IH. }
  assert (Houtdated : outdated_pod_views sts views1 ≡ₚ
      outdated_pod_views sts views2).
  { apply perm_filter. apply perm_filter. exact Hperm. }
  assert (Hcondemned : condemned_pod_views sts views1 ≡ₚ
      condemned_pod_views sts views2).
  { apply perm_filter. exact Hperm. }
  assert (Hbad : bad_name_pod_views sts views1 ≡ₚ
      bad_name_pod_views sts views2).
  { apply perm_filter. exact Hperm. }
  unfold pod_view_distance.
  rewrite Hmissing.
  pose proof (Permutation_length (perm_filter pod_view_alive _ _ Houtdated))
    as Houtdated_len.
  pose proof (Permutation_length (perm_filter pod_view_alive _ _ Hcondemned))
    as Hcondemned_len.
  pose proof (Permutation_length Hbad) as Hbad_len.
  lia.
Qed.

Lemma match_distance_storage_view_perm sts pods1 pods2 pvcs :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  match_distance sts pods1 pvcs = match_distance sts pods2 pvcs.
Proof.
  intros Hperm.
  unfold match_distance.
  rewrite !pod_distance_as_storage_views.
  by rewrite (pod_view_distance_perm _ _ _ Hperm).
Qed.

Definition pods_match sts pods : Prop :=
  PodV.key <$> pods ≡ₚ desired_pod_keys sts ∧
  Forall is_pod_alive pods ∧
  Forall (pod_match sts) pods.

Definition pvcs_match sts (pvcs : list PersistentVolumeClaimV.t) : Prop :=
  ∀ key, key ∈ desired_pvc_keys sts →
    key ∈ (PersistentVolumeClaimV.key <$> pvcs).

Definition current_state_matches sts pods pvcs : Prop :=
  pods_match sts pods ∧ pvcs_match sts pvcs.

Lemma match_distance_zero_matches γ sts pods pvcs :
  (∀ pod, pod ∈ pods → is_pod_alive pod) →
  ([∗ list] pod ∈ pods, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) -∗
  ⌜ match_distance sts pods pvcs = 0%nat ↔ current_state_matches sts pods pvcs ⌝.
Proof.
  iIntros (Hpods_alive) "Hpod_meta_frags".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hpod_meta_frags") as "%Hpods_nodup".
  iPureIntro.
  assert (Hdesired_pods_nodup : NoDup (desired_pod_keys sts)).
  { unfold desired_pod_keys, desired_ordinals.
    apply NoDup_fmap_2.
    - intros ordinal1 ordinal2 Hkey.
      apply (f_equal KKey.Name') in Hkey.
      simpl in Hkey.
      unfold desired_pod_name in Hkey.
      simpl in Hkey.
      apply app_inv_head in Hkey.
      inversion Hkey as [Hdecimal].
      by apply decimal_string_inj in Hdecimal.
    - apply NoDup_seq. }
  split.
  - intros Hdist.
    unfold match_distance, pod_distance, pvc_distance in Hdist.
    assert (Hmissing_pods : length (missing_pod_keys sts pods) = 0%nat) by lia.
    assert (Halive_outdated_pods :
        length (filter is_pod_alive (outdated_pods sts pods)) = 0%nat) by lia.
    assert (Hbad_name_pods : length (bad_name_pods sts pods) = 0%nat) by lia.
    assert (Halive_condemned_pods :
        length (filter is_pod_alive (condemned_pods sts pods)) = 0%nat) by lia.
    assert (Hmissing_pvcs : length (missing_pvc_keys sts pvcs) = 0%nat) by lia.
    assert (Hpod_good_name : ∀ pod,
        pod ∈ pods → pod_has_int32_member_key sts pod).
    { intros pod Hpod.
      destruct (decide (pod_has_int32_member_key sts pod)) as [Hgood|Hbad]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ pod, ¬ pod_has_int32_member_key sts pod) pods pod);
        [exact Hbad_name_pods|exact Hpod|exact Hbad]. }
    assert (Hdesired_pod_actual : ∀ key,
        key ∈ desired_pod_keys sts → key ∈ PodV.key <$> pods).
    { intros key Hdesired.
      destruct (decide (key ∈ PodV.key <$> pods)) as [Hactual|Hnot_actual]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts) key);
        [exact Hmissing_pods|exact Hdesired|exact Hnot_actual]. }
    assert (Hactual_pod_desired : ∀ pod,
        pod ∈ pods → pod_key_is_desired sts (PodV.key pod)).
    { intros pod Hpod.
      destruct (decide (pod_key_is_desired sts (PodV.key pod))) as [Hdesired|Hnot_desired]; [done|].
      exfalso.
      assert (Hpod_condemned : pod ∈ condemned_pods sts pods).
      { unfold condemned_pods.
        apply list_elem_of_filter. split; [split; [by apply Hpod_good_name|exact Hnot_desired]|exact Hpod]. }
      eapply (filter_length_zero_not_elem
        is_pod_alive (condemned_pods sts pods) pod);
        [exact Halive_condemned_pods|exact Hpod_condemned|by apply Hpods_alive]. }
    assert (Hpods_perm : PodV.key <$> pods ≡ₚ desired_pod_keys sts).
    { apply NoDup_Permutation; [exact Hpods_nodup|exact Hdesired_pods_nodup|].
      intros key. split.
      - intros Hactual.
        apply list_elem_of_fmap_1 in Hactual as (pod & Hkey_eq & Hpod).
        rewrite Hkey_eq. by apply Hactual_pod_desired.
      - intros Hdesired. by apply Hdesired_pod_actual. }
    split.
    + split; [exact Hpods_perm|].
      split.
      * apply Forall_forall. intros pod Hpod.
        rewrite <- list_elem_of_In in Hpod.
        by apply Hpods_alive.
      * apply Forall_forall. intros pod Hpod.
        rewrite <- list_elem_of_In in Hpod.
        destruct (decide (pod_match sts pod)) as [Hmatch|Hnot_match]; [exact Hmatch|].
        exfalso.
        assert (Hpod_needed : pod ∈ needed_pods sts pods).
        { unfold needed_pods.
          apply list_elem_of_filter. split; [by apply Hactual_pod_desired|exact Hpod]. }
        assert (Hpod_outdated : pod ∈ outdated_pods sts pods).
        { unfold outdated_pods.
          apply list_elem_of_filter. split; [exact Hnot_match|exact Hpod_needed]. }
        eapply (filter_length_zero_not_elem
          is_pod_alive
          (outdated_pods sts pods) pod);
          [exact Halive_outdated_pods|exact Hpod_outdated|].
        by apply Hpods_alive.
    + intros key Hdesired.
      destruct (decide (key ∈ PersistentVolumeClaimV.key <$> pvcs)) as [Hactual|Hnot_actual]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts) key);
        [exact Hmissing_pvcs|exact Hdesired|exact Hnot_actual].
  - intros [[Hpods_perm [Hpods_alive_forall Hpods_match_forall]] Hpvcs_match].
    unfold match_distance, pod_distance, pvc_distance.
    assert (Hmissing_pods_nil : missing_pod_keys sts pods = []).
    { unfold missing_pod_keys.
      apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual.
      rewrite Hpods_perm. exact Hdesired. }
    assert (Houtdated_pods_nil : outdated_pods sts pods = []).
    { unfold outdated_pods.
      apply filter_none. intros pod Hpod Hnot_match.
      rewrite Forall_forall in Hpods_match_forall.
      unfold needed_pods in Hpod.
      apply list_elem_of_filter in Hpod as [_ Hpod].
      rewrite list_elem_of_In in Hpod.
      exact (Hnot_match (Hpods_match_forall pod Hpod)). }
    assert (Hbad_name_pods_nil : bad_name_pods sts pods = []).
    { unfold bad_name_pods.
      apply filter_none. intros pod Hpod Hnot_member.
      apply Hnot_member.
      assert (Hkey_desired : PodV.key pod ∈ desired_pod_keys sts).
      { rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
      unfold desired_pod_keys in Hkey_desired.
      apply list_elem_of_fmap_1 in Hkey_desired as
        (ordinal & Hkey_eq & Hordinal).
      unfold pod_has_int32_member_key.
      split.
      - apply (f_equal KKey.Namespace') in Hkey_eq. exact Hkey_eq.
      - exists ordinal. split.
        + unfold desired_ordinals in Hordinal.
          apply elem_of_seq in Hordinal as [_ Hordinal].
          pose proof (statefulset_replicas_le_go_int32_max sts).
          lia.
        + apply (f_equal KKey.Name') in Hkey_eq. exact Hkey_eq. }
    assert (Halive_condemned_pods_nil : filter is_pod_alive (condemned_pods sts pods) = []).
    { apply filter_none. intros pod Hpod Halive.
      unfold condemned_pods in Hpod.
      apply list_elem_of_filter in Hpod as ((_ & Hnot_desired) & Hpod).
      apply Hnot_desired.
      unfold pod_key_is_desired.
      rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
    assert (Hmissing_pvcs_nil : missing_pvc_keys sts pvcs = []).
    { unfold missing_pvc_keys.
      apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual. by apply Hpvcs_match. }
    rewrite Hmissing_pods_nil Houtdated_pods_nil Hbad_name_pods_nil
      Halive_condemned_pods_nil Hmissing_pvcs_nil.
    done.
Qed.

Definition pod_meta_except_resource_version_changed
    (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta') ≠
      ObjectMetaV.without_resource_version pod'.(PodV.ObjectMeta').

Definition pod_spec_changed (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    pod.(PodV.Spec') ≠ pod'.(PodV.Spec').

Definition pods_progress_observed (pods pods' : list PodV.t) : Prop :=
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods) ≠
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods') ∨
  pod_meta_except_resource_version_changed pods pods' ∨
  pod_spec_changed pods pods'.

Lemma statefulset_storage_view_missing_pod_keys sts1 sts2 pods :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  missing_pod_keys sts1 pods = missing_pod_keys sts2 pods.
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Lemma meta_parent_ref_namespace meta parent_key parent_uid :
  meta_parent_ref meta = Some (parent_key, parent_uid) →
  meta.(ObjectMetaV.Namespace') = parent_key.(KKey.Namespace').
Proof.
  unfold meta_parent_ref.
  destruct meta.(ObjectMetaV.OwnerReferences') as [owner_references|];
    last done.
  destruct (list_find
    (λ owner_reference,
      owner_reference.(OwnerReferenceV.Controller') = Some true)
    owner_references) as [[i owner_reference]|]; last done.
  intros Hparent. inversion Hparent. done.
Qed.

Lemma statefulset_storage_view_missing_pvc_keys sts1 sts2 pvcs :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  missing_pvc_keys sts1 pvcs = missing_pvc_keys sts2 pvcs.
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Lemma statefulset_storage_view_match_distance sts1 sts2 pods pvcs :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  match_distance sts1 pods pvcs = match_distance sts2 pods pvcs.
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Lemma statefulset_storage_view_current_state_matches sts1 sts2 pods pvcs :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  (current_state_matches sts1 pods pvcs ↔
   current_state_matches sts2 pods pvcs).
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Lemma statefulset_storage_view_pending_pod sts1 sts2 pod :
  statefulset_storage_view sts1 = statefulset_storage_view sts2 →
  (pending_pod sts1 pod ↔ pending_pod sts2 pod).
Proof.
  destruct sts1 as [typemeta1 meta1 spec1 status1],
    sts2 as [typemeta2 meta2 spec2 status2].
  destruct meta1, meta2. simpl.
  intros Hview. injection Hview; intros; subst. done.
Qed.

Lemma pod_storage_view_pending pod sts :
  pending_pod sts pod ↔
  (¬ pod_view_alive (pod_storage_view pod) ∧
   pod_has_int32_member_name
     sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
     (pod_view_meta (pod_storage_view pod)).(ObjectMetaV.Name')).
Proof.
  destruct pod as [typemeta meta spec status].
  destruct meta. simpl. done.
Qed.

Lemma pending_pods_empty_storage_view_perm sts pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  filter (pending_pod sts) pods1 = [] →
  filter (pending_pod sts) pods2 = [].
Proof.
  intros Hperm Hempty.
  set pending_view := (λ view,
    ¬ pod_view_alive view ∧
    pod_has_int32_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (pod_view_meta view).(ObjectMetaV.Name')).
  assert (Hfilter1 : filter pending_view (pod_storage_view <$> pods1) =
      pod_storage_view <$> filter (pending_pod sts) pods1).
  { apply filter_fmap_comm. intros pod.
    unfold pending_view. symmetry. apply pod_storage_view_pending. }
  assert (Hfilter2 : filter pending_view (pod_storage_view <$> pods2) =
      pod_storage_view <$> filter (pending_pod sts) pods2).
  { apply filter_fmap_comm. intros pod.
    unfold pending_view. symmetry. apply pod_storage_view_pending. }
  pose proof (perm_filter pending_view _ _ Hperm) as Hfiltered_perm.
  rewrite Hfilter1 Hfilter2 Hempty /= in Hfiltered_perm.
  pose proof (Permutation_length Hfiltered_perm) as Hlength.
  rewrite !map_length in Hlength.
  destruct (filter (pending_pod sts) pods2); simpl in *; [done|lia].
Qed.

Lemma pod_storage_view_perm_keys pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  PodV.key <$> pods1 ≡ₚ PodV.key <$> pods2.
Proof.
  intros Hperm.
  assert (Hkeys : ∀ (pods : list PodV.t),
      PodV.key <$> pods =
      pod_view_key <$> (pod_storage_view <$> pods)).
  { intros pods. induction pods as [|pod pods IH]; simpl; first done.
    pose proof (pod_storage_view_observations pod) as Hobs.
    rewrite (proj1 Hobs). f_equal. exact IH. }
  rewrite !Hkeys. by apply Permutation_map.
Qed.

Lemma missing_pod_keys_storage_view_perm sts pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  missing_pod_keys sts pods1 = missing_pod_keys sts pods2.
Proof.
  intros Hperm.
  pose proof (pod_storage_view_perm_keys _ _ Hperm) as Hkeys.
  unfold missing_pod_keys.
  induction (desired_pod_keys sts) as [|key keys IH]; simpl; first done.
  rewrite !filter_cons.
  destruct (decide (key ∉ PodV.key <$> pods1)) as [Hnot1|Hin1];
    destruct (decide (key ∉ PodV.key <$> pods2)) as [Hnot2|Hin2]; simpl.
  - by rewrite IH.
  - exfalso. apply Hin2. rewrite -Hkeys. exact Hnot1.
  - exfalso. apply Hin1. rewrite Hkeys. exact Hnot2.
  - exact IH.
Qed.

Lemma pods_progress_observed_storage_view_perm_left pods1 pods2 pods' :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  pods_progress_observed pods1 pods' →
  pods_progress_observed pods2 pods'.
Proof.
  intros Hperm Hprogress.
  pose proof (pod_storage_view_perm_keys _ _ Hperm) as Hkeys.
  destruct Hprogress as [Hkeys_changed|[Hmeta_changed|Hspec_changed]].
  - left. intros Hsame.
    apply Hkeys_changed. rewrite Hkeys. exact Hsame.
  - right. left.
    destruct Hmeta_changed as
      (pod1 & pod' & Hpod1 & Hpod' & Hkey & Hmeta).
    assert (pod_storage_view pod1 ∈ pod_storage_view <$> pods2) as Hview.
    { rewrite -Hperm. by apply list_elem_of_fmap_2. }
    apply list_elem_of_fmap_1 in Hview as
      (pod2 & Hview & Hpod2).
    exists pod2, pod'. split_and!; try done.
    + pose proof (f_equal pod_view_key Hview) as Hview_key.
      change (PodV.key pod1 = PodV.key pod2) in Hview_key.
      rewrite -Hkey. symmetry. exact Hview_key.
    + pose proof (f_equal fst Hview) as Hview_meta.
      simpl in Hview_meta.
      intros Hmeta2. apply Hmeta.
      rewrite Hview_meta. exact Hmeta2.
  - right. right.
    destruct Hspec_changed as
      (pod1 & pod' & Hpod1 & Hpod' & Hkey & Hspec).
    assert (pod_storage_view pod1 ∈ pod_storage_view <$> pods2) as Hview.
    { rewrite -Hperm. by apply list_elem_of_fmap_2. }
    apply list_elem_of_fmap_1 in Hview as
      (pod2 & Hview & Hpod2).
    exists pod2, pod'. split_and!; try done.
    + pose proof (f_equal pod_view_key Hview) as Hview_key.
      change (PodV.key pod1 = PodV.key pod2) in Hview_key.
      rewrite -Hkey. symmetry. exact Hview_key.
    + pose proof (f_equal snd Hview) as Hview_spec.
      simpl in Hview_spec. inversion Hview_spec; subst.
      exact Hspec.
Qed.

End proof.
