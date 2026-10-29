From New.proof.controllers.statefulset Require Export top_level.

(* Construction helpers and supporting lemmas. Legacy PodSpec-comparison
   predicates remain for the deferred migration of the program proofs. *)

(* Pure facts used by the public distance-zero theorem. *)
Lemma desired_pod_keys_unique sts : NoDup (desired_pod_keys sts).
Proof.
  unfold desired_pod_keys, desired_ordinals. apply NoDup_fmap_2.
  - intros ordinal1 ordinal2 Hkey.
    apply (f_equal KKey.Name') in Hkey. simpl in Hkey.
    unfold desired_pod_name in Hkey.
    apply app_inv_head in Hkey. inversion Hkey as [Hdecimal].
    by apply decimal_string_inj in Hdecimal.
  - apply NoDup_seq.
Qed.

Lemma sum_nat_zero_iff {A} (f : A → nat) xs :
  fold_right Nat.add 0%nat (f <$> xs) = 0%nat ↔ Forall (λ x, f x = 0%nat) xs.
Proof.
  induction xs as [|x xs IH]; cbn [fmap list_fmap fold_right].
  - split; [intros _; constructor|done].
  - split.
    + intros Hzero. constructor; [lia|apply (proj1 IH); lia].
    + intros Hforall. inversion Hforall as [|? ? Hx Hxs]; subst.
      apply (proj2 IH) in Hxs. lia.
Qed.

Lemma match_distance_zero_matches_of_nodup sts revision_name state :
  NoDup (PodV.key <$> state.(revision_pods)) →
  match_distance sts revision_name state = 0%nat ↔ current_state_matches sts revision_name state.
Proof.
  intros Hnodup. split.
  - intros Hdist. unfold match_distance in Hdist.
    assert (Hrevision : revision_available sts revision_name state = true).
    { destruct (revision_available sts revision_name state); [done|lia]. }
    assert (Hmissing : missing_pod_keys sts state.(revision_pods) = []).
    { apply length_zero_iff_nil. lia. }
    assert (Hpvc : missing_pvc_keys sts state.(revision_pvcs) = []).
    { apply length_zero_iff_nil. lia. }
    assert (Hcost : fold_right Nat.add 0%nat
      ((λ pod, if decide (PodV.key pod ∈ desired_pod_keys sts)
        then if revision_pod_matches sts revision_name pod then 0%nat else 2%nat
        else 1%nat) <$> state.(revision_pods)) = 0%nat) by lia.
    apply sum_nat_zero_iff in Hcost.
    assert (Hgood : ∀ pod, pod ∈ state.(revision_pods) →
      PodV.key pod ∈ desired_pod_keys sts ∧ revision_pod_matches sts revision_name pod = true).
    { intros pod Hpod. rewrite Forall_forall in Hcost.
      specialize (Hcost pod (proj1 (list_elem_of_In _ _) Hpod)).
      destruct (decide (PodV.key pod ∈ desired_pod_keys sts)) as [Hkey|Hkey]; last lia.
      destruct (revision_pod_matches sts revision_name pod) eqn:Hmatch; [done|lia]. }
    unfold current_state_matches. split; [exact Hrevision|]. split.
    + apply NoDup_Permutation; [exact Hnodup|apply desired_pod_keys_unique|].
      intros key. split.
      * intros Hkey. apply list_elem_of_fmap_1 in Hkey as (pod & -> & Hpod).
        exact (proj1 (Hgood pod Hpod)).
      * intros Hdesired. destruct (decide (key ∈ PodV.key <$> state.(revision_pods))) as [Hkey|Hkey].
        { exact Hkey. }
        exfalso. assert (key ∈ missing_pod_keys sts state.(revision_pods)) as Hin.
        { unfold missing_pod_keys. apply list_elem_of_filter. done. }
        rewrite Hmissing elem_of_nil in Hin. exact Hin.
    + split; last exact Hpvc.
      apply Forall_forall. intros pod Hpod.
      assert (Hin : pod ∈ state.(revision_pods)) by by rewrite list_elem_of_In.
      exact (proj2 (Hgood pod Hin)).
  - intros (Hrevision & Hkeys & Hpods & Hpvc).
    assert (Hmissing : missing_pod_keys sts state.(revision_pods) = []).
    { unfold missing_pod_keys. apply filter_none. intros key Hkey Hnotin.
      apply Hnotin. by rewrite Hkeys. }
    assert (Hcost : fold_right Nat.add 0%nat
      ((λ pod, if decide (PodV.key pod ∈ desired_pod_keys sts)
        then if revision_pod_matches sts revision_name pod then 0%nat else 2%nat
        else 1%nat) <$> state.(revision_pods)) = 0%nat).
    { apply sum_nat_zero_iff. apply Forall_forall. intros pod Hpod.
      assert (Hkey : PodV.key pod ∈ desired_pod_keys sts).
      { rewrite -Hkeys. apply list_elem_of_fmap_2. by rewrite list_elem_of_In. }
      destruct (decide (PodV.key pod ∈ desired_pod_keys sts)); last contradiction.
      rewrite Forall_forall in Hpods. by rewrite (Hpods pod Hpod). }
    unfold match_distance. rewrite Hrevision Hmissing Hpvc Hcost. done.
Qed.

Definition new_persistent_volume_claim_labels
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t) :
    gmap go_string go_string :=
  let claim_labels :=
    default ∅
      claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Labels') in
  let selector_labels :=
    match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
    | Some selector =>
        default ∅ selector.(LabelSelectorV.MatchLabels')
    | None => ∅
    end in
  selector_labels ∪ claim_labels.

Definition new_persistent_volume_claim
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t)
    (ordinal : nat) : PersistentVolumeClaimV.t :=
  let object_meta :=
    claim_template.(PersistentVolumeClaimV.ObjectMeta')
      <| ObjectMetaV.Name' :=
          desired_pvc_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
            ordinal |>
      <| ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
      <| ObjectMetaV.OwnerReferences' := None |>
      <| ObjectMetaV.Labels' :=
          Some (new_persistent_volume_claim_labels set claim_template) |> in
  claim_template <| PersistentVolumeClaimV.ObjectMeta' := object_meta |>.

Definition pod_key_is_desired (sts : StatefulSetV.t) (key : KKey.t) : Prop :=
  key ∈ desired_pod_keys sts.

#[global] Instance pod_key_is_desired_decision sts key :
    Decision (pod_key_is_desired sts key).
Proof. unfold pod_key_is_desired. apply _. Defined.

Definition member_name_prefix (set_name : go_string) : go_string :=
  set_name ++ "-"%go.

Definition parse_member_name (set_name pod_name : go_string) : option nat :=
  match New.proof.string.prefix_suffix.strip_prefix (member_name_prefix set_name)
      pod_name with
  | Some suffix => parse_canonical_decimal_string suffix
  | None => None
  end.

Lemma parse_member_name_sound set_name pod_name ordinal :
  parse_member_name set_name pod_name = Some ordinal →
  pod_name = desired_pod_name set_name ordinal.
Proof.
  unfold parse_member_name.
  destruct (New.proof.string.prefix_suffix.strip_prefix
    (member_name_prefix set_name) pod_name) as [suffix|] eqn:Hstrip; [|done].
  intros Hparse.
  apply parse_canonical_decimal_string_sound in Hparse.
  apply New.proof.string.prefix_suffix.strip_prefix_correct in Hstrip.
  unfold desired_pod_name, member_name_prefix in *.
  rewrite Hstrip -Hparse.
  by rewrite List.app_assoc.
Qed.

Lemma parse_member_name_complete set_name pod_name ordinal :
  pod_name = desired_pod_name set_name ordinal →
  parse_member_name set_name pod_name = Some ordinal.
Proof.
  intros Hname.
  unfold parse_member_name.
  rewrite Hname.
  unfold desired_pod_name, member_name_prefix.
  rewrite List.app_assoc.
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete.
  apply parse_canonical_decimal_string_decimal_string.
Qed.

Definition pod_has_int32_member_name (set_name pod_name : go_string) : Prop :=
  ∃ ordinal : nat,
    (ordinal <= go_int32_max_nat)%nat ∧
    pod_name = desired_pod_name set_name ordinal.

#[global] Instance pod_has_int32_member_name_decision set_name pod_name :
    Decision (pod_has_int32_member_name set_name pod_name).
Proof.
  unfold pod_has_int32_member_name.
  destruct (parse_member_name set_name pod_name) as [ordinal|] eqn:Hparse.
  - destruct (decide (ordinal <= go_int32_max_nat)%nat) as
      [Hbound|Hoverflow].
    + left. exists ordinal. split; [done|].
      by apply parse_member_name_sound.
    + right. intros (ordinal' & Hbound & Hname).
      apply parse_member_name_complete in Hname.
      rewrite Hparse in Hname. simplify_eq/=. done.
  - right. intros (ordinal & _ & Hname).
    apply parse_member_name_complete in Hname. congruence.
Defined.

Definition pending_pod sts (pod : PodV.t) : Prop :=
  ¬ is_pod_alive pod ∧
  pod_has_int32_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').

#[global] Instance pending_pod_decision sts pod :
    Decision (pending_pod sts pod).
Proof. unfold pending_pod, is_pod_alive. apply _. Defined.

Definition pod_ordinal_suffix (pod_name : go_string) : option go_string :=
  match list_find (λ b, b = byte_dash) (reverse pod_name) with
  | Some (idx, _) => Some (reverse (take idx (reverse pod_name)))
  | None => None
  end.

Definition parse_pod_ordinal (pod_name : go_string) : option nat :=
  suffix ← pod_ordinal_suffix pod_name;
  parse_decimal_string suffix.

Definition pod_identity_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'),
    pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
  | Some ordinal, Some labels =>
      (ordinal <= go_int32_max_nat)%nat ∧
      pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      labels !! statefulset_pod_name_label =
        Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      labels !! pod_index_label = Some (decimal_string ordinal)
  | _, _ => False
  end.

#[global] Instance pod_identity_matches_decision sts pod :
    Decision (pod_identity_matches sts pod).
Proof.
  unfold pod_identity_matches.
  destruct parse_member_name,
    (pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')); apply _.
Defined.

Definition pod_volumes_map_insert
    (volumes : gmap go_string VolumeV.t) (volume : VolumeV.t) :
    gmap go_string VolumeV.t :=
  <[volume.(VolumeV.Name') := volume]> volumes.

Definition pod_volumes_map_of_list (volumes : list VolumeV.t) :
    gmap go_string VolumeV.t :=
  fold_left pod_volumes_map_insert volumes ∅.

Definition pod_volume_claim_matches
    (volumes : gmap go_string VolumeV.t) (set_name : go_string)
    (ordinal : nat) (claim_template_name : go_string) : Prop :=
  match volumes !! claim_template_name with
  | Some volume =>
      match volume.(VolumeV.VolumeSource').(
        VolumeSourceV.PersistentVolumeClaim') with
      | Some pvc =>
          pvc.(v1.PersistentVolumeClaimVolumeSource.ClaimName') =
            desired_pvc_name set_name claim_template_name ordinal
      | None => False
      end
  | None => False
  end.

#[global] Instance pod_volume_claim_matches_decision volumes set_name ordinal
    claim_template_name :
    Decision (pod_volume_claim_matches volumes set_name ordinal
      claim_template_name).
Proof.
  unfold pod_volume_claim_matches.
  destruct (volumes !! claim_template_name) as [volume|]; [|apply _].
  destruct volume.(VolumeV.VolumeSource').(
    VolumeSourceV.PersistentVolumeClaim'); apply _.
Defined.

Definition pod_storage_matches (set : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_pod_ordinal pod.(PodV.ObjectMeta').(ObjectMetaV.Name') with
  | Some ordinal =>
      (ordinal <= go_int32_max_nat)%nat ∧
      Forall
        (pod_volume_claim_matches
          (pod_volumes_map_of_list
            (PodSpecV.volumes_list pod.(PodV.Spec')))
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
        (pvc_claim_template_names set)
  | None => False
  end.

#[global] Instance pod_storage_matches_decision set pod :
    Decision (pod_storage_matches set pod).
Proof.
  unfold pod_storage_matches.
  destruct (parse_pod_ordinal
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')); apply _.
Defined.

Definition storage_claim_volume (set : StatefulSetV.t) (ordinal : nat)
    (claim_template_name : go_string) : VolumeV.t :=
  {| VolumeV.Name' := claim_template_name;
     VolumeV.VolumeSource' :=
       (VolumeSourceV.zero <| VolumeSourceV.PersistentVolumeClaim' :=
            Some
              {| v1.PersistentVolumeClaimVolumeSource.ClaimName' :=
                   desired_pvc_name
                     set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                     claim_template_name ordinal;
                 v1.PersistentVolumeClaimVolumeSource.ReadOnly' := false |}
       |>)
  |}.

Definition init_storage_volumes (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) (claim_template_names : list go_string) :
    list VolumeV.t :=
  (storage_claim_volume set ordinal <$> claim_template_names) ++
  filter
    (λ volume, volume.(VolumeV.Name') ∉ claim_template_names)
    (PodSpecV.volumes_list pod.(PodV.Spec')).

(* The map iteration order is exposed as [claim_template_names].  Its set is
   fixed by the StatefulSet, while its order is intentionally unspecified by
   Go.  Existing Pod volumes controlled by a claim template are replaced;
   all other volumes retain their original order. *)
Definition init_storage (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) (claim_template_names : list go_string) : PodV.t :=
  pod <| PodV.Spec' :=
    pod.(PodV.Spec') <| PodSpecV.Volumes' :=
      Some (init_storage_volumes set pod ordinal claim_template_names) |> |>.

Definition without_statefulset_fields := PodAPI.without_managed.

Definition desired_pod_labels (sts : StatefulSetV.t) (ordinal : nat) : PodAPI.string_map :=
  let meta := sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.ObjectMeta') in
  Some (<[pod_index_label := decimal_string ordinal]>
    (<[statefulset_pod_name_label := desired_pod_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal]>
      (default ∅ meta.(ObjectMetaV.Labels')))).

Definition desired_pod_annotations (sts : StatefulSetV.t) : PodAPI.string_map :=
  let meta := sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.ObjectMeta') in
  Some (default ∅ meta.(ObjectMetaV.Annotations')).

Definition desired_prepared_spec (sts : StatefulSetV.t) (pod_name : go_string) : PodSpecV.t :=
  let ordinal := default 0%nat (parse_pod_ordinal pod_name) in
  without_statefulset_fields (PodAPI.create_spec (desired_pod_labels sts ordinal)
    (desired_pod_annotations sts)
    (without_statefulset_fields sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.Spec'))).

Definition pod_immutable_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.Spec').(PodSpecV.Hostname') =
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
  pod.(PodV.Spec').(PodSpecV.Subdomain') =
    sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
  pod_storage_matches sts pod ∧
  without_statefulset_fields pod.(PodV.Spec') =
    desired_prepared_spec sts pod.(PodV.ObjectMeta').(ObjectMetaV.Name').

#[global] Instance pod_immutable_matches_decision sts pod :
    Decision (pod_immutable_matches sts pod).
Proof.
  unfold pod_immutable_matches, without_statefulset_fields.
  destruct (decide
    (pod.(PodV.Spec').(PodSpecV.Hostname') =
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [Hhostname|Hhostname].
  2: { right. intros (H & _). contradiction. }
  destruct (decide
    (pod.(PodV.Spec').(PodSpecV.Subdomain') =
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName')))
    as [Hsubdomain|Hsubdomain].
  2: { right. intros (_ & H & _). contradiction. }
  destruct (decide (pod_storage_matches sts pod)) as [Hstorage|Hstorage].
  2: { right. intros (_ & _ & H & _). contradiction. }
  destruct (decide (without_statefulset_fields pod.(PodV.Spec') =
    desired_prepared_spec sts pod.(PodV.ObjectMeta').(ObjectMetaV.Name')))
    as [Hrest|Hrest].
  2: { right. intros (_ & _ & _ & H). contradiction. }
  left. split_and!; done.
Defined.

Definition pod_match (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod_identity_matches sts pod ∧ pod_immutable_matches sts pod.

(** A constructor produces a create request. API preparation has not yet
    happened, so this deliberately differs from the stored-Pod invariant. *)
Definition pod_creation_request_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod_identity_matches sts pod ∧
  pod.(PodV.Spec').(PodSpecV.Hostname') = pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
  pod.(PodV.Spec').(PodSpecV.Subdomain') = sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
  pod_storage_matches sts pod ∧
  without_statefulset_fields pod.(PodV.Spec') =
    without_statefulset_fields sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.Spec') ∧
  ∃ ordinal,
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ∧
    pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') = desired_pod_labels sts ordinal ∧
    pod.(PodV.ObjectMeta').(ObjectMetaV.Annotations') = desired_pod_annotations sts.

Lemma create_volumes_map_fold volumes (initial : gmap go_string VolumeV.t) :
  fold_left pod_volumes_map_insert (PodAPI.create_volume <$> volumes) (PodAPI.create_volume <$> initial) =
  PodAPI.create_volume <$> fold_left pod_volumes_map_insert volumes initial.
Proof.
  revert initial. induction volumes as [|volume volumes IH]; intros initial; simpl; first done.
  rewrite /pod_volumes_map_insert /= -fmap_insert. apply IH.
Qed.

Lemma create_volumes_map volumes :
  pod_volumes_map_of_list (PodAPI.create_volume <$> volumes) =
  PodAPI.create_volume <$> pod_volumes_map_of_list volumes.
Proof.
  unfold pod_volumes_map_of_list.
  rewrite -(create_volumes_map_fold volumes ∅) fmap_empty. done.
Qed.

Lemma create_volume_claim_matches volumes set_name ordinal claim_name :
  pod_volume_claim_matches (pod_volumes_map_of_list (PodAPI.create_volume <$> volumes))
    set_name ordinal claim_name ↔
  pod_volume_claim_matches (pod_volumes_map_of_list volumes) set_name ordinal claim_name.
Proof.
  rewrite create_volumes_map /pod_volume_claim_matches lookup_fmap.
  destruct (pod_volumes_map_of_list volumes !! claim_name) as [volume|]; last done.
  rewrite /PodAPI.create_volume /=. done.
Qed.

Lemma pod_storage_matches_prepared set pod :
  pod_storage_matches set (pod <| PodV.Spec' := PodV.prepared_spec pod |>) ↔ pod_storage_matches set pod.
Proof.
  unfold pod_storage_matches. simpl.
  destruct (parse_pod_ordinal pod.(PodV.ObjectMeta').(ObjectMetaV.Name')); last done.
  rewrite /PodV.prepared_spec /PodAPI.create_spec /PodSpecV.volumes_list /=.
  destruct pod.(PodV.Spec').(PodSpecV.Volumes') as [volumes|]; simpl; last done.
  split; intros [Hbound Hclaims]; split; try exact Hbound.
  - eapply Forall_impl; last exact Hclaims.
    intros name Hclaim. by apply (proj1 (create_volume_claim_matches volumes _ _ _)).
  - eapply Forall_impl; last exact Hclaims.
    intros name Hclaim. by apply (proj2 (create_volume_claim_matches volumes _ _ _)).
Qed.

Definition stateful_pod_request_spec (sts : StatefulSetV.t) ordinal claim_names : PodSpecV.t :=
  let spec := sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.Spec') in
  spec <| PodSpecV.Volumes' := Some ((storage_claim_volume sts ordinal <$> claim_names) ++
      filter (λ volume, volume.(VolumeV.Name') ∉ claim_names) (PodSpecV.volumes_list spec)) |>
    <| PodSpecV.Hostname' := desired_pod_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal |>
    <| PodSpecV.Subdomain' := sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>.

#[global] Instance pod_match_decision sts pod : Decision (pod_match sts pod).
Proof. unfold pod_match. apply _. Defined.

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

Definition living_pods (all_pods : list PodV.t) : list PodV.t :=
  filter is_pod_alive all_pods.

Definition pod_reservation_identity (pod : PodV.t) : KKey.t * types.UID.t :=
  (PodV.key pod, pod.(PodV.ObjectMeta').(ObjectMetaV.UID')).

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

Definition pod_distance sts pods : nat :=
  length (missing_pod_keys sts pods) +
  2 * length (outdated_pods sts pods) +
  length (condemned_pods sts pods) +
  length (bad_name_pods sts pods).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs).

Definition input_requirement (sts : StatefulSetV.t) : Prop :=
  (* Generated Pod names are also hostnames and label values, so they must
     remain within the DNS-1123 label limit after adding the ordinal. *)
  (∀ ordinal,
    (ordinal < statefulset_replicas sts)%nat →
    valid_dns1123_label
      (desired_pod_name
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)) ∧
  (* StatefulSet admission does not validate Pod-template finalizers, although
     Pod create validates the finalizers copied by the controller. *)
  valid_finalizers
    ((sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template')).(
      PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')) ∧
  (* StatefulSet admission validates claim-template specs but not all metadata
     copied to the PVC submitted by the controller. *)
  Forall
    (λ claim_template,
      ∀ ordinal,
        (ordinal < statefulset_replicas sts)%nat →
        PersistentVolumeClaimV.valid_create PersistentVolumeClaimV.kind
          sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
          (new_persistent_volume_claim sts claim_template ordinal))
    (StatefulSetSpecV.volume_claim_templates_list sts.(StatefulSetV.Spec')) ∧
  (∀ ordinal claim_names,
    (ordinal < statefulset_replicas sts)%nat →
    NoDup claim_names →
    list_to_set (C:=gset go_string) claim_names = list_to_set (pvc_claim_template_names sts) →
    let spec := stateful_pod_request_spec sts ordinal claim_names in
    PodAPI.validate_spec (PodAPI.schema_defaults spec) = true ∧
    PodAPI.validate_annotations (desired_pod_annotations sts)
      (PodAPI.create_spec (desired_pod_labels sts ordinal) (desired_pod_annotations sts) spec) = true ∧
    PodAPI.validate_spec
      (PodAPI.create_spec (desired_pod_labels sts ordinal) (desired_pod_annotations sts) spec) = true).



Definition terminating_bound_after_deletion terminating_bound
    (deletion : option (KKey.t * types.UID.t)) :=
  match deletion with
  | None => terminating_bound
  | Some _ => S terminating_bound
  end.

Section proof.
Context `{hG: !heapGS Σ} `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition own_started_deletion γ
    (deletion : option (KKey.t * types.UID.t)) : iProp Σ :=
  match deletion with
  | None => emp
  | Some (key, uid) => own_deleting_reserved_frag γ 1 key uid
  end.

Lemma own_occupied_pods_as_identities γ dq pods :
  ([∗ list] pod ∈ pods,
    own_occupied_reserved_frag γ dq (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ⊣⊢
    [∗ list] identity ∈ pod_reservation_identity <$> pods,
      own_occupied_reserved_frag γ dq identity.1 identity.2.
Proof.
  rewrite big_sepL_fmap. done.
Qed.

Lemma own_pod_frags_living γ dq pods :
  ([∗ list] pod ∈ pods,
    own_meta_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
      pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))) -∗
  ⌜ Forall is_pod_alive pods ⌝.
Proof.
  iIntros "Hpods". iInduction pods as [|pod pods] "IH".
  { iPureIntro. constructor. }
  rewrite big_sepL_cons. iDestruct "Hpods" as "[(Hmeta & _) Hpods]".
  iPoseProof (kview.own_meta_valid with "Hmeta") as "%Hmeta".
  iPoseProof ("IH" with "Hpods") as "%Hpods".
  iPureIntro. constructor; last exact Hpods.
  unfold is_pod_alive. destruct Hmeta as (_ & _ & _ & _ & Hliving).
  exact Hliving.
Qed.

End proof.
