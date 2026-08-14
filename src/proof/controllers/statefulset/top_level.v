From New.proof.controllers.statefulset Require Export statefulset_init.

(* Pure desired-state definitions used by all three top-level specifications.
   Apart from package initialization, this file imports no other statefulset
   proof, so clients can depend on the specifications without their proofs. *)

Definition pvc_claim_template_names (sts : StatefulSetV.t) : list go_string :=
  (λ claim_template,
    claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
  <$> StatefulSetSpecV.volume_claim_templates_list
    sts.(StatefulSetV.Spec').

Definition desired_pvc_name set_name claim_template_name ordinal : go_string :=
  claim_template_name ++ "-"%go ++ set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pvc_key sts claim_template_name ordinal : KKey.t := {|
  KKey.Kind' := PersistentVolumeClaimV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pvc_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') claim_template_name ordinal;
|}.

Definition desired_pvc_key_candidates sts : list KKey.t :=
  concat (
    (λ ordinal,
      (λ claim_template_name, desired_pvc_key sts claim_template_name ordinal)
      <$> pvc_claim_template_names sts)
    <$> seq 0
      (match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
       | Some replicas => sint.nat replicas
       | None => 1%nat
       end)
  ).

Definition desired_pvc_keys sts : list KKey.t :=
  elements (list_to_set (C:=gset KKey.t) (desired_pvc_key_candidates sts)).

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

Definition statefulset_replicas (sts : StatefulSetV.t) : nat :=
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
  | Some replicas => sint.nat replicas
  | None => 1%nat
  end.

Definition desired_ordinals (sts : StatefulSetV.t) : list nat :=
  seq 0 (statefulset_replicas sts).

Definition desired_pod_name (set_name : go_string) (ordinal : nat) : go_string :=
  set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pod_key sts ordinal : KKey.t := {|
  KKey.Kind' := PodV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pod_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal;
|}.

Definition desired_pod_keys (sts : StatefulSetV.t) : list KKey.t :=
  desired_pod_key sts <$> desired_ordinals sts.

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

Definition without_statefulset_fields (_ : PodSpecV.t) : PodSpecV.t := {|
  PodSpecV.Volumes' := None;
  PodSpecV.Hostname' := ""%go;
  PodSpecV.Subdomain' := ""%go;
|}.

Definition pod_immutable_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.Spec').(PodSpecV.Hostname') =
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
  pod.(PodV.Spec').(PodSpecV.Subdomain') =
    sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
  pod_storage_matches sts pod ∧
  without_statefulset_fields pod.(PodV.Spec') =
    without_statefulset_fields
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(
        PodTemplateSpecV.Spec').

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
  left. split_and!; try done.
Defined.

Definition pod_match (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod_identity_matches sts pod ∧ pod_immutable_matches sts pod.

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

Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).

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

Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) :
    list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs))
    (desired_pvc_keys sts).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs).

(* Although the Pod snapshots in the top-level specs are living, this metric
   is also applied to raw index results and intermediate lists containing
   terminating Pods. A Pod stops contributing as soon as deletion starts, so
   that transition decreases the distance without waiting for physical removal. *)
Definition match_distance sts all_pods pvcs : nat :=
  pod_distance sts (living_pods all_pods) + pvc_distance sts pvcs.

Definition pods_match sts pods : Prop :=
  PodV.key <$> pods ≡ₚ desired_pod_keys sts ∧
  Forall is_pod_alive pods ∧
  Forall (pod_match sts) pods.

Definition pvcs_match sts (pvcs : list PersistentVolumeClaimV.t) : Prop :=
  ∀ key, key ∈ desired_pvc_keys sts →
    key ∈ (PersistentVolumeClaimV.key <$> pvcs).

Definition current_state_matches sts pods pvcs : Prop :=
  pods_match sts pods ∧ pvcs_match sts pvcs.

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
        PersistentVolumeClaimV.valid_named_create
          sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
          (new_persistent_volume_claim sts claim_template ordinal))
    (StatefulSetSpecV.volume_claim_templates_list
      sts.(StatefulSetV.Spec')).

Section specs.
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

Record all_fractions := {
  sts_dq : dfrac;
  pod_dq : dfrac;
  children_dq : dfrac;
  pvc_dq : dfrac;
}.

Definition mutating_fractions dq : all_fractions :=
  {| sts_dq := dq; pod_dq := 1; children_dq := 1; pvc_dq := 1 |}.

Definition stability_fractions dq : all_fractions :=
  {| sts_dq := dq; pod_dq := dq; children_dq := dq; pvc_dq := dq |}.

Definition own_occupied_pods γ (pods : list PodV.t) : iProp Σ :=
  [∗ list] pod ∈ pods,
    own_occupied_reserved_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID').

Definition own_occupied_pvcs γ
    (pvcs : list PersistentVolumeClaimV.t) : iProp Σ :=
  [∗ list] pvc ∈ pvcs,
    own_occupied_reserved_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID').

Definition own_missing_pod_reservations γ sts pods : iProp Σ :=
  ([∗ set] key ∈ list_to_set (C:=gset KKey.t) (missing_pod_keys sts pods),
    own_available_frag γ key ∨
    ∃ uid, own_deleting_reserved_frag γ key uid)%I.

Definition own_missing_pvc_reservations γ sts pvcs : iProp Σ :=
  [∗ set] key ∈ list_to_set (C:=gset KKey.t) (missing_pvc_keys sts pvcs),
    own_available_frag γ key.

Definition statefulset_owned_resources γ sts fractions pods pvcs terminating_phase : iProp Σ :=
  "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(sts_dq) sts.(StatefulSetV.ObjectMeta') ∗
  "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(sts_dq)
      (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
  "Hown_pod_frags" ∷ ([∗ list] pod ∈ pods,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq)
      pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq)
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
  "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(children_dq) (list_to_set (PodV.key <$> pods)) ∗
  "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (StatefulSetV.key sts)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_phase ∗
  "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
    own_meta_frag γ (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') fractions.(pvc_dq)
      pvc.(PersistentVolumeClaimV.ObjectMeta')).

Definition syncStatefulSet_preservation_spec γ l namespace name sts dq pods pvcs phase : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ statefulset_owned_resources γ sts (mutating_fractions dq) pods pvcs phase ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs ∗
      "Hreserved_pods" ∷ own_missing_pod_reservations γ sts pods ∗
      "Hreserved_pvcs" ∷ own_missing_pvc_reservations γ sts pvcs ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement sts ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ pods' pvcs' phase' (err : interface.t), RET #err;
      statefulset_owned_resources γ sts (mutating_fractions dq) pods' pvcs' phase' ∗
      own_occupied_pods γ pods' ∗
      own_occupied_pvcs γ pvcs' ∗
      own_missing_pod_reservations γ sts pods' ∗
      own_missing_pvc_reservations γ sts pvcs' ∗
      ⌜ match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs ⌝
  }}}.

Definition syncStatefulSet_progress_spec γ l namespace name sts dq pods pvcs : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ statefulset_owned_resources γ sts (mutating_fractions dq) pods pvcs Quiescent ∗
      "Hoccupied_pods" ∷ own_occupied_pods γ pods ∗
      "Hoccupied_pvcs" ∷ own_occupied_pvcs γ pvcs ∗
      "Hreserved_pods" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_available_frag γ key) ∗
      "Hreserved_pvcs" ∷ own_missing_pvc_reservations γ sts pvcs ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement sts ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ pods' pvcs' phase' (err : interface.t), RET #err;
      statefulset_owned_resources γ sts (mutating_fractions dq) pods' pvcs' phase' ∗
      own_occupied_pods γ pods' ∗
      own_occupied_pvcs γ pvcs' ∗
      own_missing_pod_reservations γ sts pods' ∗
      own_missing_pvc_reservations γ sts pvcs' ∗
      ⌜ current_state_matches sts pods' pvcs' ∨
        (pods_progress_observed pods pods' ∧ match_distance sts pods' pvcs' < match_distance sts pods pvcs) ⌝
  }}}.

Definition syncStatefulSet_stability_spec γ l namespace name sts dq pods pvcs : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ statefulset_owned_resources γ sts (stability_fractions dq) pods pvcs Quiescent ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches sts pods pvcs ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (err : interface.t), RET #err;
      statefulset_owned_resources γ sts (stability_fractions dq) pods pvcs Quiescent
  }}}.

End specs.
