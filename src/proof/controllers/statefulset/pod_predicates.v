From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.controllers.statefulset Require Export pvc.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
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

Definition pod_identity_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'),
    pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
  | Some ordinal, Some labels =>
      (ordinal <= go_int32_max_nat)%nat ∧
      pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      pod.(PodV.Spec').(PodSpecV.Hostname') =
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      pod.(PodV.Spec').(PodSpecV.Subdomain') =
        sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
      labels !! statefulset_pod_name_label =
        Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      labels !! pod_index_label = Some (decimal_string ordinal)
  | _, _ => False
  end.

#[global] Instance pod_identity_matches_decision sts pod :
    Decision (pod_identity_matches sts pod).
Proof. unfold pod_identity_matches. destruct parse_member_name, (pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')); apply _. Defined.

(* Go map insertion overwrites an earlier volume with the same name, so the
   left fold preserves the last volume from the Pod's volume slice. *)
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
      match volume.(VolumeV.VolumeSource').(VolumeSourceV.PersistentVolumeClaim') with
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
  destruct volume.(VolumeV.VolumeSource').(VolumeSourceV.PersistentVolumeClaim');
    apply _.
Defined.

Definition pod_storage_matches (set : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_pod_ordinal
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name') with
  | Some ordinal =>
      (ordinal <= go_int32_max_nat)%nat ∧
      Forall
        (pod_volume_claim_matches
          (pod_volumes_map_of_list pod.(PodV.Spec').(PodSpecV.Volumes'))
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

(* The template-controlled PodSpec fields checked by podSpecMatches after
   removing the identity and storage fields managed in place. *)
Parameter pod_immutable_matches : StatefulSetV.t → PodV.t → Prop.
Axiom pod_immutable_matches_decision : ∀ sts pod,
  Decision (pod_immutable_matches sts pod).
#[global] Existing Instance pod_immutable_matches_decision.

(* A Pod produced from the StatefulSet's template already agrees with every
   template-controlled field checked by [pod_immutable_matches]. Replacing its
   ObjectMeta preserves that agreement because [PodV.update_objectmeta] does
   not change the PodSpec. Identity and storage fields are intentionally not
   covered here: [newStatefulSetPod] establishes them separately through
   [updateIdentity] and [updateStorage]. *)
Axiom pod_from_template_immutable_matches : ∀ sts pod meta,
  controller.pod_from_template
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template') pod →
  pod_immutable_matches sts (PodV.update_objectmeta pod meta).

Definition pod_match (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod_identity_matches sts pod ∧
  pod_storage_matches sts pod ∧
  pod_immutable_matches sts pod.

#[global] Instance pod_match_decision sts pod : Decision (pod_match sts pod).
Proof. unfold pod_match. apply _. Defined.

End proof.

