From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export external_wp.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export ordinal.
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

Lemma wp_isTerminating pod_l (pod : PodV.t) dq :
  {{{ PodV.deepown_l pod_l pod dq }}}
    @! statefulset.isTerminating #pod_l
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ ¬ is_pod_alive pod ⌝ ∗
      PodV.deepown_l pod_l pod dq
  }}}.
Proof.
  wp_start as "Hpod".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c) "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]") as "Hpod".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold is_pod_alive.
  split.
  - intros Hnot_null Hdeletion_timestamp_none.
    apply negb_true_iff in Hnot_null.
    apply bool_decide_eq_false in Hnot_null.
    apply Hnot_null.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
  - intros Hnot_alive.
    apply negb_true_iff.
    apply bool_decide_eq_false.
    intros Hnull.
    apply Hnot_alive.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
Qed.

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

(* The pure effect of [updateIdentity] after [ordinalOf] has successfully
   recovered [ordinal] from the Pod name. *)
Definition update_identity (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) : PodV.t :=
  let pod_name := desired_pod_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal in
  let labels : gmap go_string go_string :=
    default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') in
  let labels :=
    <[pod_index_label := decimal_string ordinal]>
      (<[statefulset_pod_name_label := pod_name]> labels) in
  let object_meta :=
    pod.(PodV.ObjectMeta')
      <| ObjectMetaV.Name' := pod_name |>
      <| ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
      <| ObjectMetaV.Labels' := Some labels |> in
  let spec :=
    pod.(PodV.Spec')
      <| PodSpecV.Hostname' := pod_name |>
      <| PodSpecV.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |> in
  pod <| PodV.ObjectMeta' := object_meta |>
      <| PodV.Spec' := spec |>.

Lemma update_identity_identity_matches set pod ordinal :
  (ordinal <= go_int32_max_nat)%nat →
  pod_identity_matches set (update_identity set pod ordinal).
Proof.
  intros Hordinal.
  unfold pod_identity_matches, update_identity.
  cbn -[parse_member_name].
  rewrite (parse_member_name_complete
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (desired_pod_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
    ordinal eq_refl).
  cbn.
  split_and!; try done.
  - rewrite lookup_insert_ne.
    + {
      unfold pod_index_label, statefulset_pod_name_label.
      intros Hlabels. inversion Hlabels.
    }
    + rewrite lookup_insert_eq. done.
  - rewrite lookup_insert_eq. done.
Qed.

(* [ordinalOf] parses the decimal suffix following the last dash, without
   checking that the preceding parent name belongs to the StatefulSet. *)
Definition pod_ordinal_suffix (pod_name : go_string) : option go_string :=
  match list_find (λ b, b = byte_dash) (reverse pod_name) with
  | Some (idx, _) => Some (reverse (take idx (reverse pod_name)))
  | None => None
  end.

Definition parse_pod_ordinal (pod_name : go_string) : option nat :=
  suffix ← pod_ordinal_suffix pod_name;
  parse_decimal_string suffix.

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

Lemma wp_identityMatches set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    dq_set dq_pod :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.identityMatches #set_l #pod_l
  {{{ (ret : bool), RET #ret;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hret" ∷ ⌜ ret = true ↔ pod_identity_matches set pod ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iDestruct "Hset_spec_l" as (set_spec_c) "[Hset_spec_field Hset_spec]".
  iNamedPrefix "Hset_spec" "Hset_spec_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  iDestruct "Hpod_spec_l" as (pod_spec_c) "[Hpod_spec_field Hpod_spec]".
  iNamedPrefix "Hpod_spec" "Hpod_spec_".
  Ltac restore_identity_objects set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null :=
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod".
  Ltac finish_identity_false set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null :=
    restore_identity_objects set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null;
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_with_labels set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null labels Hlabels Hlabels_none Hmanagedfields_none :=
    iAssert (match pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
        | Some vl => ∃ cl,
            v1.ObjectMeta.Labels' pod_meta_c ↦${dq_pod} cl ∗ ⌜ cl = vl ⌝
        | None => True
        end)%I with "[Hpod_labels]" as "Hpod_meta_Hdeepown_labels_some";
    [ rewrite Hlabels; iExists labels; iFrame; done | ];
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame;
      repeat (iSplit; first (iPureIntro; done));
      iSplit;
      [ iPureIntro; rewrite Hlabels; exact Hlabels_none | ];
      repeat (iSplit; first (iPureIntro; done));
      iPureIntro; exact Hmanagedfields_none
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_without_labels set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null Hlabels Hlabels_none Hmanagedfields_none :=
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame;
      do 9 (iSplit; first (iPureIntro; assumption));
      iSplit;
      [ iPureIntro; rewrite Hlabels; exact Hlabels_none | ];
      iSplit; [ rewrite Hlabels; done | ];
      do 3 (iSplit; first (iPureIntro; assumption));
      iPureIntro; exact Hmanagedfields_none
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len. }
  iIntros (parent ordinal) "%Hparent".
  wp_auto.
  destruct (decide (pod_identity_matches set pod)) as [Hmatches|Hnot_matches].
  2: {
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_apply (wp_podName (v1.ObjectMeta.Name' set_meta_c) ordinal with "[]").
    { iPureIntro. word. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
      eqn:Hlabels.
    - iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_c)
        "[Hpod_labels %Hlabels_c]".
      subst labels_c.
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
      }
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_apply (wp_strconv_Itoa with "[]").
      { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
        iPureIntro. word. }
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
      }
      exfalso.
      apply Hnot_matches.
      assert (Hcanonical :
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal)).
      { rewrite -Hpod_meta_Hdeepown_name -Hset_meta_Hdeepown_name. exact e. }
      assert (Hparse : parse_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
          Some (sint.nat ordinal)).
      { by apply parse_member_name_complete. }
      pose proof (proj1 (Hparent (v1.ObjectMeta.Name' set_meta_c))
        (conj eq_refl (conj l e))) as Hmember.
      destruct Hmember as (member_ordinal & Hmember_bound & Hmember_name).
      assert (Hmember_ordinal : member_ordinal = sint.nat ordinal).
      { apply (desired_pod_name_inj (v1.ObjectMeta.Name' set_meta_c)).
        rewrite -Hmember_name. exact e. }
      subst member_ordinal.
      assert (Hpod_name_nonempty :
          v1.ObjectMeta.Name' pod_meta_c ≠ ""%go).
      { intros Hempty.
        pose proof (desired_pod_name_has_dash
          (v1.ObjectMeta.Name' set_meta_c) (sint.nat ordinal)) as Hdash.
        unfold desired_pod_name in Hdash.
        rewrite -e Hempty in Hdash.
        rewrite elem_of_nil in Hdash. exact Hdash. }
      assert (Hpod_name_lookup :
          labels !! statefulset_pod_name_label =
            Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
      { destruct (labels !! statefulset_pod_name_label) as [label|]
          eqn:Hlookup.
        - simpl in e3. f_equal.
          rewrite -Hpod_meta_Hdeepown_name. exact e3.
        - simpl in e3. exfalso. apply Hpod_name_nonempty. by rewrite -e3. }
      assert (Hpod_index_lookup :
          labels !! pod_index_label = Some (decimal_string (sint.nat ordinal))).
      { destruct (labels !! pod_index_label) as [label|] eqn:Hlookup.
        - simpl in e4. by f_equal.
        - simpl in e4.
          pose proof (parse_decimal_string_decimal_string
            (sint.nat ordinal)) as Hdecimal.
          rewrite -e4 in Hdecimal. done. }
      unfold pod_identity_matches.
      rewrite Hparse Hlabels.
      repeat split; try done.
      + by rewrite -Hpod_meta_Hdeepown_namespace
          -Hset_meta_Hdeepown_namespace.
      + by rewrite -Hpod_spec_Hdeepown_hostname
          -Hpod_meta_Hdeepown_name.
      + by rewrite -Hpod_spec_Hdeepown_subdomain
          -Hset_spec_Hdeepown_servicename.
    - assert (Hlabels_nil : v1.ObjectMeta.Labels' pod_meta_c = null).
      { apply Hpod_meta_Hdeepown_labels_none. reflexivity. }
      rewrite Hlabels_nil.
      wp_auto.
      wp_if_destruct.
      + rewrite Hlabels_nil.
        wp_auto.
        wp_apply (wp_strconv_Itoa with "[]").
        { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
          iPureIntro. word. }
        wp_if_destruct.
        * exfalso.
          match goal with
          | H : ""%go = decimal_string (sint.nat ordinal) |- _ =>
              pose proof (parse_decimal_string_decimal_string
                (sint.nat ordinal)) as Hdecimal;
              rewrite -H in Hdecimal; done
          end.
        * finish_identity_false_without_labels set_meta_c set dq_set set_l
            set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
            Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none
            Hpod_meta_Hdeepown_managedfields_none.
      + finish_identity_false_without_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
  }
  unfold pod_identity_matches in Hmatches.
  destruct (parse_member_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) as [expected_ordinal|]
    eqn:Hparse; [|done].
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
    eqn:Hlabels; [|done].
  simpl in Hmatches.
  pose proof Hmatches as Hidentity_matches.
  destruct Hmatches as
    (Hordinal_bound & Hnamespace & Hhostname & Hsubdomain &
      Hpod_name_label & Hpod_index_label).
  assert (Hmember : pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  { exists expected_ordinal. split; [done|].
    by apply parse_member_name_sound. }
  assert (Hmember_c : pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (v1.ObjectMeta.Name' pod_meta_c)).
  { rewrite Hpod_meta_Hdeepown_name. exact Hmember. }
  pose proof (proj2
    (Hparent set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')) Hmember_c) as
    (Hparent_eq & Hordinal_nonnegative & Hcanonical).
  assert (Hexpected_ordinal : expected_ordinal = sint.nat ordinal).
  { apply (desired_pod_name_inj
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
    rewrite -(parse_member_name_sound _ _ _ Hparse).
    rewrite Hpod_meta_Hdeepown_name in Hcanonical.
    exact Hcanonical. }
  wp_if_destruct.
  2: { exfalso. word. }
  wp_if_destruct.
  2: { exfalso. apply n. by rewrite Hset_meta_Hdeepown_name. }
  wp_apply (wp_podName
    (v1.ObjectMeta.Name' set_meta_c) ordinal with "[]").
  { iPureIntro. exact Hordinal_nonnegative. }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    unfold desired_pod_name in Hcanonical.
    rewrite -Hset_meta_Hdeepown_name in Hcanonical.
    exact Hcanonical.
  }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_meta_Hdeepown_namespace Hset_meta_Hdeepown_namespace.
  }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_spec_Hdeepown_hostname Hpod_meta_Hdeepown_name.
  }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_spec_Hdeepown_subdomain Hset_spec_Hdeepown_servicename.
  }
  iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_c)
    "[Hpod_labels %Hlabels_c]".
  subst labels_c.
  wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
  rewrite Hpod_name_label /=.
  wp_if_destruct.
  2: { exfalso. apply n. by rewrite Hpod_meta_Hdeepown_name. }
  wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
  rewrite Hpod_index_label /=.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_if_destruct.
  2: { exfalso. done. }
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iCombineNamed "Hset_spec_H*" as "Hset_spec".
  iAssert (StatefulSetSpecV.deepown set_spec_c
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec]" as "Hset_spec".
  { iNamed "Hset_spec". iFrame. done. }
  iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec_field Hset_spec]" as "Hset_spec_l".
  { iExists set_spec_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
    as "Hset".
  iAssert (match pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
      | Some vl => ∃ cl,
          v1.ObjectMeta.Labels' pod_meta_c ↦${dq_pod} cl ∗ ⌜ cl = vl ⌝
      | None => True
      end)%I with "[Hpod_labels]" as "Hpod_meta_Hdeepown_labels_some".
  { rewrite Hlabels. iExists labels. iFrame. done. }
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame.
    repeat (iSplit; first (iPureIntro; done)).
    iSplit.
    { iPureIntro. rewrite Hlabels. exact Hpod_meta_Hdeepown_labels_none. }
    repeat (iSplit; first (iPureIntro; done)).
    iPureIntro. exact Hpod_meta_Hdeepown_managedfields_none. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iCombineNamed "Hpod_spec_H*" as "Hpod_spec".
  iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
    with "[Hpod_spec]" as "Hpod_spec".
  { iNamed "Hpod_spec". iFrame. done. }
  iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
    with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l".
  { iExists pod_spec_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
    as "Hpod".
  iApply ("HΦ" $! true).
  iFrame.
  iPureIntro. split; [|done].
  intros _.
  unfold pod_identity_matches.
  rewrite Hparse Hlabels.
  exact Hidentity_matches.
Qed.

Lemma wp_storageMatches set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    dq_set dq_pod :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <=
          go_int_max ⌝
  }}}
    @! statefulset.storageMatches #set_l #pod_l
  {{{ (ret : bool), RET #ret;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hret" ∷ ⌜ ret = true ↔ pod_storage_matches set pod ⌝
  }}}.
Proof. Admitted.

(* The ordinal and name preconditions exclude the failure result (-1) from
   ordinalOf. The helper mutates the Pod in place, so it requires full Pod
   ownership and returns an existentially quantified updated pure Pod. *)
Lemma wp_updateIdentity set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) dq_set :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝ ∗
      "%Hpod_hostname_len" ∷
        ⌜ length pod.(PodV.ObjectMeta').(ObjectMetaV.Name') <= 63 ⌝ ∗
      "%Hset_meta_valid" ∷ ⌜ ObjectMetaV.valid StatefulSetV.kind set.(StatefulSetV.ObjectMeta') ⌝ ∗
      "%Hset_spec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hvalid" ∷
        ⌜ KObjectV.valid_named_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (KObjectV.Pod pod) ⌝
  }}}
    @! statefulset.updateIdentity #set_l #pod_l
  {{{ pod', RET #();
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod' 1 ∗
      "%Hmember_name" ∷
        ⌜ pod_has_int32_member_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            pod'.(PodV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hpod_namespace" ∷
        ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hidentity_matches" ∷ ⌜ pod_identity_matches set pod' ⌝ ∗
      "%Hstorage_matches" ∷
        ⌜ pod_storage_matches set pod' ↔ pod_storage_matches set pod ⌝ ∗
      "%Himmutable_matches" ∷
        ⌜ pod_immutable_matches set pod' ↔ pod_immutable_matches set pod ⌝ ∗
      "%Hparent" ∷
        ⌜ obj_parent_ref_is (KObjectV.Pod pod') StatefulSetV.kind
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ↔
            obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Halive" ∷ ⌜ is_pod_alive pod' ↔ is_pod_alive pod ⌝ ∗
      "%Hvalid" ∷
        ⌜ KObjectV.valid_named_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (KObjectV.Pod pod') ⌝
  }}}.
Proof. Admitted.

(* updateStorage only rewrites Pod volumes.  In particular, it establishes the
   storage predicate without changing whether the identity predicate holds. *)
Lemma wp_updateStorage set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) dq_set :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝ ∗
      "%Hset_spec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hclaim_names_valid" ∷
        ⌜ ∀ claim_template_name,
            claim_template_name ∈ pvc_claim_template_names set →
            valid_name PersistentVolumeClaimV.kind (desired_pvc_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              claim_template_name ordinal) ⌝ ∗
      "%Hvalid" ∷
        ⌜ KObjectV.valid_named_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (KObjectV.Pod pod) ⌝
  }}}
    @! statefulset.updateStorage #set_l #pod_l
  {{{ pod', RET #();
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod' 1 ∗
      "%Hmember_name" ∷
        ⌜ pod_has_int32_member_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            pod'.(PodV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hpod_meta" ∷
        ⌜ pod'.(PodV.ObjectMeta') = pod.(PodV.ObjectMeta') ⌝ ∗
      "%Hstorage_matches" ∷ ⌜ pod_storage_matches set pod' ⌝ ∗
      "%Hidentity_matches" ∷
        ⌜ pod_identity_matches set pod' ↔ pod_identity_matches set pod ⌝ ∗
      "%Himmutable_matches" ∷
        ⌜ pod_immutable_matches set pod' ↔ pod_immutable_matches set pod ⌝ ∗
      "%Hparent" ∷
        ⌜ obj_parent_ref_is (KObjectV.Pod pod') StatefulSetV.kind
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ↔
            obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Halive" ∷ ⌜ is_pod_alive pod' ↔ is_pod_alive pod ⌝ ∗
      "%Hvalid" ∷
        ⌜ KObjectV.valid_named_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (KObjectV.Pod pod') ⌝
  }}}.
Proof. Admitted.

Lemma wp_newStatefulSetPod (gv : schema.GroupVersion.t) set_l (set : StatefulSetV.t) (ordinal : w64) dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "%Hgv_group" ∷ ⌜ gv.(schema.GroupVersion.Group') = "apps"%go ⌝ ∗
      "%Hgv_version" ∷ ⌜ gv.(schema.GroupVersion.Version') = "v1"%go ⌝ ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "%Hset_meta_valid" ∷ ⌜ ObjectMetaV.valid StatefulSetV.kind set.(StatefulSetV.ObjectMeta') ⌝ ∗
      "%Hset_name_short" ∷
        ⌜ length set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hset_spec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Htemplate_valid" ∷ ⌜ PodTemplateSpecV.valid set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') ⌝ ∗
      "%Hordinal_nonnegative" ∷ ⌜ 0 <= sint.Z ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (sint.nat ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_valid" ∷
        ⌜ valid_name PodV.kind
            (desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') (sint.nat ordinal)) ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat (length (desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal))) <= go_int_max ⌝ ∗
      "%Hpod_hostname_len" ∷
        ⌜ length (desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal)) <= 63 ⌝ ∗
      "%Hclaim_names_valid" ∷
        ⌜ ∀ claim_template_name,
            claim_template_name ∈ pvc_claim_template_names set →
            valid_name PersistentVolumeClaimV.kind (desired_pvc_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              claim_template_name (sint.nat ordinal)) ⌝
  }}}
    @! statefulset.newStatefulSetPod #set_l #ordinal
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hkey" ∷ ⌜ PodV.key pod = desired_pod_key set (sint.nat ordinal) ⌝ ∗
      "%Hparent" ∷
        ⌜ obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid" ∷
        ⌜ KObjectV.valid_named_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (KObjectV.Pod pod) ⌝ ∗
      "%Halive" ∷ ⌜ is_pod_alive pod ⌝ ∗
      "%Hmatch" ∷ ⌜ pod_match set pod ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_bind ((global_addr apps_v1.SchemeGroupVersion) @!
    (go.PointerType schema.GroupVersion) @! "WithKind" #"StatefulSet"%go)%E.
  wp_apply (New.proof.k8s_io.api.apps.v1.wp_SchemeGroupVersion__WithKind
    (schema_sem := @code.k8s_io.api.apps.v1.v1.import_schema_Assumption
      _ _ _ _ object_apps_v1_sem) gv "StatefulSet"%go with "[]").
  { iFrame "#". }
  iIntros (gvk) "%Hgvk".
  destruct Hgvk as (Hgvk_group & Hgvk_version & Hgvk_kind).
  wp_auto.
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  wp_bind (@! statefulset.meta_v1.NewControllerRef
    #(interface.mk_ok (go.PointerType apps_v1.StatefulSet) (#set_l)) #gvk)%E.
  change (statefulset.meta_v1.NewControllerRef) with meta_v1.NewControllerRef.
  wp_apply (v1.wp_NewControllerRef_StatefulSet with "[Hset_objectmeta_l]").
  { iFrame "# Hset_objectmeta_l".
    iPureIntro.
    rewrite Hgvk_group Hgvk_version Hgvk_kind Hgv_group Hgv_version.
    split; done. }
  iIntros (controller_ref_l controller_ref)
    "(Hcontroller_ref & %Hcontroller_ref_parent & %Hcontroller_ref_valid & Hset_objectmeta_l)".
  rewrite Hgvk_kind in Hcontroller_ref_parent.
  wp_auto.
  iDestruct "Hset_spec_l" as (set_spec_c)
    "[Hset_spec_field Hset_spec_deepown]".
  iNamedPrefix "Hset_spec_deepown" "Hset_spec_deepown_".
  iDestruct (struct_fields_split with "Hset_spec_field") as
    "[Hset_spec_fields %Hset_spec_l_not_null]".
  iNamedPrefix "Hset_spec_fields" "Hset_spec_fields_".
  change ((set_l.[apps_v1.StatefulSet.t, "Spec"])
      .[apps_v1.StatefulSetSpec.t, "Template"]) with
    ((StatefulSetV.spec_ptr set_l).[v1.StatefulSetSpec.t, "Template"]).
  wp_apply (controller.wp_GetPodFromTemplate_StatefulSet
    ((StatefulSetV.spec_ptr set_l).[v1.StatefulSetSpec.t, "Template"])
    (interface.mk_ok (go.PointerType apps_v1.StatefulSet) (#set_l))
    controller_ref_l dq (v1.StatefulSetSpec.Template' set_spec_c)
    set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') set_l
    set.(StatefulSetV.ObjectMeta') controller_ref with
    "[Hset_spec_fields_Template Hset_spec_deepown_Hdeepown_template
      Hset_objectmeta_l Hcontroller_ref]").
  { iFrame "#".
    iSplitL "Hset_spec_fields_Template".
    { unfold object_core_v1_sem. iExact "Hset_spec_fields_Template". }
    iFrame.
    iPureIntro. split_and!; done. }
  iIntros (pod_l pod)
    "(Hpod & %Hparent & %Hvalid_nameless & %Hpod_deletion_timestamp &
      %Hpod_from_template & Hset_spec_fields_Template &
      Hset_spec_deepown_Hdeepown_template & Hset_objectmeta_l)".
  wp_auto.
  iCombineNamed "Hset_spec_fields_*" as "Hset_spec_fields".
  iAssert (((StatefulSetV.spec_ptr set_l) ↦{dq} set_spec_c)%I)
    with "[Hset_spec_fields]" as "Hset_spec_field".
  { iApply (struct_fields_combine (V:=v1.StatefulSetSpec.t) _ _ _
      Hset_spec_l_not_null).
    simpl. iNamed "Hset_spec_fields". iFrame. }
  iAssert (StatefulSetSpecV.deepown set_spec_c set.(StatefulSetV.Spec') dq)
    with "[Hset_spec_deepown_Hdeepown_replicas_some
      Hset_spec_deepown_Hdeepown_template
      Hset_spec_deepown_Hdeepown_volumeclaimtemplates]" as
      "Hset_spec_deepown".
  { rewrite /StatefulSetSpecV.deepown. iFrame.
    iPureIntro. done. }
  iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
      set.(StatefulSetV.Spec') dq)
    with "[Hset_spec_field Hset_spec_deepown]" as "Hset_spec_l".
  { iExists set_spec_c. iFrame. }
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  rewrite Hset_meta_Hdeepown_name.
  wp_apply (wp_podName
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal with "[]").
  { iPureIntro. exact Hordinal_nonnegative. }
  iDestruct (struct_fields_split with "Hpod_objectmeta_field") as
    "[Hpod_meta_fields %Hpod_meta_l_not_null]".
  iNamedPrefix "Hpod_meta_fields" "Hpod_meta_fields_".
  set pod_name := desired_pod_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') (sint.nat ordinal).
  set pod_meta := pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := pod_name |>.
  set pod_named := PodV.update_objectmeta pod pod_meta.
  iCombineNamed "Hpod_meta_fields_*" as "Hpod_meta_fields".
  iAssert (((PodV.objectmeta_ptr pod_l) ↦
      (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>))%I)
    with "[Hpod_meta_fields]" as "Hpod_objectmeta_field".
  { iApply (struct_fields_combine (V:=v1.ObjectMeta.t) _ _ _
      Hpod_meta_l_not_null).
    simpl. iNamed "Hpod_meta_fields". iFrame. }
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown
      (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>) pod_meta 1)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { rewrite /ObjectMetaV.deepown /pod_meta.
    iNamed "Hpod_objectmeta". iFrame. iPureIntro. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l) pod_meta 1)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>). iFrame. }
  iPoseProof (PodV.deepown_l_merge pod_l pod pod_meta 1 Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]") as
    "Hpod".
  iAssert (PodV.deepown_l pod_l pod_named 1) with "[Hpod]" as "Hpod".
  { unfold pod_named. iExact "Hpod". }
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq)
    with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as
    "Hset".
  assert (Hvalid_named : KObjectV.valid_named_create PodV.kind
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
      (KObjectV.Pod pod_named)).
  { apply KObjectV.valid_nameless_pod_set_name; [done| |done].
    unfold pod_name, desired_pod_name.
    destruct set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name'); done. }
  assert (Himmutable_named : pod_immutable_matches set pod_named).
  { apply (pod_from_template_immutable_matches set pod pod_meta).
    exact Hpod_from_template. }
  assert (Hparent_named : obj_parent_ref_is (KObjectV.Pod pod_named)
      StatefulSetV.kind set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')).
  { exact Hparent. }
  assert (Halive_named : is_pod_alive pod_named).
  { exact Hpod_deletion_timestamp. }
  wp_apply (wp_updateIdentity set_l pod_l set pod_named
    (sint.nat ordinal) dq with "[$Hset $Hpod]").
  { iSplit.
    { iPureIntro. unfold pod_named, pod_meta, pod_name. done. }
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    by iPureIntro. }
  iIntros (pod_identity)
    "(Hset & Hpod & %Hmember_identity & %Hname_identity &
      %Hnamespace_identity & %Hidentity_matches & %Hstorage_identity &
      %Himmutable_identity & %Hparent_identity & %Halive_identity &
      %Hvalid_identity)".
  wp_auto.
  assert (Hpod_identity_name :
      pod_identity.(PodV.ObjectMeta').(ObjectMetaV.Name') =
        desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          (sint.nat ordinal)).
  { rewrite Hname_identity. unfold pod_named, pod_meta, pod_name. done. }
  wp_apply (wp_updateStorage set_l pod_l set pod_identity
    (sint.nat ordinal) dq with "[$Hset $Hpod]").
  { iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iSplit.
    { iPureIntro. rewrite Hpod_identity_name. exact Hpod_name_len. }
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    by iPureIntro. }
  iIntros (pod_storage)
    "(Hset & Hpod & %Hmember_storage & %Hmeta_storage &
      %Hstorage_matches & %Hidentity_storage & %Himmutable_storage &
      %Hparent_storage & %Halive_storage & %Hvalid_storage)".
  wp_auto.
  iApply ("HΦ" $! pod_l pod_storage).
  iFrame "Hset Hpod".
  iPureIntro.
  split_and!.
  - unfold PodV.key, PodV.meta_key, desired_pod_key.
    rewrite Hmeta_storage Hnamespace_identity Hpod_identity_name.
    done.
  - apply (proj2 Hparent_storage).
    apply (proj2 Hparent_identity).
    exact Hparent_named.
  - exact Hvalid_storage.
  - apply (proj2 Halive_storage).
    apply (proj2 Halive_identity).
    exact Halive_named.
  - unfold pod_match.
    split_and!.
    + apply (proj2 Hidentity_storage). exact Hidentity_matches.
    + exact Hstorage_matches.
    + apply (proj2 Himmutable_storage).
      apply (proj2 Himmutable_identity).
      exact Himmutable_named.
Qed.

Lemma wp_filterPodsForStatefulSet set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t) dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
      "%Hpod_name_len" ∷ ⌜ ∀ pod, pod ∈ pods → Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.filterPodsForStatefulSet #set_l #pods_sl
  {{{ result_sl ptrs', RET #result_sl;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      result_sl ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';
        filter (λ pod, pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (result_sl0) "[Hresult0 Hown_result_cap]".
  set result0 := {|
    slice.ptr := result_sl0;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hlen.
  set set_name := set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name').
  set P := (λ pod, pod_has_int32_member_name set_name
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set I := (∃ (i: w64) (pod_ptr_value: loc) (result: slice.t) (ptrs': list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs' ∗
    "Hlist_pre" ∷ ([∗ list] ptr;pod ∈ ptrs';filter P (take (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hlist_post" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert (I) with "[i set Hset pod result Hpods Hresult0 Hown_result_cap]" as "Hloop_inv".
  { iExists (W64 0), (zero_val loc), result0, [].
    rewrite !take_0 !filter_nil !big_sepL2_nil.
    iFrame.
    iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hpods_sl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pod with "Hlist_post") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    { iPureIntro.
      apply Hpod_name_len.
      apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      exact Hthis_pod_lookup. }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_spec_l $Hthis_status_l]") as "Hthis".
    wp_if_destruct.
    + wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (sl0) "[Hsl0 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
      iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]).
      assert (P this_pod) as Hthis_member.
      { unfold P.
        apply (proj1 Hmember). done. }
      assert (filter P (take (sint.nat i) pods) ++ [this_pod] =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iPureIntro. word.
    + 
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs'.
      assert (¬ P this_pod) as Hthis_not_member.
      { unfold P.
        intros Hthis_member.
        pose proof (proj2 Hmember Hthis_member) as Hfalse.
        done. }
      assert (filter P (take (sint.nat i) pods) =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. word.
  - assert (take (sint.nat i) pods = pods) as ->.
    { assert (sint.nat i = length ptrs) as Hi_len.
      { rewrite Hpods_sl_len1. word. }
      rewrite Hlen in Hi_len. rewrite Hi_len.
      apply take_ge. lia. }
    iApply "HΦ". iFrame.
Qed.

End proof.
