From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.statefulset Require Export delete_pod.
From New.proof.controllers.statefulset Require Export pod_identity.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.kubernetes_model.tx Require Export update.

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

(* Existing Pods are updated only to repair mutable identity metadata. The
   immutable Hostname, Subdomain, and Volumes fields are initialized before
   creation and are never part of this update input. *)
Definition prepare_stateful_pod_update (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) : PodV.t :=
  if decide (pod_identity_matches set pod)
  then pod
  else update_identity set pod ordinal.

Definition stateful_pod_update_input (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) (update_input : PodV.t) : Prop :=
  update_input = prepare_stateful_pod_update set pod ordinal.

(* The first disjunct covers the early no-op return. Otherwise the repaired
   metadata must be accepted by Kubernetes update validation. *)
Definition stateful_pod_update_admissible
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat) : Prop :=
  pod_identity_matches set pod ∨
  let update_input := update_identity set pod ordinal in
  PodV.valid update_input ∧
  ObjectMetaV.valid_simple_update
    pod.(PodV.ObjectMeta') update_input.(PodV.ObjectMeta') ∧
  ObjectSpecV.valid_update
    (ObjectSpecV.PodSpec pod.(PodV.Spec'))
    (ObjectSpecV.PodSpec update_input.(PodV.Spec')).

Lemma stateful_pod_update_input_identity set pod ordinal :
  ¬ pod_identity_matches set pod →
  stateful_pod_update_input set pod ordinal
    (update_identity set pod ordinal).
Proof.
  intros Hidentity.
  unfold stateful_pod_update_input, prepare_stateful_pod_update.
  destruct (decide (pod_identity_matches set pod))
    as [Hidentity'|Hidentity']; [contradiction|done].
Qed.

Lemma stateful_pod_update_admissible_valid set pod ordinal :
  stateful_pod_update_admissible set pod ordinal →
  ¬ pod_identity_matches set pod →
  PodV.valid (update_identity set pod ordinal) ∧
  ObjectMetaV.valid_simple_update
    pod.(PodV.ObjectMeta')
    (update_identity set pod ordinal).(PodV.ObjectMeta') ∧
  ObjectSpecV.valid_update
    (ObjectSpecV.PodSpec pod.(PodV.Spec'))
    (ObjectSpecV.PodSpec
      (update_identity set pod ordinal).(PodV.Spec')).
Proof.
  intros [Hidentity|Hadmissible] Hnot_identity.
  - contradiction.
  - exact Hadmissible.
Qed.

Lemma valid_simple_update_pod_key_uid pod pod' :
  ObjectMetaV.valid_simple_update
    pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') →
  PodV.key pod = PodV.key pod' ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.UID') =
    pod'.(PodV.ObjectMeta').(ObjectMetaV.UID').
Proof.
  intros (Hname & _ & Hnamespace & _ & Huid & _).
  split.
  - rewrite /PodV.key /PodV.meta_key Hname Hnamespace. done.
  - symmetry. exact Huid.
Qed.

Lemma wp_updateStatefulPod γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    dq_set dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_valid" ∷ ⌜ PodV.valid pod ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              ordinal ⌝ ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max ⌝ ∗
      "%Hpod_not_deleting" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hupdate_admissible" ∷
        ⌜ stateful_pod_update_admissible set pod ordinal ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))
  }}}
    @! statefulset.updateStatefulPod #set_l #pod_l
  {{{ (pod' : PodV.t), RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_valid" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hpod_key" ∷ ⌜ PodV.key pod' = PodV.key pod ⌝ ∗
      "%Hpod_uid" ∷
        ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') =
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod'.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      ( ("%Hnoop" ∷
            ⌜ pod_identity_matches set pod ∧ pod' = pod ⌝)
        ∨
        ( "%Hnot_ready" ∷
            ⌜ ¬ pod_identity_matches set pod ⌝ ∗
          "%Hupdate_input" ∷
            ⌜ stateful_pod_update_input set pod ordinal
                (update_identity set pod ordinal) ⌝ ∗
          "%Hmeta_updated" ∷
            ⌜ ObjectMetaV.updated
                (update_identity set pod ordinal).(PodV.ObjectMeta')
                pod'.(PodV.ObjectMeta') ⌝ ∗
          "%Hspec_updated" ∷
            ⌜ ObjectSpecV.updated
                (ObjectSpecV.PodSpec
                  (update_identity set pod ordinal).(PodV.Spec'))
                (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_identityMatches set_l pod_l set pod dq_set dq_pod
    with "[$Hset $Hpod]").
  { iPureIntro. exact Hpod_name_len. }
  iIntros (identity_ret)
    "(Hset & Hpod & %Hidentity_spec)".
  destruct identity_ret.
  - assert (Hidentity : pod_identity_matches set pod).
    { apply Hidentity_spec. done. }
    wp_auto.
    iApply ("HΦ" $! pod).
    iFrame "Hset Hpod Hown_meta Hown_spec".
    do 3 (iSplit; first done).
    iLeft. iPureIntro. split; done.
  - assert (Hnot_identity : ¬ pod_identity_matches set pod).
    { intros Hidentity. apply Hidentity_spec in Hidentity. done. }
    pose proof
      (stateful_pod_update_admissible_valid
        set pod ordinal Hupdate_admissible Hnot_identity)
      as (Hinput_valid & Hvalid_meta_update & Hvalid_spec_update).
    pose proof
      (valid_simple_update_pod_key_uid
        pod (update_identity set pod ordinal) Hvalid_meta_update)
      as (Hinput_key & Hinput_uid).
    pose proof
      (stateful_pod_update_input_identity
        set pod ordinal Hnot_identity) as Hinput.
    wp_auto.
    iAssert
      (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1)
      as "#Hcorev1".
    { iPkgInit. }
    iEval (rewrite /named) in "Hpod".
    iDestruct "Hpod" as (pod_phy) "[Hpod_ptr Hpod]".
    wp_apply (wp_Pod__DeepCopy
      (package_sem := object_core_v1_sem)
      (meta_v1_sem := object_meta_v1_sem)
      pod_l pod_phy pod dq_pod dq_pod
      with "[$Hcorev1 $Hpod_ptr $Hpod]").
    iIntros (updatedPod_l) "(HupdatedPod & Hpod_ptr & Hpod)".
    iAssert (PodV.deepown_l pod_l pod dq_pod)
      with "[Hpod_ptr Hpod]" as "Hpod".
    { iExists pod_phy. iFrame. }
    wp_auto.
    wp_apply (wp_updateIdentity
      set_l updatedPod_l set pod ordinal dq_set
      with "[$Hset $HupdatedPod]").
    { iPureIntro. split_and!; done. }
    iIntros "(Hset & HupdatedPod & %Hidentity_matches)".
    iEval (rewrite /named) in "HupdatedPod".
    iPoseProof (PodV.deepown_l_split with "HupdatedPod") as
      "(%HupdatedPod_l_not_null & HupdatedPod_typemeta &
        HupdatedPod_objectmeta_l & HupdatedPod_spec_l &
        HupdatedPod_status_l)".
    iDestruct "HupdatedPod_objectmeta_l" as
      (updatedPod_meta_c)
      "[HupdatedPod_objectmeta_field HupdatedPod_objectmeta]".
    iNamedPrefix "HupdatedPod_objectmeta" "HupdatedPod_meta_".
    wp_auto.
    rewrite HupdatedPod_meta_Hdeepown_namespace.
    iCombineNamed "HupdatedPod_meta_*" as
      "HupdatedPod_objectmeta".
    iAssert (ObjectMetaV.deepown updatedPod_meta_c
        (PodV.ObjectMeta' (update_identity set pod ordinal)) 1)
      with "[HupdatedPod_objectmeta]" as
        "HupdatedPod_objectmeta".
    { iNamed "HupdatedPod_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (PodV.objectmeta_ptr updatedPod_l)
        (PodV.ObjectMeta' (update_identity set pod ordinal)) 1)
      with
        "[HupdatedPod_objectmeta_field HupdatedPod_objectmeta]"
      as "HupdatedPod_objectmeta_l".
    { iExists updatedPod_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _
      HupdatedPod_l_not_null
      with "[$HupdatedPod_typemeta $HupdatedPod_objectmeta_l
        $HupdatedPod_spec_l $HupdatedPod_status_l]")
      as "HupdatedPod".
    iAssert (is_pkg_init apimodel) as "#Hapimodel".
    { iPkgInit. }
    wp_apply (wp_State__PodUpdateTx γ model_l
      (update_identity set pod ordinal).(PodV.ObjectMeta').(
        ObjectMetaV.Namespace')
      updatedPod_l (update_identity set pod ordinal)
      (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
      pod.(PodV.ObjectMeta')
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))
      with "[$HupdatedPod $Hown_meta $Hown_spec]").
    { iFrame "#".
      iPureIntro.
      split_and!; done. }
    iIntros (returned_pod_l returned_pod) "Hupdate".
    iNamedPrefix "Hupdate" "Hupdate_".
    wp_auto.
    iApply ("HΦ" $! returned_pod).
    iFrame "Hset Hpod Hupdate_Hown_meta_frag
      Hupdate_Hown_spec_frag".
    do 3 (iSplit; first (iPureIntro; assumption)).
    iRight. iFrame "%".
Qed.

End proof.
