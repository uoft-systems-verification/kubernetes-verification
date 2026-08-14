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

(* Existing Pods are updated only to repair mutable identity metadata. These
   conditions are needed only when identity repair causes an update to be
   issued; the early no-op branch does not need update admissibility. The
   immutable Hostname, Subdomain, and Volumes fields are initialized before
   creation and are never part of the update input. *)
Definition stateful_pod_update_admissible
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat) : Prop :=
  let update_input := update_identity set pod ordinal in
  PodV.valid update_input ∧
  ObjectMetaV.valid_simple_update
    pod.(PodV.ObjectMeta') update_input.(PodV.ObjectMeta') ∧
  ObjectSpecV.valid_update
    (ObjectSpecV.PodSpec pod.(PodV.Spec'))
    (ObjectSpecV.PodSpec update_input.(PodV.Spec')).

Lemma statefulset_pod_name_label_valid :
  valid_label_name statefulset_pod_name_label.
Proof.
  right.
  exists "statefulset.kubernetes.io"%go, "pod-name"%go.
  split; first done.
  split.
  - unfold valid_dns1123_subdomain, dns1123_subdomain_syntax.
    cbn. repeat split.
    all: unfold dns1123_lower_alphanumeric, dns1123_subdomain_byte,
      dns1123_label_byte, byte_dot, byte_dash.
    Timeout 10 all: vm_compute.
    all: intuition congruence.
  - unfold valid_qualified_name, qualified_name_syntax.
    cbn. repeat split.
    all: unfold label_alphanumeric, label_extended_character,
      byte_underscore, byte_dot, byte_dash.
    Timeout 10 all: vm_compute.
    all: intuition congruence.
Qed.

Lemma pod_index_label_valid :
  valid_label_name pod_index_label.
Proof.
  right.
  exists "apps.kubernetes.io"%go, "pod-index"%go.
  split; first done.
  split.
  - unfold valid_dns1123_subdomain, dns1123_subdomain_syntax.
    cbn. repeat split.
    all: unfold dns1123_lower_alphanumeric, dns1123_subdomain_byte,
      dns1123_label_byte, byte_dot, byte_dash.
    Timeout 10 all: vm_compute.
    all: intuition congruence.
  - unfold valid_qualified_name, qualified_name_syntax.
    cbn. repeat split.
    all: unfold label_alphanumeric, label_extended_character,
      byte_underscore, byte_dot, byte_dash.
    Timeout 10 all: vm_compute.
    all: intuition congruence.
Qed.

Lemma stateful_pod_update_admissible_of_valid set pod ordinal :
  PodV.valid pod →
  PodV.key pod = desired_pod_key set ordinal →
  valid_dns1123_label
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') →
  stateful_pod_update_admissible set pod ordinal.
Proof.
  intros Hpod_valid Hpod_key Hname_valid.
  pose proof (f_equal KKey.Name' Hpod_key) as Hpod_name.
  pose proof (f_equal KKey.Namespace' Hpod_key) as Hpod_namespace.
  simpl in Hpod_name, Hpod_namespace.
  destruct Hpod_valid as
    (Htypemeta & Hresource_version & Hmeta_valid &
      Hspec_valid & Hstatus_valid).
  pose proof Hname_valid as (_ & Hname_length).
  assert (Hdecimal_length :
      length (decimal_string ordinal) ≤ 63).
  { assert (length (decimal_string ordinal) ≤
        length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
    { rewrite Hpod_name /desired_pod_name !app_length /=. lia. }
    lia. }
  assert (Hlabels_valid :
      valid_labels
        (Some
          (<[pod_index_label := decimal_string ordinal]>
            (<[statefulset_pod_name_label :=
                desired_pod_name
                  set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                  ordinal]>
              (default ∅
                pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')))))).
  { assert (Hpod_name_label_valid :
        valid_labels
          (Some
            (<[statefulset_pod_name_label :=
                desired_pod_name
                  set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                  ordinal]>
              (default ∅
                pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'))))).
    { apply valid_labels_insert.
      - exact (ObjectMetaV.valid_labels_of_valid _ Hmeta_valid).
      - apply statefulset_pod_name_label_valid.
      - rewrite -Hpod_name.
        by apply valid_label_value_of_valid_dns1123_label. }
    pose proof
      (valid_labels_insert
        (Some
          (<[statefulset_pod_name_label :=
              desired_pod_name
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                ordinal]>
            (default ∅
              pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'))))
        pod_index_label (decimal_string ordinal)
        Hpod_name_label_valid pod_index_label_valid
        (valid_label_value_decimal_string _ Hdecimal_length))
      as Hlabels_valid.
    exact Hlabels_valid. }
  assert (Hupdated_valid :
      PodV.valid (update_identity set pod ordinal)).
  { unfold PodV.valid, update_identity. cbn.
    split_and!; try done.
    unfold ObjectMetaV.valid in Hmeta_valid |- *.
    destruct Hmeta_valid as
      (Hgenerate_name & Hname_nonempty & Hname_valid' &
        Hnamespace_nonempty & Hnamespace_valid & Huid_valid &
        _ & Hannotations_valid & Howner_references_valid &
        Hfinalizers_valid & Hmanaged_fields_valid & Hselflink).
    split_and!; try done.
    - by rewrite -Hpod_name.
    - by rewrite -Hpod_name.
    - by rewrite -Hpod_namespace.
    - by rewrite -Hpod_namespace. }
  assert (Hmeta_update :
      ObjectMetaV.valid_simple_update
        pod.(PodV.ObjectMeta')
        (update_identity set pod ordinal).(PodV.ObjectMeta')).
  { unfold ObjectMetaV.valid_simple_update, update_identity. cbn.
    split_and!; try done. }
  assert (Hspec_update :
      ObjectSpecV.valid_update
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))
        (ObjectSpecV.PodSpec
          (update_identity set pod ordinal).(PodV.Spec'))).
  { unfold ObjectSpecV.valid_update, update_identity. cbn.
    apply PodSpecV.valid_update_refl. }
  split_and!; done.
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
      "%Hpod_desired_key" ∷
        ⌜ PodV.key pod = desired_pod_key set ordinal ⌝ ∗
      "%Hpod_name_valid" ∷
        ⌜ valid_dns1123_label
            pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_not_deleting" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
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
      "%Hpod_spec" ∷ ⌜ pod'.(PodV.Spec') = pod.(PodV.Spec') ⌝ ∗
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
  pose proof (pod_name_length_le_go_int_max_of_valid pod Hpod_valid)
    as Hpod_name_len.
  pose proof (f_equal KKey.Name' Hpod_desired_key) as Hpod_name.
  simpl in Hpod_name.
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
    do 4 (iSplit; first done).
    iLeft. iPureIntro. split; done.
  - assert (Hnot_identity : ¬ pod_identity_matches set pod).
    { intros Hidentity. apply Hidentity_spec in Hidentity. done. }
    pose proof
      (stateful_pod_update_admissible_of_valid
        set pod ordinal Hpod_valid Hpod_desired_key Hpod_name_valid)
      as (Hinput_valid & Hvalid_meta_update & Hvalid_spec_update).
    pose proof Hvalid_meta_update as
      (Hinput_name & _ & Hinput_namespace & _ & Hinput_uid' & _).
    assert (Hinput_key :
        PodV.key pod = PodV.key (update_identity set pod ordinal)).
    { rewrite /PodV.key /PodV.meta_key Hinput_name Hinput_namespace.
      done. }
    assert (Hinput_uid :
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') =
        (update_identity set pod ordinal).(PodV.ObjectMeta').(
          ObjectMetaV.UID')).
    { symmetry. exact Hinput_uid'. }
    assert (Hinput_valid_create :
        PodV.valid_named_create
          (update_identity set pod ordinal).(PodV.ObjectMeta').(
            ObjectMetaV.Namespace')
          (update_identity set pod ordinal)).
    { eapply PodV.valid_named_create_of_valid; done. }
    assert (Hinput_uid_nonempty :
        (update_identity set pod ordinal).(PodV.ObjectMeta').(
          ObjectMetaV.UID') ≠ ""%go).
    { destruct Hinput_valid as (_ & _ & Hmeta & _).
      eapply valid_uid_non_empty.
      eapply ObjectMetaV.valid_uid_of_valid. exact Hmeta. }
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
    assert (returned_pod.(PodV.Spec') = pod.(PodV.Spec'))
      as Hreturned_spec.
    { unfold ObjectSpecV.updated, PodSpecV.updated in
        Hupdate_Hspec_updated.
      simpl in Hupdate_Hspec_updated.
      exact Hupdate_Hspec_updated. }
    wp_auto.
    iApply ("HΦ" $! returned_pod).
    iFrame "Hset Hpod Hupdate_Hown_meta_frag
      Hupdate_Hown_spec_frag".
    do 4 (iSplit; first (iPureIntro; assumption)).
    iRight. iFrame "%".
Qed.

End proof.
