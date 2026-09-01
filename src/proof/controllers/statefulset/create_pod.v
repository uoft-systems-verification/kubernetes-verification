From New.proof.controllers.statefulset Require Export create_pvc.
From New.proof.kubernetes_model Require Import create_named.

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

Context `{!KObjectV.ObjectInterfaceAssumptions}.

(* [createStatefulPod] first ensures one PVC for every distinct claim-template
   name, then creates the named Pod.  The intended caller owns a reservation for
   the missing Pod key, so Pod creation succeeds and the AlreadyExists branch is
   unreachable. *)
Lemma wp_createStatefulPod γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    (children : gset KKey.t) dq_set :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              ordinal ⌝ ∗
      "%Hnamespace_nonempty" ∷
        ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠
            ""%go ⌝ ∗
      "%Hnamespace_valid" ∷
        ⌜ valid_namespace
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hpod_valid_create" ∷
        ⌜ PodV.valid_create PodV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') pod ⌝ ∗
      "%Hpod_parent" ∷
        ⌜ obj_parent_ref_is (KObjectV.Pod pod)
            StatefulSetV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hpod_reserved" ∷
        own_available_reserved_frag γ 1 (desired_pod_key set ordinal) ∗
      "Hown_children" ∷
        own_children_frag γ
          (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hpvc_states" ∷
        ([∗ map] claim_template_name↦claim_template ∈
          persistent_volume_claim_templates_by_name
            (StatefulSetSpecV.volume_claim_templates_list
              set.(StatefulSetV.Spec')),
          (∃ claim,
            "%Hkey" ∷
              ⌜ PersistentVolumeClaimV.key claim =
                desired_pvc_key set claim_template_name ordinal ⌝ ∗
            "Hmeta" ∷ own_meta_frag γ
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
              claim.(PersistentVolumeClaimV.ObjectMeta') ∗
            "Hreserved" ∷ own_occupied_reserved_frag γ 1
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
          (own_available_reserved_frag γ 1
              (desired_pvc_key set claim_template_name ordinal) ∗
           ⌜ PersistentVolumeClaimV.valid_create PersistentVolumeClaimV.kind
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
                (new_persistent_volume_claim
                  set claim_template ordinal) ⌝))
  }}}
    @! statefulset.createStatefulPod #set_l #pod_l
  {{{ (pod' : PodV.t) (uid : types.UID.t), RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpvc_states" ∷
        ([∗ set] claim_template_name ∈
          list_to_set (pvc_claim_template_names set),
          ∃ claim,
            "%Hkey" ∷
              ⌜ PersistentVolumeClaimV.key claim =
                desired_pvc_key set claim_template_name ordinal ⌝ ∗
            "Hmeta" ∷ own_meta_frag γ
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
              claim.(PersistentVolumeClaimV.ObjectMeta') ∗
            "Hreserved" ∷ own_occupied_reserved_frag γ 1
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "%Hpod_valid" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hpod_meta_created" ∷
        ⌜ ObjectMetaV.created
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (pod_objectmeta_after_conversion pod.(PodV.ObjectMeta'))
            pod'.(PodV.ObjectMeta') ⌝ ∗
      "%Hpod_generation" ∷ ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.Generation') = W64 1 ⌝ ∗
      "%Hpod_spec_created" ∷
        ⌜ ObjectSpecV.created
            (ObjectSpecV.PodSpec pod.(PodV.Spec'))
            (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
      "%Hpod_status_created" ∷
        ⌜ ObjectStatusV.created
            (ObjectStatusV.PodStatus pod.(PodV.Status'))
            (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
      "%Hpod_key" ∷
        ⌜ desired_pod_key set ordinal = PodV.key pod' ⌝ ∗
      "%Hpod_key_fresh" ∷
        ⌜ desired_pod_key set ordinal ∉ children ⌝ ∗
      "%Huid" ∷
        ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hpod_meta" ∷
        own_meta_frag γ (desired_pod_key set ordinal) uid 1
          pod'.(PodV.ObjectMeta') ∗
      "Hpod_spec" ∷
        own_spec_frag γ (desired_pod_key set ordinal) uid 1
          (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      "Hpod_reserved" ∷
        own_occupied_reserved_frag γ 1 (desired_pod_key set ordinal) uid ∗
      "Hown_children" ∷
        own_children_frag γ
          (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (children ∪ {[desired_pod_key set ordinal]})
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  assert (pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go) as Hpod_name_nonempty.
  { intros Hempty.
    rewrite Hpod_name in Hempty.
    unfold desired_pod_name in Hempty.
    apply app_eq_nil in Hempty as [_ Hempty].
    discriminate Hempty. }
  pose proof (pod_name_length_le_go_int_max_of_valid_create
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
    pod Hpod_valid_create Hpod_name_nonempty) as Hpod_name_len.
  wp_apply (wp_createPersistentVolumeClaims
    γ model_l set_l pod_l set pod ordinal dq_set 1
    with "[$Hset $Hpod $Hpvc_states]").
  { iFrame "# %". }
  iIntros "H". iNamed "H".
  wp_auto.
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l &
      Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as
    (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  wp_auto.
  rewrite Hset_meta_Hdeepown_namespace.
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__PodCreate_named_available
    γ model_l
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
    (desired_pod_key set ordinal) pod_l pod
    (StatefulSetV.key set)
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
    children
    with "[$Hpod $Hpod_reserved $Hown_children]").
  { iFrame "#".
    iPureIntro.
    split_and!.
    - exact Hpod_valid_create.
    - exact Hpod_name_nonempty.
    - rewrite /StatefulSetV.key /StatefulSetV.meta_key /=.
      done.
    - rewrite /desired_pod_key Hpod_name.
      done.
    - exact Hpod_parent. }
  iIntros (pod_l' pod' uid) "Hcreate".
  iNamedPrefix "Hcreate" "Hcreate_".
  wp_auto.
  wp_apply (wp_IsAlreadyExists interface.nil with "[]").
  replace (bool_decide (already_exists_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact already_exists_error_nil).
  wp_auto.
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta_field Hset_objectmeta]" as
      "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _
    Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l
      $Hset_spec_l $Hset_status_l]") as "Hset".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold PodV.created in Hcreate_Hcreated.
  destruct Hcreate_Hcreated as
    (_ & Hpod_meta_created & Hpod_generation & Hpod_spec_created & Hpod_status_created).
  split_and!; done.
Qed.

Definition stateful_pod_create_pvc_inputs γ set ordinal : iProp Σ :=
  [∗ map] claim_template_name↦claim_template ∈
    persistent_volume_claim_templates_by_name
      (StatefulSetSpecV.volume_claim_templates_list set.(StatefulSetV.Spec')),
    (∃ claim,
      ⌜ PersistentVolumeClaimV.key claim = desired_pvc_key set claim_template_name ordinal ⌝ ∗
      own_meta_frag γ (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 claim.(PersistentVolumeClaimV.ObjectMeta') ∗
      own_occupied_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
    (own_available_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal) ∗
     ⌜ PersistentVolumeClaimV.valid_create PersistentVolumeClaimV.kind set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
        (new_persistent_volume_claim set claim_template ordinal) ⌝).

Definition stateful_pod_create_pvc_outputs γ set ordinal : iProp Σ :=
  [∗ set] claim_template_name ∈ list_to_set (pvc_claim_template_names set),
    ∃ claim,
      ⌜ PersistentVolumeClaimV.key claim = desired_pvc_key set claim_template_name ordinal ⌝ ∗
      own_meta_frag γ (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 claim.(PersistentVolumeClaimV.ObjectMeta') ∗
      own_occupied_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID').

Definition stateful_pod_created γ set pod ordinal children : iProp Σ :=
  ∃ pod' uid,
    "%Hpod_valid" ∷ ⌜ PodV.valid pod' ⌝ ∗
    "%Hpod_meta_created" ∷ ⌜ ObjectMetaV.created set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
      (pod_objectmeta_after_conversion pod.(PodV.ObjectMeta')) pod'.(PodV.ObjectMeta') ⌝ ∗
    "%Hpod_generation" ∷ ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.Generation') = W64 1 ⌝ ∗
    "%Hpod_spec_created" ∷
      ⌜ ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec')) (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
    "%Hpod_status_created" ∷ ⌜ ObjectStatusV.created (ObjectStatusV.PodStatus pod.(PodV.Status'))
      (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
    "%Hpod_key" ∷ ⌜ desired_pod_key set ordinal = PodV.key pod' ⌝ ∗
    "%Hpod_key_fresh" ∷ ⌜ desired_pod_key set ordinal ∉ children ⌝ ∗
    "%Huid" ∷ ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
    "Hpod_meta" ∷ own_meta_frag γ (desired_pod_key set ordinal) uid 1 pod'.(PodV.ObjectMeta') ∗
    "Hpod_spec" ∷ own_spec_frag γ (desired_pod_key set ordinal) uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
    "Hpod_reserved" ∷ own_occupied_reserved_frag γ 1 (desired_pod_key set ordinal) uid ∗
    "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set) set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (children ∪ {[desired_pod_key set ordinal]}).

(* A deleting reservation means that the previous Pod with this name is still
   terminating or has already disappeared.  In the former case PodCreate
   reports AlreadyExists, which createStatefulPod deliberately treats as
   success; in the latter case the ordinary creation result is returned. *)
Lemma wp_createStatefulPod_deleting γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    (children : gset KKey.t) dq_set old_uid :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hordinal_bound" ∷ ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
        desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hnamespace_nonempty" ∷ ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠ ""%go ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hpod_valid_create" ∷
        ⌜ PodV.valid_create PodV.kind set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') pod ⌝ ∗
      "%Hpod_parent" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hpod_reserved" ∷ own_deleting_reserved_frag γ 1 (desired_pod_key set ordinal) old_uid ∗
      "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hpvc_states" ∷ ([∗ map] claim_template_name↦claim_template ∈
        persistent_volume_claim_templates_by_name
          (StatefulSetSpecV.volume_claim_templates_list set.(StatefulSetV.Spec')),
        (∃ claim,
          "%Hkey" ∷ ⌜ PersistentVolumeClaimV.key claim = desired_pvc_key set claim_template_name ordinal ⌝ ∗
          "Hmeta" ∷ own_meta_frag γ (desired_pvc_key set claim_template_name ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 claim.(PersistentVolumeClaimV.ObjectMeta') ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
        (own_available_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal) ∗
         ⌜ PersistentVolumeClaimV.valid_create PersistentVolumeClaimV.kind set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (new_persistent_volume_claim set claim_template ordinal) ⌝))
  }}}
    @! statefulset.createStatefulPod #set_l #pod_l
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpvc_states" ∷ ([∗ set] claim_template_name ∈ list_to_set (pvc_claim_template_names set),
        ∃ claim,
          "%Hkey" ∷ ⌜ PersistentVolumeClaimV.key claim = desired_pvc_key set claim_template_name ordinal ⌝ ∗
          "Hmeta" ∷ own_meta_frag γ (desired_pvc_key set claim_template_name ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 claim.(PersistentVolumeClaimV.ObjectMeta') ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (desired_pvc_key set claim_template_name ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
      ((∃ pod' uid,
        "%Hpod_valid" ∷ ⌜ PodV.valid pod' ⌝ ∗
        "%Hpod_meta_created" ∷ ⌜ ObjectMetaV.created
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
          (pod_objectmeta_after_conversion pod.(PodV.ObjectMeta')) pod'.(PodV.ObjectMeta') ⌝ ∗
        "%Hpod_generation" ∷ ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.Generation') = W64 1 ⌝ ∗
        "%Hpod_spec_created" ∷ ⌜ ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec'))
          (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
        "%Hpod_status_created" ∷ ⌜ ObjectStatusV.created (ObjectStatusV.PodStatus pod.(PodV.Status'))
          (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
        "%Hpod_key" ∷ ⌜ desired_pod_key set ordinal = PodV.key pod' ⌝ ∗
        "%Hpod_key_fresh" ∷ ⌜ desired_pod_key set ordinal ∉ children ⌝ ∗
        "%Huid" ∷ ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
        "Hpod_meta" ∷ own_meta_frag γ (desired_pod_key set ordinal) uid 1 pod'.(PodV.ObjectMeta') ∗
        "Hpod_spec" ∷ own_spec_frag γ (desired_pod_key set ordinal) uid 1
          (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
        "Hpod_reserved" ∷ own_occupied_reserved_frag γ 1 (desired_pod_key set ordinal) uid ∗
        "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (children ∪ {[desired_pod_key set ordinal]})) ∨
       ("Hpod_reserved" ∷ own_deleting_reserved_frag γ 1 (desired_pod_key set ordinal) old_uid ∗
        "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  assert (pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go) as Hpod_name_nonempty.
  { intros Hempty.
    rewrite Hpod_name in Hempty.
    unfold desired_pod_name in Hempty.
    apply app_eq_nil in Hempty as [_ Hempty].
    discriminate Hempty. }
  pose proof (pod_name_length_le_go_int_max_of_valid_create
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') pod Hpod_valid_create
    Hpod_name_nonempty) as Hpod_name_len.
  wp_apply (wp_createPersistentVolumeClaims γ model_l set_l pod_l set pod ordinal dq_set 1
    with "[$Hset $Hpod $Hpvc_states]").
  { iFrame "# %". }
  iIntros "H". iNamed "H". wp_auto.
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  wp_auto. rewrite Hset_meta_Hdeepown_namespace.
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__PodCreate_named γ model_l
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') (desired_pod_key set ordinal) pod_l pod
    (StatefulSetV.key set) set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') children old_uid
    with "[$Hpod $Hpod_reserved $Hown_children]").
  { iFrame "#". iPureIntro. split_and!.
    - exact Hpod_valid_create.
    - exact Hpod_name_nonempty.
    - rewrite /StatefulSetV.key /StatefulSetV.meta_key /=. done.
    - rewrite /desired_pod_key Hpod_name. done.
    - exact Hpod_parent. }
  iIntros (created err) "[Hcreate|Hexists]".
  - iDestruct "Hcreate" as (pod_l' pod' uid)
      "(%Hcreated & %Herr & %Hpod_valid & %Hpod_created &
        %Hpod_key & %Hpod_key_fresh & %Huid & Hpod & Hpod_meta & Hpod_spec &
        Hpod_status & Hpod_reserved & Hown_children & Hown_grandchildren)".
    unfold PodV.created in Hpod_created.
    destruct Hpod_created as
      (_ & Hpod_meta_created & Hpod_generation & Hpod_spec_created & Hpod_status_created).
    subst created err. wp_auto.
    wp_apply (wp_IsAlreadyExists interface.nil with "[]").
    replace (bool_decide (already_exists_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact already_exists_error_nil).
    wp_auto.
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iApply "HΦ". iFrame. iLeft. iExists pod', uid. iFrame. done.
  - iDestruct "Hexists" as "(%Hcreated & %Halready_exists & Hpod_reserved & Hown_children)".
    subst created.
    pose proof (already_exists_error_not_nil err Halready_exists) as Herr.
    destruct err as [err_v|]; last contradiction.
    wp_auto.
    wp_apply (wp_IsAlreadyExists (interface.ok err_v) with "[]").
    replace (bool_decide (already_exists_error (interface.ok err_v))) with true by
      (symmetry; apply bool_decide_eq_true_2; exact Halready_exists).
    wp_auto.
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iApply "HΦ". iFrame "Hset Hpvc_states". iRight. iFrame.
Qed.

Lemma wp_createStatefulPod_preservation γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    (children : gset KKey.t) dq_set :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hordinal_bound" ∷ ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
        desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hnamespace_nonempty" ∷ ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠ ""%go ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hpod_valid_create" ∷
        ⌜ PodV.valid_create PodV.kind set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') pod ⌝ ∗
      "%Hpod_parent" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) StatefulSetV.kind
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hpod_reserved" ∷ (own_available_reserved_frag γ 1 (desired_pod_key set ordinal) ∨
        ∃ old_uid, own_deleting_reserved_frag γ 1 (desired_pod_key set ordinal) old_uid) ∗
      "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hpvc_states" ∷ stateful_pod_create_pvc_inputs γ set ordinal
  }}}
    @! statefulset.createStatefulPod #set_l #pod_l
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpvc_states" ∷ stateful_pod_create_pvc_outputs γ set ordinal ∗
      (stateful_pod_created γ set pod ordinal children ∨
       ∃ old_uid,
        own_deleting_reserved_frag γ 1 (desired_pod_key set ordinal) old_uid ∗
        own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  iDestruct "Hpod_reserved" as "[Havailable|Hdeleting]".
  - wp_apply (wp_createStatefulPod γ model_l set_l pod_l set pod ordinal children dq_set
      with "[$Hset $Hpod $Havailable $Hown_children $Hpvc_states]").
    { iFrame "# %". }
    iIntros (pod' uid) "H". iNamedPrefix "H" "Hcreate_".
    iApply "HΦ". iFrame "Hcreate_Hset Hcreate_Hpvc_states". iLeft.
    iExists pod', uid. iFrame. iPureIntro. split_and!; done.
  - iDestruct "Hdeleting" as (old_uid) "Hdeleting".
    wp_apply (wp_createStatefulPod_deleting γ model_l set_l pod_l set pod ordinal children dq_set old_uid
      with "[$Hset $Hpod $Hdeleting $Hown_children $Hpvc_states]").
    { iFrame "# %". }
    iIntros "(Hset & Hpvc_states & [Hcreated|Hdeleting])".
    + iApply "HΦ". iFrame "Hset Hpvc_states". iLeft. iExact "Hcreated".
    + iApply "HΦ". iFrame "Hset Hpvc_states". iRight. iExists old_uid. iExact "Hdeleting".
Qed.

End proof.
