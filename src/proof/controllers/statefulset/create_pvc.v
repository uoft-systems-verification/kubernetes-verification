From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.statefulset Require Export pvc.
From New.proof.kubernetes_model Require Export create_named_orphan.

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

Definition new_persistent_volume_claim_key
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t)
    (ordinal : nat) : KKey.t :=
  PersistentVolumeClaimV.key
    (new_persistent_volume_claim set claim_template ordinal).

(* The controller only needs metadata and spec fragments to remember that the
   PVC exists.  The model's metadata-fragment validity ties the UID used by
   both fragments to the PVC metadata. *)
Definition persistent_volume_claim_exists γ key : iProp Σ :=
  ∃ claim,
    "%Hkey" ∷ ⌜ PersistentVolumeClaimV.key claim = key ⌝ ∗
    "Hmeta" ∷ own_meta_frag γ key
      claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      claim.(PersistentVolumeClaimV.ObjectMeta') ∗
    "Hspec" ∷ own_spec_frag γ key
      claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
      (ObjectSpecV.PersistentVolumeClaimSpec
        claim.(PersistentVolumeClaimV.Spec')).

(* [createPersistentVolumeClaim] is an idempotent ensure operation.  If the
   claim already exists, Get succeeds and its fragments are preserved.  If its
   key is reserved, the Kubernetes model guarantees that it is absent, so the
   NotFound branch creates it and consumes the reservation. *)
Lemma wp_createPersistentVolumeClaim γ model_l
    set_l pod_l claim_template_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (claim_template : PersistentVolumeClaimV.t) (ordinal : nat)
    dq_set dq_pod dq_claim_template :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template" ∷
        PersistentVolumeClaimV.deepown_l
          claim_template_l claim_template dq_claim_template ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              ordinal ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max ⌝ ∗
      "Hpvc_state" ∷
        (persistent_volume_claim_exists γ
            (new_persistent_volume_claim_key
              set claim_template ordinal) ∨
         ("Hreserved" ∷ own_reserved_frag γ
            (new_persistent_volume_claim_key
              set claim_template ordinal) ∗
          "%Hvalid_create" ∷
            ⌜ PersistentVolumeClaimV.valid_named_create
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
                (new_persistent_volume_claim
                  set claim_template ordinal) ⌝ ∗
          "%Hnamespace_nonempty" ∷
            ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠
                ""%go ⌝ ∗
          "%Hnamespace_valid" ∷
            ⌜ valid_namespace
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝))
  }}}
    @! statefulset.createPersistentVolumeClaim
      #set_l #pod_l #claim_template_l
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template" ∷
        PersistentVolumeClaimV.deepown_l
          claim_template_l claim_template dq_claim_template ∗
      "Hpvc_state" ∷
        persistent_volume_claim_exists γ
          (new_persistent_volume_claim_key
            set claim_template ordinal)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_newPersistentVolumeClaim
    set_l pod_l claim_template_l set pod claim_template ordinal
    dq_set dq_pod dq_claim_template
    with "[$Hset $Hpod $Hclaim_template]").
  { iFrame "%". }
  iIntros (claim_l) "H". iNamed "H".
  iPoseProof (PersistentVolumeClaimV.deepown_l_split with "Hclaim") as
    "(%Hclaim_l_not_null & Hclaim_typemeta & Hclaim_objectmeta_l &
      Hclaim_spec_l & Hclaim_status_l)".
  iDestruct "Hclaim_objectmeta_l" as (claim_meta_c)
    "[Hclaim_objectmeta_field Hclaim_objectmeta]".
  iNamedPrefix "Hclaim_objectmeta" "Hclaim_meta_".
  wp_auto.
  rewrite Hclaim_meta_Hdeepown_namespace Hclaim_meta_Hdeepown_name.
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  iDestruct "Hpvc_state" as "[Hpvc_exists | Hcreate]".
  - iDestruct "Hpvc_exists" as (existing_claim) "H".
    iNamed "H".
    wp_apply (wp_State__PersistentVolumeClaimGet
      γ model_l
      (new_persistent_volume_claim_key set claim_template ordinal)
      (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Namespace')
      (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
      existing_claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
      1
      existing_claim.(PersistentVolumeClaimV.ObjectMeta')
      existing_claim.(PersistentVolumeClaimV.Spec')
      with "[$Hmeta $Hspec]").
    { iFrame "#".
      iPureIntro.
      unfold new_persistent_volume_claim_key,
        PersistentVolumeClaimV.key, PersistentVolumeClaimV.meta_key,
        new_persistent_volume_claim.
      done. }
    iIntros (existing_claim_l existing_claim') "Hget".
    iNamedPrefix "Hget" "Hget_".
    wp_auto.
    wp_apply (wp_IsNotFound interface.nil with "[]").
    replace (bool_decide (not_found_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact not_found_error_nil).
    wp_auto.
    iApply "HΦ".
    iFrame "Hset Hpod Hclaim_template".
    iExists existing_claim.
    iFrame.
    iPureIntro.
    exact Hkey.
  - iNamed "Hcreate".
    wp_apply (wp_State__PersistentVolumeClaimGet_reserved
      γ model_l
      (new_persistent_volume_claim_key set claim_template ordinal)
      (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Namespace')
      (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
      with "[$Hreserved]").
    { iFrame "#".
      iPureIntro.
      unfold new_persistent_volume_claim_key,
        PersistentVolumeClaimV.key, PersistentVolumeClaimV.meta_key,
        new_persistent_volume_claim.
      done. }
    iIntros (err) "Hget". iNamed "Hget".
    wp_auto.
    wp_apply (wp_IsNotFound err with "[]").
    replace (bool_decide (not_found_error err)) with true by
      (symmetry; apply bool_decide_true; exact Hnot_found).
    wp_auto.
    rewrite Hclaim_meta_Hdeepown_namespace.
    iCombineNamed "Hclaim_meta_*" as "Hclaim_objectmeta".
    iAssert (ObjectMetaV.deepown claim_meta_c
        (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta') 1)
      with "[Hclaim_objectmeta]" as "Hclaim_objectmeta".
    { iNamed "Hclaim_objectmeta".
      rewrite /ObjectMetaV.deepown.
      iFrame.
      done. }
    iAssert (ObjectMetaV.deepown_l
        (PersistentVolumeClaimV.objectmeta_ptr claim_l)
        (new_persistent_volume_claim set claim_template ordinal).(PersistentVolumeClaimV.ObjectMeta') 1)
      with "[Hclaim_objectmeta_field Hclaim_objectmeta]"
      as "Hclaim_objectmeta_l".
    { iExists claim_meta_c.
      iFrame "Hclaim_objectmeta_field".
      iExact "Hclaim_objectmeta". }
    iAssert (PersistentVolumeClaimV.deepown_l claim_l
        (new_persistent_volume_claim set claim_template ordinal) 1)
      with "[Hclaim_typemeta Hclaim_objectmeta_l
        Hclaim_spec_l Hclaim_status_l]" as "Hclaim".
    { iApply PersistentVolumeClaimV.deepown_l_restore;
        [exact Hclaim_l_not_null | iFrame]. }
    wp_apply (wp_State__PersistentVolumeClaimCreate_named_orphan
      with "[$Hclaim $Hown_reserved_frag]").
    { iFrame "# %".
      iPureIntro.
      split.
      - unfold new_persistent_volume_claim_key,
          PersistentVolumeClaimV.key, PersistentVolumeClaimV.meta_key.
        done.
      - unfold obj_parent_ref, meta_parent_ref,
          new_persistent_volume_claim.
        done. }
    iIntros (created_claim_l created_claim uid) "Hcreated".
    iNamed "Hcreated".
    subst uid.
    wp_auto.
    iApply "HΦ".
    iFrame "Hset Hpod Hclaim_template".
    iExists created_claim.
    iFrame.
    iPureIntro.
    symmetry.
    exact Hkey_eq'.
Qed.

End proof.
