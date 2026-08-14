From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export pvc.
From New.proof.kubernetes_model Require Export create_named_orphan get_reserved.
From New.proof.kubernetes_model Require Import get.
From New.proof.map Require Import for_range.

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

Definition claim_template_maps_related
    (R : v1.PersistentVolumeClaim.t → PersistentVolumeClaimV.t → Prop)
    (physical : gmap go_string v1.PersistentVolumeClaim.t)
    (pure : gmap go_string PersistentVolumeClaimV.t) : Prop :=
  ∀ name physical_claim_template,
    physical !! name = Some physical_claim_template →
    ∃ pure_claim_template,
      pure !! name = Some pure_claim_template ∧
      R physical_claim_template pure_claim_template.

Lemma claim_template_maps_related_insert R physical pure
    physical_claim_template pure_claim_template :
  physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
    pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') →
  R physical_claim_template pure_claim_template →
  claim_template_maps_related R physical pure →
  claim_template_maps_related R
    (claim_templates_map_insert physical physical_claim_template)
    (persistent_volume_claim_template_insert pure pure_claim_template).
Proof.
  intros Hname Hindex Hrelated name claim_template Hlookup.
  unfold claim_templates_map_insert in Hlookup.
  unfold persistent_volume_claim_template_insert.
  apply lookup_insert_Some in Hlookup as
    [[Hkey Hclaim_template]|[Hkey Hlookup]].
  - subst name claim_template.
    exists pure_claim_template.
    rewrite -Hname lookup_insert_eq.
    split; done.
  - destruct (Hrelated _ _ Hlookup) as
      (pure_claim_template' & Hpure & Hindex').
    exists pure_claim_template'.
    rewrite lookup_insert_ne.
    + intros Heq. apply Hkey. rewrite Hname. exact Heq.
    + split; done.
Qed.

Lemma Forall2_claim_template_names_with_lookup
    physical_claim_templates pure_claim_templates :
  Forall2
    (λ physical_claim_template pure_claim_template,
      physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
    physical_claim_templates pure_claim_templates →
  Forall2
    (λ physical_claim_template pure_claim_template,
      physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') ∧
      ∃ i,
        physical_claim_templates !! i = Some physical_claim_template ∧
        pure_claim_templates !! i = Some pure_claim_template)
    physical_claim_templates pure_claim_templates.
Proof.
  intros Hclaim_templates.
  induction Hclaim_templates as
      [|physical_claim_template pure_claim_template
         physical_claim_templates pure_claim_templates
         Hname Hclaim_templates IH];
    constructor; first split.
  - exact Hname.
  - exists 0%nat. done.
  - eapply Forall2_impl.
    2: exact IH.
    intros physical_claim_template' pure_claim_template'
      (Hname' & i & Hphysical & Hpure).
    split; first done. exists (S i). simpl. split; done.
Qed.

Lemma claim_template_maps_related_fold R physical_claim_templates
    pure_claim_templates physical pure :
  Forall2
    (λ physical_claim_template pure_claim_template,
      physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') ∧
      R physical_claim_template pure_claim_template)
    physical_claim_templates pure_claim_templates →
  claim_template_maps_related R physical pure →
  claim_template_maps_related R
    (fold_left claim_templates_map_insert physical_claim_templates physical)
    (fold_left persistent_volume_claim_template_insert
      pure_claim_templates pure).
Proof.
  intros Hclaim_templates.
  revert physical pure.
  induction Hclaim_templates as
      [|physical_claim_template pure_claim_template
         physical_claim_templates' pure_claim_templates'
         [Hname Hindex] Hclaim_templates IH];
    intros physical pure Hrelated; simpl; first done.
  apply IH.
  by apply claim_template_maps_related_insert.
Qed.

Lemma claim_templates_maps_related physical_claim_templates
    pure_claim_templates :
  Forall2
    (λ physical_claim_template pure_claim_template,
      physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
    physical_claim_templates pure_claim_templates →
  claim_template_maps_related
    (λ physical_claim_template pure_claim_template,
      ∃ i,
        physical_claim_templates !! i = Some physical_claim_template ∧
        pure_claim_templates !! i = Some pure_claim_template)
    (claim_templates_map_of_list physical_claim_templates)
    (persistent_volume_claim_templates_by_name pure_claim_templates).
Proof.
  intros Hclaim_templates.
  apply claim_template_maps_related_fold.
  - by apply Forall2_claim_template_names_with_lookup.
  - intros name physical_claim_template Hlookup.
    rewrite lookup_empty in Hlookup. done.
Qed.

Lemma persistent_volume_claim_template_lookup_acc
    (claim_templates_phy :
      gmap go_string v1.PersistentVolumeClaim.t)
    (claim_templates_list : list v1.PersistentVolumeClaim.t)
    (claim_templates : list PersistentVolumeClaimV.t)
    claim_template_name claim_template_phy dq :
  (∀ name,
    claim_templates_phy !! name =
      claim_templates_map_of_list claim_templates_list !! name) →
  claim_templates_phy !! claim_template_name = Some claim_template_phy →
  ([∗ list] claim_template_phy;claim_template ∈
      claim_templates_list;claim_templates,
      PersistentVolumeClaimV.deepown claim_template_phy claim_template dq) -∗
  ∃ claim_template,
    ⌜ persistent_volume_claim_templates_by_name claim_templates !!
        claim_template_name = Some claim_template ⌝ ∗
    PersistentVolumeClaimV.deepown
      claim_template_phy claim_template dq ∗
    (PersistentVolumeClaimV.deepown
        claim_template_phy claim_template dq -∗
     ([∗ list] claim_template_phy;claim_template ∈
        claim_templates_list;claim_templates,
        PersistentVolumeClaimV.deepown
          claim_template_phy claim_template dq)).
Proof.
  intros Hmap_eq Hclaim_lookup.
  iIntros "Hclaim_templates".
  iDestruct (persistent_volume_claim_deepown_list_names with
    "Hclaim_templates") as "[%Hnames Hclaim_templates]".
  assert (Forall2
      (λ physical_claim_template pure_claim_template,
        physical_claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
          pure_claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
      claim_templates_list claim_templates) as Hnames_forall2.
  { apply Forall2_fmap_1.
    rewrite -list_eq_Forall2.
    exact Hnames. }
  pose proof (claim_templates_maps_related _ _ Hnames_forall2)
    as Hmaps_related.
  rewrite Hmap_eq in Hclaim_lookup.
  destruct (Hmaps_related _ _ Hclaim_lookup) as
    (claim_template & Hclaim_template_lookup & i &
      Hclaim_phy_lookup & Hclaim_pure_lookup).
  iDestruct (big_sepL2_lookup_acc _ _ _ i _ _
    Hclaim_phy_lookup Hclaim_pure_lookup with
    "Hclaim_templates") as "[Hclaim_template Hclaim_templates]".
  iExists claim_template.
  iSplit; first done.
  iFrame.
Qed.

(* [createPersistentVolumeClaim] is an idempotent ensure operation.  If the
   claim already exists, Get succeeds and its fragments are preserved.  If its
   key is reserved, the Kubernetes model guarantees that it is absent, so the
   NotFound branch creates it and consumes the reservation. *)
Lemma wp_createPersistentVolumeClaim_without_claim_templates γ model_l
    set_l pod_l claim_template_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (claim_template : PersistentVolumeClaimV.t) (ordinal : nat)
    dq_set dq_pod dq_claim_template_ptr dq_claim_template
    set_phy claim_template_phy :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template_ptr" ∷
        claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown
        claim_template_phy claim_template dq_claim_template ∗
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
        ((∃ claim,
            "%Hkey" ∷
              ⌜ PersistentVolumeClaimV.key claim =
                new_persistent_volume_claim_key
                  set claim_template ordinal ⌝ ∗
            "Hmeta" ∷ own_meta_frag γ
              (new_persistent_volume_claim_key
                set claim_template ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
              claim.(PersistentVolumeClaimV.ObjectMeta') ∗
            "Hreserved" ∷ own_occupied_reserved_frag γ
              (new_persistent_volume_claim_key set claim_template ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
         ("Hreserved" ∷ own_available_frag γ
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
      "Hset" ∷ statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template_ptr" ∷
        claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown
        claim_template_phy claim_template dq_claim_template ∗
      "Hpvc_state" ∷
        (∃ claim,
          "%Hkey" ∷
            ⌜ PersistentVolumeClaimV.key claim =
              new_persistent_volume_claim_key
                set claim_template ordinal ⌝ ∗
          "Hmeta" ∷ own_meta_frag γ
            (new_persistent_volume_claim_key
              set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
            claim.(PersistentVolumeClaimV.ObjectMeta') ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ
            (new_persistent_volume_claim_key set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_newPersistentVolumeClaim_without_claim_templates
    set_l pod_l claim_template_l set pod claim_template ordinal
    dq_set dq_pod dq_claim_template_ptr dq_claim_template
    set_phy claim_template_phy
    with "[$Hpkg $Hset $Hpod $Hclaim_template_ptr $Hclaim_template]").
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
      with "[$Hmeta]").
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
    iFrame "Hset Hpod Hclaim_template_ptr Hclaim_template".
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
    iFrame "Hset Hpod Hclaim_template_ptr Hclaim_template".
    iExists created_claim.
    iFrame.
    iPureIntro.
    symmetry.
    exact Hkey_eq'.
Qed.

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
        ((∃ claim,
            "%Hkey" ∷
              ⌜ PersistentVolumeClaimV.key claim =
                new_persistent_volume_claim_key
                  set claim_template ordinal ⌝ ∗
            "Hmeta" ∷ own_meta_frag γ
              (new_persistent_volume_claim_key
                set claim_template ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
              claim.(PersistentVolumeClaimV.ObjectMeta') ∗
            "Hreserved" ∷ own_occupied_reserved_frag γ
              (new_persistent_volume_claim_key set claim_template ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
         ("Hreserved" ∷ own_available_frag γ
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
        (∃ claim,
          "%Hkey" ∷
            ⌜ PersistentVolumeClaimV.key claim =
              new_persistent_volume_claim_key
                set claim_template ordinal ⌝ ∗
          "Hmeta" ∷ own_meta_frag γ
            (new_persistent_volume_claim_key
              set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
            claim.(PersistentVolumeClaimV.ObjectMeta') ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ
            (new_persistent_volume_claim_key set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  iDestruct "Hset" as (set_phy) "[Hset_ptr Hset]".
  iNamed "Hset".
  iNamed "Hdeepown_spec".
  iDestruct "Hdeepown_volumeclaimtemplates" as
    (claim_templates_list) "Hdeepown_volumeclaimtemplates".
  iDestruct "Hclaim_template" as (claim_template_phy)
    "[Hclaim_template_ptr Hclaim_template]".
  iAssert (statefulset_without_claim_templates_l
      set_l set dq_set set_phy)
    with "[Hset_ptr Hdeepown_objectmeta
      Hdeepown_replicas_some Hdeepown_selector_some
      Hdeepown_template Hdeepown_status]" as "Hset".
  { rewrite /statefulset_without_claim_templates_l.
    iFrame. iFrame "%". }
  wp_apply (wp_createPersistentVolumeClaim_without_claim_templates
    γ model_l set_l pod_l claim_template_l set pod claim_template ordinal
    dq_set dq_pod dq_claim_template dq_claim_template
    set_phy claim_template_phy
    with "[$Hset $Hpod $Hclaim_template_ptr
      $Hclaim_template $Hpvc_state]").
  { iFrame "# %". }
  iIntros "H". iNamed "H".
  iAssert (PersistentVolumeClaimV.deepown_l
      claim_template_l claim_template dq_claim_template)
    with "[Hclaim_template_ptr Hclaim_template]"
    as "Hclaim_template_l".
  { iExists claim_template_phy. iFrame. }
  iNamed "Hset".
  iAssert (StatefulSetV.deepown_l set_l set dq_set)
    with "[Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hdeepown_volumeclaimtemplates
      Hdeepown_status]" as "Hset".
  { iExists set_phy.
    rewrite /StatefulSetV.deepown /StatefulSetSpecV.deepown.
    iFrame.
    iFrame "%". }
  iApply "HΦ".
  iFrame "Hset Hpod Hclaim_template_l Hpvc_state".
Qed.

(* [volumeClaimTemplatesByName] indexes templates by name before this function
   iterates over them.  The specification consequently tracks one PVC state per
   distinct template name, matching both the controller implementation and the
   top-level [desired_pvc_keys] progress invariant. *)
Lemma wp_createPersistentVolumeClaims γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    dq_set dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
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
      "%Hnamespace_nonempty" ∷
        ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠
            ""%go ⌝ ∗
      "%Hnamespace_valid" ∷
        ⌜ valid_namespace
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
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
            "Hreserved" ∷ own_occupied_reserved_frag γ
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
          (own_available_frag γ
              (desired_pvc_key set claim_template_name ordinal) ∗
           ⌜ PersistentVolumeClaimV.valid_named_create
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
                (new_persistent_volume_claim
                  set claim_template ordinal) ⌝))
  }}}
    @! statefulset.createPersistentVolumeClaims #set_l #pod_l
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
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
            "Hreserved" ∷ own_occupied_reserved_frag γ
              (desired_pvc_key set claim_template_name ordinal)
              claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_volumeClaimTemplatesByName set_l set dq_set with "Hset").
  iIntros (set_phy claim_templates_map claim_templates_list
    claim_templates_phy) "H".
  iDestruct "H" as "[Hset_ptr H]".
  iDestruct "H" as
    "(%Hdeepown_typemeta & Hdeepown_objectmeta &
      %Hdeepown_replicas_none & Hdeepown_replicas_some &
      %Hdeepown_selector_none & Hdeepown_selector_some &
      Hdeepown_template & %Hdeepown_volumeclaimtemplates_none &
      Hdeepown_volumeclaimtemplates &
      %Hclaim_templates_map_values & %Hclaim_templates_list_names &
      %Hclaim_templates_map_dom & %Hclaim_templates_map_eq &
      %Hdeepown_servicename &
      Hdeepown_status & Hclaim_templates_map)".
  iEval (rewrite /deepown_list) in "Hdeepown_volumeclaimtemplates".
  iDestruct "Hdeepown_volumeclaimtemplates" as
    "[Hclaim_templates_slice Hclaim_templates_deepown]".
  iAssert (statefulset_without_claim_templates_l
      set_l set dq_set set_phy)
    with "[Hset_ptr Hdeepown_objectmeta
      Hdeepown_replicas_some Hdeepown_selector_some
      Hdeepown_template Hdeepown_status]" as "Hset".
  { rewrite /statefulset_without_claim_templates_l.
    iFrame. iFrame "%". }

  set claim_templates :=
    StatefulSetSpecV.volume_claim_templates_list
      set.(StatefulSetV.Spec').
  set claim_templates_pure :=
    persistent_volume_claim_templates_by_name claim_templates.
  set pvc_ready := (λ claim_template_name claim_template,
    (∃ claim,
      "%Hkey" ∷
        ⌜ PersistentVolumeClaimV.key claim =
          desired_pvc_key set claim_template_name ordinal ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
        claim.(PersistentVolumeClaimV.ObjectMeta') ∗
      "Hreserved" ∷ own_occupied_reserved_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
    (own_available_frag γ
        (desired_pvc_key set claim_template_name ordinal) ∗
     ⌜ PersistentVolumeClaimV.valid_named_create
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
          (new_persistent_volume_claim
            set claim_template ordinal) ⌝))%I.
  set pvc_done := (λ claim_template_name,
    ∃ claim,
      "%Hkey" ∷
        ⌜ PersistentVolumeClaimV.key claim =
          desired_pvc_key set claim_template_name ordinal ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
        claim.(PersistentVolumeClaimV.ObjectMeta') ∗
      "Hreserved" ∷ own_occupied_reserved_frag γ
        (desired_pvc_key set claim_template_name ordinal)
        claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID'))%I.
  assert (Hclaim_templates_pure_dom :
      dom claim_templates_pure = dom claim_templates_phy).
  { unfold_leibniz.
    apply set_equiv. intros claim_template_name.
    rewrite Hclaim_templates_map_dom /claim_templates_pure
      persistent_volume_claim_templates_by_name_dom.
    done. }
  assert (Hclaim_templates_pure_size :
      size claim_templates_pure = size claim_templates_phy).
  { pose proof (f_equal size Hclaim_templates_pure_dom) as Hsize.
    rewrite !size_dom in Hsize.
    exact Hsize. }
  iAssert (([∗ map] name↦claim_template ∈ claim_templates_pure,
      pvc_ready name claim_template))%I
    with "[Hpvc_states]" as "Hpvc_todo".
  { rewrite /claim_templates_pure.
    iExact "Hpvc_states". }
  wp_auto.
  set P := (λ (keys : list go_string) (z : Z),
    ∃ (last_claim_template : v1.PersistentVolumeClaim.t),
      "set" ∷ set_ptr ↦ set_l ∗
      "pod" ∷ pod_ptr ↦ pod_l ∗
      "claimTemplate" ∷ claimTemplate_ptr ↦ last_claim_template ∗
      "Hset" ∷ statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_templates_slice" ∷
        set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates')
          ↦* claim_templates_list ∗
      "Hclaim_templates_deepown" ∷
        ([∗ list] claim_template_phy;claim_template ∈
          claim_templates_list;claim_templates,
          PersistentVolumeClaimV.deepown
            claim_template_phy claim_template dq_set) ∗
      "Hpvc_done" ∷
        ([∗ map] name↦claim_template ∈
          map_prefix keys z claim_templates_pure,
          pvc_done name) ∗
      "Hpvc_todo" ∷
        ([∗ map] name↦claim_template ∈
          claim_templates_pure ∖
            map_prefix keys z claim_templates_pure,
          pvc_ready name claim_template))%I.
  wp_apply (wp_map_for_range_return (key_type:=go.string) P
    with "Hclaim_templates_map").
  iIntros (keys) "%Hkeys".
  destruct Hkeys as (Hkeys_dom & Hkeys_len & Hkeys_nodup).
  iSplitL "set pod claimTemplate Hset Hpod
      Hclaim_templates_slice Hclaim_templates_deepown Hpvc_todo".
  { iExists (zero_val v1.PersistentVolumeClaim.t).
    rewrite map_prefix_empty map_difference_empty big_sepM_empty.
    iFrame. }
  iSplitL "".
  { iModIntro.
    iIntros (z claim_template_name claim_template_phy)
      "%Hiter HP".
    destruct Hiter as (Hz_bounds & Hkey_lookup & Hclaim_lookup).
    destruct Hz_bounds as (Hz_nonneg & Hz_upper).
    iDestruct "HP" as (last_claim_template) "HP".
    iNamed "HP".
    assert (Hclaim_template_name_not_processed :
        claim_template_name ∉ take (Z.to_nat z) keys).
    { intros Hin.
      rewrite elem_of_take in Hin.
      destruct Hin as (i & Hi_lookup & Hi_lt).
      pose proof (NoDup_lookup keys i (Z.to_nat z)
        claim_template_name Hkeys_nodup Hi_lookup Hkey_lookup).
      lia. }
    assert (Hprefix_lookup :
        map_prefix keys z claim_templates_pure !!
          claim_template_name = None).
    { rewrite /map_prefix map_lookup_filter_None.
      right.
      intros claim_template Hlookup Hin.
      apply Hclaim_template_name_not_processed.
      rewrite elem_of_list_to_set in Hin.
      exact Hin. }
    iDestruct
      (persistent_volume_claim_template_lookup_acc
        claim_templates_phy claim_templates_list claim_templates
        claim_template_name claim_template_phy dq_set
        Hclaim_templates_map_eq Hclaim_lookup
        with "Hclaim_templates_deepown")
      as (claim_template)
        "(%Hclaim_template_lookup & Hclaim_template &
          Hclaim_templates_restore)".
    pose proof (Hclaim_templates_map_values _ _ Hclaim_lookup) as
      [_ Hclaim_template_phy_name].
    iDestruct (persistent_volume_claim_deepown_name with
      "Hclaim_template") as
      "[%Hclaim_template_deepown_name Hclaim_template]".
    assert (Hclaim_template_name :
        claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') =
          claim_template_name) by congruence.
    assert (Htodo_lookup :
        (claim_templates_pure ∖
          map_prefix keys z claim_templates_pure) !!
          claim_template_name = Some claim_template).
    { rewrite lookup_difference_Some.
      split; done. }
    iDestruct (big_sepM_delete _ _ _ _ Htodo_lookup with
      "Hpvc_todo") as "[Hpvc_state Hpvc_todo]".
    wp_auto.
    iAssert
      ((∃ claim,
          "%Hkey" ∷
            ⌜ PersistentVolumeClaimV.key claim =
              new_persistent_volume_claim_key
                set claim_template ordinal ⌝ ∗
          "Hmeta" ∷ own_meta_frag γ
            (new_persistent_volume_claim_key
              set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
            claim.(PersistentVolumeClaimV.ObjectMeta') ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ
            (new_persistent_volume_claim_key set claim_template ordinal)
            claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∨
       (own_available_frag γ
          (new_persistent_volume_claim_key
            set claim_template ordinal) ∗
        ⌜ PersistentVolumeClaimV.valid_named_create
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')
            (new_persistent_volume_claim
              set claim_template ordinal) ⌝ ∗
        ⌜ set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ≠
            ""%go ⌝ ∗
        ⌜ valid_namespace
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝))%I
      with "[Hpvc_state]" as "Hpvc_state".
    { rewrite new_persistent_volume_claim_key_eq
        Hclaim_template_name /pvc_ready.
      iDestruct "Hpvc_state" as "[Hpvc_state | Hpvc_state]".
      - iLeft. iExact "Hpvc_state".
      - iDestruct "Hpvc_state" as "[Hreserved %Hvalid_create]".
        iRight.
        iFrame "Hreserved".
        iFrame "%". }
    wp_apply
      (wp_createPersistentVolumeClaim_without_claim_templates
        γ model_l set_l pod_l claimTemplate_ptr set pod
        claim_template ordinal dq_set dq_pod 1 dq_set set_phy
        claim_template_phy
        with "[$Hset $Hpod $claimTemplate
          $Hclaim_template $Hpvc_state]").
    { iFrame "# %". }
    iIntros "H". iNamed "H".
    iEval (rewrite new_persistent_volume_claim_key_eq
      Hclaim_template_name) in "Hpvc_state".
    iSpecialize ("Hclaim_templates_restore" with "Hclaim_template").
    iRename "Hclaim_templates_restore" into
      "Hclaim_templates_deepown".
    wp_auto.
    assert (Hprefix_next :
        map_prefix keys (z + 1) claim_templates_pure =
          <[claim_template_name:=claim_template]>
            (map_prefix keys z claim_templates_pure)).
    { apply map_prefix_insert; done. }
    iRight. iSplit; first done.
    iExists claim_template_phy.
    iFrame "set pod Hset Hpod Hclaim_template_ptr
      Hclaim_templates_slice Hclaim_templates_deepown".
    rewrite Hprefix_next.
    iSplitL "Hpvc_done Hpvc_state".
    - rewrite (big_sepM_insert
        (λ name _, pvc_done name)%I
        (map_prefix keys z claim_templates_pure)
        claim_template_name claim_template Hprefix_lookup).
      iFrame.
    - rewrite <-(delete_difference claim_templates_pure
        (map_prefix keys z claim_templates_pure)
        claim_template_name claim_template).
      iExact "Hpvc_todo".
  }
  iIntros "Hclaim_templates_map HP".
  iDestruct "HP" as (last_claim_template) "HP".
  iNamed "HP".
  assert (Hprefix_all :
      map_prefix keys (Z.of_nat (size claim_templates_pure))
        claim_templates_pure = claim_templates_pure).
  { apply map_prefix_all.
    - rewrite Hclaim_templates_pure_dom. exact Hkeys_dom.
    - rewrite Hclaim_templates_pure_size. exact Hkeys_len. }
  rewrite Hclaim_templates_pure_size in Hprefix_all.
  iEval (rewrite Hprefix_all) in "Hpvc_done".
  iEval (rewrite Hprefix_all map_difference_diag big_sepM_empty)
    in "Hpvc_todo".
  iClear "Hpvc_todo".
  iAssert (([∗ set] claim_template_name ∈ dom claim_templates_pure,
      pvc_done claim_template_name))%I
    with "[Hpvc_done]" as "Hpvc_states".
  { rewrite -big_sepM_dom.
    iExact "Hpvc_done". }
  iNamed "Hset".
  iAssert (StatefulSetV.deepown_l set_l set dq_set)
    with "[Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hclaim_templates_slice
      Hclaim_templates_deepown Hdeepown_status]" as "Hset".
  { iExists set_phy.
    rewrite /StatefulSetV.deepown /StatefulSetSpecV.deepown.
    iFrame "Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hdeepown_status".
    iFrame "%".
    iExists claim_templates_list.
    rewrite /deepown_list.
    iFrame. }
  wp_auto.
  iApply "HΦ".
  rewrite /pvc_done /claim_templates_pure
    persistent_volume_claim_templates_by_name_dom
    /claim_templates /pvc_claim_template_names.
  iFrame.
Qed.

End proof.
