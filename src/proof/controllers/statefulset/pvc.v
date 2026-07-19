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

Definition claim_templates_map_insert m claim_template : gmap go_string v1.PersistentVolumeClaim.t :=
  <[claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') := claim_template]> m.

Definition claim_templates_map_of_list claim_templates : gmap go_string v1.PersistentVolumeClaim.t :=
  fold_left claim_templates_map_insert claim_templates ∅.

Lemma claim_templates_map_of_list_snoc claim_templates claim_template :
  claim_templates_map_of_list (claim_templates ++ [claim_template]) =
  claim_templates_map_insert (claim_templates_map_of_list claim_templates) claim_template.
Proof.
  unfold claim_templates_map_of_list.
  by rewrite fold_left_app.
Qed.

Lemma claim_templates_map_of_list_values claim_templates :
  map_Forall (λ name claim_template,
    claim_template ∈ claim_templates ∧
    claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') = name)
    (claim_templates_map_of_list claim_templates).
Proof.
  induction claim_templates using rev_ind.
  - rewrite /claim_templates_map_of_list /=.
    apply map_Forall_empty.
  - rewrite claim_templates_map_of_list_snoc.
    rewrite map_Forall_lookup.
    intros name claim_template Hlookup.
    unfold claim_templates_map_insert in Hlookup.
    apply lookup_insert_Some in Hlookup as [[<- <-]|[Hname_ne Hlookup]].
    + split; [apply elem_of_app; right; by left|done].
    + rewrite map_Forall_lookup in IHclaim_templates.
      specialize (IHclaim_templates _ _ Hlookup) as [Hin Hname].
      split; [apply elem_of_app; by left|done].
Qed.

Lemma claim_templates_map_of_list_names claim_templates :
  Forall (λ claim_template,
    is_Some (claim_templates_map_of_list claim_templates !!
      claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name')))
    claim_templates.
Proof.
  induction claim_templates using rev_ind.
  - done.
  - apply Forall_forall. intros claim_template Hin.
    rewrite claim_templates_map_of_list_snoc /claim_templates_map_insert.
    apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    + rewrite Forall_forall in IHclaim_templates.
      destruct (IHclaim_templates claim_template Hin) as [mapped Hlookup].
      destruct (decide (
        x.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name'))) as
        [Heq|Hne].
      * exists x. by rewrite Heq lookup_insert_eq.
      * exists mapped. by rewrite lookup_insert_ne.
    + destruct Hin as [<-|[]].
      exists x. by rewrite lookup_insert_eq.
Qed.

(* The returned map contains physical PVC template values copied from the
   StatefulSet's physical VolumeClaimTemplates slice.  Keeping the StatefulSet
   deep ownership split in the postcondition exposes that physical slice and
   lets callers relate map entries back to the concrete templates without
   immediately hiding the fields behind StatefulSetV.deepown_l again. *)
Lemma wp_volumeClaimTemplatesByName set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq }}}
    @! statefulset.volumeClaimTemplatesByName #set_l
  {{{ (set_phy : v1.StatefulSet.t) claim_templates_map claim_templates_list
      (claim_templates_phy : gmap go_string v1.PersistentVolumeClaim.t),
      RET #claim_templates_map;
      set_l ↦{dq} set_phy ∗
      "%Hdeepown_typemeta" ∷ ⌜ set_phy.(v1.StatefulSet.TypeMeta') = set.(StatefulSetV.TypeMeta') ⌝ ∗
      "Hdeepown_objectmeta" ∷
        ObjectMetaV.deepown set_phy.(v1.StatefulSet.ObjectMeta') set.(StatefulSetV.ObjectMeta') dq ∗
      "%Hdeepown_replicas_none" ∷
        ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') = null ↔
          set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') = None ⌝ ∗
      "Hdeepown_replicas_some" ∷
        (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
        | Some i =>
            ∃ replicas,
              set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') ↦{dq} replicas ∗
              ⌜ replicas = i ⌝
        | None => True%I
        end) ∗
      "Hdeepown_template" ∷ PodTemplateSpecV.deepown set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Template')
          set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') dq ∗
      "Hdeepown_volumeclaimtemplates" ∷ deepown_list
        set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates') claim_templates_list
          set.(StatefulSetV.Spec').(StatefulSetSpecV.VolumeClaimTemplates')
          (λ claim_template_phy pure_claim_template,
            PersistentVolumeClaimV.deepown claim_template_phy pure_claim_template dq) ∗
      "%Hclaim_templates_map_values" ∷
        ⌜ map_Forall (λ name claim_template_phy,
            claim_template_phy ∈ claim_templates_list ∧
            claim_template_phy.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') = name
          ) claim_templates_phy ⌝ ∗
      "%Hclaim_templates_list_names" ∷
        ⌜ Forall (λ claim_template_phy,
            is_Some (claim_templates_phy !!
              claim_template_phy.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name'))
          ) claim_templates_list ⌝ ∗
      "%Hdeepown_servicename" ∷
        ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.ServiceName') =
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ⌝ ∗
      "Hdeepown_status" ∷ StatefulSetStatusV.deepown set_phy.(v1.StatefulSet.Status') set.(StatefulSetV.Status') dq ∗
      "Hclaim_templates_map" ∷ claim_templates_map ↦$ claim_templates_phy
  }}}.
Proof.
  wp_start as "Hset".
  iDestruct "Hset" as (set_phy) "[Hset_ptr Hset_deepown]".
  iNamed "Hset_deepown".
  iNamed "Hdeepown_spec".
  iDestruct "Hdeepown_volumeclaimtemplates" as (claim_templates_list)
    "Hdeepown_volumeclaimtemplates".
  rewrite /deepown_list.
  iDestruct "Hdeepown_volumeclaimtemplates" as
    "[Hclaim_templates_slice Hclaim_templates_deepown]".
  wp_auto.
  wp_apply wp_map_make2 as "%claim_templates_map Hclaim_templates_map".
  iDestruct (own_slice_len with "Hclaim_templates_slice") as
    %(Hclaim_templates_len1 & Hclaim_templates_len2).
  iDestruct (own_slice_wf with "Hclaim_templates_slice") as
    %Hclaim_templates_cap.
  iDestruct (big_sepL2_length with "Hclaim_templates_deepown") as
    %Hclaim_templates_deepown_len.
  set I := (∃ (i : w64) (claim_template_value : v1.PersistentVolumeClaim.t)
      (claim_templates_map_l : map.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hclaim_templates_slice" ∷
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates') ↦*
        claim_templates_list ∗
    "HclaimTemplate_ptr" ∷ claimTemplate_ptr ↦ claim_template_value ∗
    "HclaimTemplates_ptr" ∷ claimTemplates_ptr ↦ claim_templates_map_l ∗
    "Hclaim_templates_map" ∷ claim_templates_map_l ↦$
      claim_templates_map_of_list (take (sint.nat i) claim_templates_list) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z
      (slice.len set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates')) ⌝
  )%I.
  iAssert I with "[i Hclaim_templates_slice claimTemplate claimTemplates
      Hclaim_templates_map]" as
    "Hloop_inv".
  { iExists (W64 0), (zero_val v1.PersistentVolumeClaim.t), claim_templates_map.
    rewrite take_0 /claim_templates_map_of_list /=.
    iFrame.
    iPureIntro. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  - destruct (decide (0 ≤ sint.Z i <
      sint.Z (slice.len set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates'))))
      as [_|Hbounds]; last word.
    assert (∃ this_claim_template,
      claim_templates_list !! sint.nat i = Some this_claim_template) as
      [this_claim_template Hthis_claim_template_lookup].
    { apply lookup_lt_is_Some_2. rewrite Hclaim_templates_len1. word. }
    wp_apply (wp_load_slice_index with "[$Hclaim_templates_slice]"); [word| |].
    { iPureIntro. exact Hthis_claim_template_lookup. }
    iIntros "Hclaim_templates_slice".
    wp_auto.
    wp_apply (wp_map_insert go.string with "[$Hclaim_templates_map]").
    iIntros "Hclaim_templates_map".
    wp_auto.
    iApply wp_for_post_do.
    wp_auto.
    iFrame "HΦ".
    iFrame "Hset_ptr Hdeepown_objectmeta Hdeepown_replicas_some
      Hdeepown_template Hclaim_templates_deepown Hdeepown_status".
    iExists (word.add i (W64 1)), this_claim_template, claim_templates_map_l.
    assert (claim_templates_map_of_list
      (take (sint.nat (word.add i (W64 1))) claim_templates_list) =
      claim_templates_map_insert
        (claim_templates_map_of_list (take (sint.nat i) claim_templates_list))
        this_claim_template) as Hmap_next.
    { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ _ Hthis_claim_template_lookup).
      apply claim_templates_map_of_list_snoc. }
    rewrite Hmap_next.
    iFrame.
    iFrame "%".
    iPureIntro. word.
  - assert (take (sint.nat i) claim_templates_list = claim_templates_list) as Htake_all.
    { assert (sint.nat i = length claim_templates_list) as Hi_len.
      { rewrite Hclaim_templates_len1. word. }
      rewrite Hi_len.
      apply take_ge. lia. }
    rewrite Htake_all.
    iApply ("HΦ" $! set_phy claim_templates_map_l claim_templates_list
      (claim_templates_map_of_list claim_templates_list)).
    iFrame.
    rewrite /deepown_list.
    iFrame.
    iFrame "%".
    iSplit.
    + iPureIntro. apply claim_templates_map_of_list_values.
    + iPureIntro. apply claim_templates_map_of_list_names.
Unshelve.
  all: apply _.
Qed.

End proof.
