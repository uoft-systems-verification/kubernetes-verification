(* Discarding fractions of deep ownership.

   The concurrent pod-creating goroutines of the ReplicaSet controller read the
   ReplicaSet's ObjectMeta and pod template simultaneously. Sharing those reads
   across goroutines requires the corresponding deep-ownership predicates to be
   persistent, which we obtain by discarding the fraction ([DfracDiscarded]).
   This file proves the discard lemmas and persistence instances for the
   predicates involved. *)
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export pod replicaset.
From New.proof Require Import proof_prelude.

Section persist.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

(* [TimeV.deepown] and [ManagedFieldsEntryV.deepown] are opaque in the pure
   model (see kubernetes_types/common.v and objectmeta.v). We assume they are
   ownership predicates in the usual sense: any fraction can be discarded to
   obtain persistent, read-only knowledge. Every points-to based instantiation
   of these predicates satisfies both assumptions. *)
Axiom time_deepown_persist : ∀ c v dq,
  (TimeV.deepown c v dq : iProp Σ) ⊢ |==> TimeV.deepown c v DfracDiscarded.
Axiom time_deepown_persistent : ∀ c v,
  Persistent (TimeV.deepown c v DfracDiscarded : iProp Σ).
#[global] Existing Instance time_deepown_persistent.
Axiom managed_fields_entry_deepown_persist : ∀ c v dq,
  (ManagedFieldsEntryV.deepown c v dq : iProp Σ) ⊢ |==> ManagedFieldsEntryV.deepown c v DfracDiscarded.
Axiom managed_fields_entry_deepown_persistent : ∀ c v,
  Persistent (ManagedFieldsEntryV.deepown c v DfracDiscarded : iProp Σ).
#[global] Existing Instance managed_fields_entry_deepown_persistent.

Lemma big_sepL2_persist {A B} (P : A → B → dfrac → iProp Σ) dq (cs : list A) (vs : list B) :
  (∀ c v, P c v dq ⊢ |==> P c v DfracDiscarded) →
  ([∗ list] c;v ∈ cs;vs, P c v dq) ⊢ |==> [∗ list] c;v ∈ cs;vs, P c v DfracDiscarded.
Proof.
  intros HP.
  iInduction cs as [|c cs] "IH" forall (vs); destruct vs as [|v vs].
  - rewrite !big_sepL2_nil. iIntros "_". iModIntro. done.
  - iIntros "H". iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil. discriminate Hnil.
  - iIntros "H". iDestruct (big_sepL2_nil_inv_r with "H") as %Hnil. discriminate Hnil.
  - rewrite !big_sepL2_cons. iIntros "[Hc Hcs]".
    iMod (HP with "Hc") as "Hc". iMod ("IH" with "Hcs") as "Hcs".
    iModIntro. by iFrame.
Qed.

Lemma owner_reference_deepown_persist c v dq :
  OwnerReferenceV.deepown c v dq ⊢ |==> OwnerReferenceV.deepown c v DfracDiscarded.
Proof.
  rewrite /OwnerReferenceV.deepown. iNamed 1.
  iAssert (|==> match v.(OwnerReferenceV.Controller') with
    | Some vc => ∃ cc, c.(v1.OwnerReference.Controller') ↦□ cc ∗ ⌜ cc = vc ⌝
    | None => True%I
    end)%I with "[Hdeepown_controller_some]" as ">Hcontroller".
  { destruct (v.(OwnerReferenceV.Controller')) as [vc|]; last done.
    iDestruct "Hdeepown_controller_some" as (cc) "[Hcc %Hcc]".
    iPersist "Hcc". iModIntro. iExists cc. by iFrame "# %". }
  iAssert (|==> match v.(OwnerReferenceV.BlockOwnerDeletion') with
    | Some vb => ∃ cb, c.(v1.OwnerReference.BlockOwnerDeletion') ↦□ cb ∗ ⌜ cb = vb ⌝
    | None => True%I
    end)%I with "[Hdeepown_blockownerdeleton_some]" as ">Hblock".
  { destruct (v.(OwnerReferenceV.BlockOwnerDeletion')) as [vb|]; last done.
    iDestruct "Hdeepown_blockownerdeleton_some" as (cb) "[Hcb %Hcb]".
    iPersist "Hcb". iModIntro. iExists cb. by iFrame "# %". }
  iModIntro. by iFrame "∗ # %".
Qed.

#[global] Instance owner_reference_deepown_persistent c v :
  Persistent (OwnerReferenceV.deepown c v DfracDiscarded).
Proof.
  rewrite /OwnerReferenceV.deepown.
  destruct (v.(OwnerReferenceV.Controller')), (v.(OwnerReferenceV.BlockOwnerDeletion'));
    apply _.
Qed.

Lemma objectmeta_deepown_persist c v dq :
  ObjectMetaV.deepown c v dq ⊢ |==> ObjectMetaV.deepown c v DfracDiscarded.
Proof.
  rewrite /ObjectMetaV.deepown. iNamed 1.
  iMod (time_deepown_persist with "Hdeepown_creationtimestamp") as "Hdeepown_creationtimestamp".
  iAssert (|==> match v.(ObjectMetaV.DeletionTimestamp') with
    | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionTimestamp') ↦□ cd ∗ TimeV.deepown cd vd DfracDiscarded
    | None => True%I
    end)%I with "[Hdeepown_deletiontimestamp_some]" as ">Hdeletiontimestamp".
  { destruct (v.(ObjectMetaV.DeletionTimestamp')) as [vd|]; last done.
    iDestruct "Hdeepown_deletiontimestamp_some" as (cd) "[Hcd Ht]".
    iPersist "Hcd". iMod (time_deepown_persist with "Ht") as "Ht".
    iModIntro. iExists cd. by iFrame "∗ #". }
  iAssert (|==> match v.(ObjectMetaV.DeletionGracePeriodSeconds') with
    | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionGracePeriodSeconds') ↦□ cd ∗ ⌜ cd = vd ⌝
    | None => True%I
    end)%I with "[Hdeepown_deletiongraceperiodseconds_some]" as ">Hgrace".
  { destruct (v.(ObjectMetaV.DeletionGracePeriodSeconds')) as [vd|]; last done.
    iDestruct "Hdeepown_deletiongraceperiodseconds_some" as (cd) "[Hcd %Hcd]".
    iPersist "Hcd". iModIntro. iExists cd. by iFrame "# %". }
  iAssert (|==> match v.(ObjectMetaV.Labels') with
    | Some vl => ∃ cl, c.(v1.ObjectMeta.Labels') ↦${DfracDiscarded} cl ∗ ⌜ cl = vl ⌝
    | None => True%I
    end)%I with "[Hdeepown_labels_some]" as ">Hlabels".
  { destruct (v.(ObjectMetaV.Labels')) as [vl|]; last done.
    iDestruct "Hdeepown_labels_some" as (cl) "[Hcl %Hcl]".
    iMod (own_map_persist with "Hcl") as "Hcl". iModIntro. iExists cl. by iFrame "∗ %". }
  iAssert (|==> match v.(ObjectMetaV.Annotations') with
    | Some va => ∃ ca, c.(v1.ObjectMeta.Annotations') ↦${DfracDiscarded} ca ∗ ⌜ ca = va ⌝
    | None => True%I
    end)%I with "[Hdeepown_annotations_some]" as ">Hannotations".
  { destruct (v.(ObjectMetaV.Annotations')) as [va|]; last done.
    iDestruct "Hdeepown_annotations_some" as (ca) "[Hca %Hca]".
    iMod (own_map_persist with "Hca") as "Hca". iModIntro. iExists ca. by iFrame "∗ %". }
  iAssert (|==> match v.(ObjectMetaV.OwnerReferences') with
    | Some vos => ∃ cos, c.(v1.ObjectMeta.OwnerReferences') ↦*{DfracDiscarded} cos ∗
        [∗ list] co;vo ∈ cos;vos, OwnerReferenceV.deepown co vo DfracDiscarded
    | None => True%I
    end)%I with "[Hdeepown_ownerreferences_some]" as ">Howners".
  { destruct (v.(ObjectMetaV.OwnerReferences')) as [vos|]; last done.
    iDestruct "Hdeepown_ownerreferences_some" as (cos) "[Hcos Hlist]".
    iMod (own_slice_persist with "Hcos") as "Hcos".
    iMod (big_sepL2_persist OwnerReferenceV.deepown with "Hlist") as "Hlist".
    { intros. apply owner_reference_deepown_persist. }
    iModIntro. iExists cos. by iFrame. }
  iAssert (|==> match v.(ObjectMetaV.Finalizers') with
    | Some vfs => ∃ cfs, c.(v1.ObjectMeta.Finalizers') ↦*{DfracDiscarded} cfs ∗ ⌜ cfs = vfs ⌝
    | None => True%I
    end)%I with "[Hdeepown_finalizers_some]" as ">Hfinalizers".
  { destruct (v.(ObjectMetaV.Finalizers')) as [vfs|]; last done.
    iDestruct "Hdeepown_finalizers_some" as (cfs) "[Hcfs %Hcfs]".
    iMod (own_slice_persist with "Hcfs") as "Hcfs". iModIntro. iExists cfs. by iFrame "∗ %". }
  iAssert (|==> match v.(ObjectMetaV.ManagedFields') with
    | Some vms => ∃ cms, c.(v1.ObjectMeta.ManagedFields') ↦*{DfracDiscarded} cms ∗
        [∗ list] cm;vm ∈ cms;vms, ManagedFieldsEntryV.deepown cm vm DfracDiscarded
    | None => True%I
    end)%I with "[Hdeepown_managedfields_some]" as ">Hmanaged".
  { destruct (v.(ObjectMetaV.ManagedFields')) as [vms|]; last done.
    iDestruct "Hdeepown_managedfields_some" as (cms) "[Hcms Hlist]".
    iMod (own_slice_persist with "Hcms") as "Hcms".
    iMod (big_sepL2_persist ManagedFieldsEntryV.deepown with "Hlist") as "Hlist".
    { intros. apply managed_fields_entry_deepown_persist. }
    iModIntro. iExists cms. by iFrame. }
  iModIntro. by iFrame "∗ # %".
Qed.

#[global] Instance objectmeta_deepown_persistent c v :
  Persistent (ObjectMetaV.deepown c v DfracDiscarded).
Proof.
  rewrite /ObjectMetaV.deepown.
  destruct (v.(ObjectMetaV.DeletionTimestamp')), (v.(ObjectMetaV.DeletionGracePeriodSeconds')),
    (v.(ObjectMetaV.Labels')), (v.(ObjectMetaV.Annotations')), (v.(ObjectMetaV.OwnerReferences')),
    (v.(ObjectMetaV.Finalizers')), (v.(ObjectMetaV.ManagedFields'));
    apply _.
Qed.

Lemma objectmeta_deepown_l_persist l v dq :
  ObjectMetaV.deepown_l l v dq ⊢ |==> ObjectMetaV.deepown_l l v DfracDiscarded.
Proof.
  iDestruct 1 as (c) "[Hl Hdeepown]".
  iPersist "Hl". iMod (objectmeta_deepown_persist with "Hdeepown") as "Hdeepown".
  iModIntro. iExists c. by iFrame "∗ #".
Qed.

#[global] Instance objectmeta_deepown_l_persistent l v :
  Persistent (ObjectMetaV.deepown_l l v DfracDiscarded).
Proof. rewrite /ObjectMetaV.deepown_l. apply _. Qed.

Lemma volume_source_deepown_persist c v dq :
  VolumeSourceV.deepown c v dq ⊢ |==> VolumeSourceV.deepown c v DfracDiscarded.
Proof.
  rewrite /VolumeSourceV.deepown. iNamed 1.
  iAssert (|==> match v.(VolumeSourceV.PersistentVolumeClaim') with
    | Some pvc => ∃ c_pvc, c.(v1.VolumeSource.PersistentVolumeClaim') ↦□ c_pvc ∗ ⌜ c_pvc = pvc ⌝
    | None => True%I
    end)%I with "[Hdeepown_persistentvolumeclaim_some]" as ">Hpvc".
  { destruct (v.(VolumeSourceV.PersistentVolumeClaim')) as [pvc|]; last done.
    iDestruct "Hdeepown_persistentvolumeclaim_some" as (c_pvc) "[Hc %Hc]".
    iPersist "Hc". iModIntro. iExists c_pvc. by iFrame "# %". }
  iModIntro. by iFrame "∗ # %".
Qed.

#[global] Instance volume_source_deepown_persistent c v :
  Persistent (VolumeSourceV.deepown c v DfracDiscarded).
Proof.
  rewrite /VolumeSourceV.deepown. destruct (v.(VolumeSourceV.PersistentVolumeClaim')); apply _.
Qed.

Lemma volume_deepown_persist c v dq :
  VolumeV.deepown c v dq ⊢ |==> VolumeV.deepown c v DfracDiscarded.
Proof.
  rewrite /VolumeV.deepown. iNamed 1.
  iMod (volume_source_deepown_persist with "Hdeepown_volumesource") as "Hdeepown_volumesource".
  iModIntro. by iFrame "∗ # %".
Qed.

#[global] Instance volume_deepown_persistent c v :
  Persistent (VolumeV.deepown c v DfracDiscarded).
Proof. rewrite /VolumeV.deepown. apply _. Qed.

Lemma pod_spec_deepown_persist c v dq :
  PodSpecV.deepown c v dq ⊢ |==> PodSpecV.deepown c v DfracDiscarded.
Proof.
  rewrite /PodSpecV.deepown. iNamed 1.
  iDestruct "Hdeepown_volumes" as (volumes) "[Hsl Hlist]".
  iMod (own_slice_persist with "Hsl") as "Hsl".
  iMod (big_sepL2_persist VolumeV.deepown with "Hlist") as "Hlist".
  { intros. apply volume_deepown_persist. }
  iModIntro. iFrame "%". iExists volumes. rewrite /deepown_list_dq. by iFrame.
Qed.

#[global] Instance pod_spec_deepown_persistent c v :
  Persistent (PodSpecV.deepown c v DfracDiscarded).
Proof. rewrite /PodSpecV.deepown /deepown_list_dq. apply _. Qed.

Lemma pod_template_spec_deepown_persist c v dq :
  PodTemplateSpecV.deepown c v dq ⊢ |==> PodTemplateSpecV.deepown c v DfracDiscarded.
Proof.
  rewrite /PodTemplateSpecV.deepown. iNamed 1.
  iMod (objectmeta_deepown_persist with "Hdeepown_objectmeta") as "Hdeepown_objectmeta".
  iMod (pod_spec_deepown_persist with "Hdeepown_spec") as "Hdeepown_spec".
  iModIntro. by iFrame.
Qed.

#[global] Instance pod_template_spec_deepown_persistent c v :
  Persistent (PodTemplateSpecV.deepown c v DfracDiscarded).
Proof. rewrite /PodTemplateSpecV.deepown. apply _. Qed.

Lemma pod_template_spec_deepown_l_persist l v dq :
  PodTemplateSpecV.deepown_l l v dq ⊢ |==> PodTemplateSpecV.deepown_l l v DfracDiscarded.
Proof.
  iDestruct 1 as (c) "[Hl Hdeepown]".
  iPersist "Hl". iMod (pod_template_spec_deepown_persist with "Hdeepown") as "Hdeepown".
  iModIntro. iExists c. by iFrame "∗ #".
Qed.

#[global] Instance pod_template_spec_deepown_l_persistent l v :
  Persistent (PodTemplateSpecV.deepown_l l v DfracDiscarded).
Proof. rewrite /PodTemplateSpecV.deepown_l. apply _. Qed.

End persist.
