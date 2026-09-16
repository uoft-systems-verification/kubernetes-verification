(* Discarding fractions of deep ownership.

   The concurrent pod-creating goroutines of the ReplicaSet controller read the
   ReplicaSet's metadata and pod template simultaneously.  Sharing a read across
   goroutines is convenient when the predicate is persistent, which we obtain by
   discarding the fraction ([DfracDiscarded]).  This file proves the discard
   lemmas and persistence instances for the predicates involved.

   Every lemma here is proved from the discard rules of points-to, maps and
   slices.  Predicates whose representation is an opaque axiom in the pure model
   -- [TimeV.deepown] and [ManagedFieldsEntryV.deepown] -- admit no such proof,
   so full [ObjectMetaV.deepown] and [PodTemplateSpecV.deepown] have no discard
   lemma.  Readers that share metadata take a reduced footprint instead
   ([ObjectMetaV.own_scalars], [ObjectMetaV.own_template_meta],
   [PodTemplateSpecV.own_template]), which is also all the code reads. *)
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export pod replicaset.
From New.proof Require Import proof_prelude.

Section persist.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".


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

(* Persistence for the reduced metadata footprints of
   [kubernetes_types/objectmeta.v].  Neither lemma says anything about
   [TimeV.deepown] or [ManagedFieldsEntryV.deepown]: the scalar fields are
   related by pure equalities, and labels, annotations and finalizers are maps
   and slices with established discard rules.  Full [ObjectMetaV.deepown] has
   no discard lemma precisely because its timestamps and managed fields are
   opaque; readers that need to share metadata take one of these instead. *)
Lemma objectmeta_own_scalars_persist l c v dq :
  ObjectMetaV.own_scalars l c v dq ⊢ |==> ObjectMetaV.own_scalars l c v DfracDiscarded.
Proof.
  rewrite /ObjectMetaV.own_scalars. iNamed 1.
  iPersist "Hown_scalars_l". iModIntro. by iFrame "# %".
Qed.

#[global] Instance objectmeta_own_scalars_persistent l c v :
  Persistent (ObjectMetaV.own_scalars l c v DfracDiscarded).
Proof. rewrite /ObjectMetaV.own_scalars. apply _. Qed.

Lemma objectmeta_own_template_meta_persist c v dq :
  ObjectMetaV.own_template_meta c v dq ⊢
    |==> ObjectMetaV.own_template_meta c v DfracDiscarded.
Proof.
  rewrite /ObjectMetaV.own_template_meta. iNamed 1.
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
  iAssert (|==> match v.(ObjectMetaV.Finalizers') with
    | Some vfs => ∃ cfs, c.(v1.ObjectMeta.Finalizers') ↦*{DfracDiscarded} cfs ∗ ⌜ cfs = vfs ⌝
    | None => True%I
    end)%I with "[Hdeepown_finalizers_some]" as ">Hfinalizers".
  { destruct (v.(ObjectMetaV.Finalizers')) as [vfs|]; last done.
    iDestruct "Hdeepown_finalizers_some" as (cfs) "[Hcfs %Hcfs]".
    iMod (own_slice_persist with "Hcfs") as "Hcfs". iModIntro. iExists cfs. by iFrame "∗ %". }
  iModIntro. by iFrame "∗ # %".
Qed.

#[global] Instance objectmeta_own_template_meta_persistent c v :
  Persistent (ObjectMetaV.own_template_meta c v DfracDiscarded).
Proof.
  rewrite /ObjectMetaV.own_template_meta.
  destruct (v.(ObjectMetaV.Labels')), (v.(ObjectMetaV.Annotations')),
    (v.(ObjectMetaV.Finalizers'));
    apply _.
Qed.

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

Lemma pod_template_spec_own_template_persist l c v dq :
  PodTemplateSpecV.own_template l c v dq ⊢
    |==> PodTemplateSpecV.own_template l c v DfracDiscarded.
Proof.
  rewrite /PodTemplateSpecV.own_template. iNamed 1.
  iPersist "Hown_template_l".
  iMod (objectmeta_own_template_meta_persist with "Hown_template_meta")
    as "Hown_template_meta".
  iMod (pod_spec_deepown_persist with "Hown_template_spec") as "Hown_template_spec".
  iModIntro. by iFrame "∗ #".
Qed.

#[global] Instance pod_template_spec_own_template_persistent l c v :
  Persistent (PodTemplateSpecV.own_template l c v DfracDiscarded).
Proof. rewrite /PodTemplateSpecV.own_template. apply _. Qed.

End persist.
