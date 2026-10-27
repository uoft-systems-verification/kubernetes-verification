From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export statefulset_init revision_predicates.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.
Section proof.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions :=
  code.controllers.statefulset.statefulset.import_core_v1_Assumption.
#[local] Instance meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  code.controllers.statefulset.statefulset.import_meta_v1_Assumption.
Local Set Default Proof Using "All".

Lemma wp_getPodRevision pod_l (pod : PodV.t) dq :
  {{{ PodV.deepown_l pod_l pod dq }}}
    @! statefulset.getPodRevision #pod_l
  {{{ RET #(pod_revision pod); PodV.deepown_l pod_l pod dq }}}.
Proof.
  wp_start as "Hpod".
  iDestruct (PodV.deepown_l_split with "Hpod") as
    "(%Hne & Htm & Hmeta & Hspec & Hstatus)".
  iDestruct "Hmeta" as (cm) "[Hm Hmeta]".
  iNamed "Hmeta".
  wp_auto_keep.
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [ls|] eqn:Hlabels.
  - iDestruct "Hdeepown_labels_some" as (ls_c) "[Hlabels %Heq]". subst ls_c.
    wp_apply (wp_map_lookup1 with "Hlabels") as "Hlabels".
    iCombineNamed "Hdeepown_*" as "Hrest".
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l) pod.(PodV.ObjectMeta') dq)
      with "[Hm Hrest Hlabels]" as "Hmeta".
    { iExists cm. iFrame "Hm". rewrite /ObjectMetaV.deepown Hlabels.
      iNamed "Hrest". iFrame. done. }
    iEval (rewrite /pod_revision Hlabels /= /statefulset_revision_label) in "HΦ".
    iApply "HΦ". iApply (PodV.deepown_l_restore _ _ _ Hne with "[$]").
  - assert (cm.(v1.ObjectMeta.Labels') = map.nil) as Hnil by (apply Hdeepown_labels_none; done).
    rewrite Hnil. wp_auto_keep.
    iCombineNamed "Hdeepown_*" as "Hrest".
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l) pod.(PodV.ObjectMeta') dq)
      with "[Hm Hrest]" as "Hmeta".
    { iExists cm. iFrame "Hm". rewrite /ObjectMetaV.deepown Hlabels.
      iNamed "Hrest". iFrame. done. }
    iEval (rewrite /pod_revision Hlabels /= /statefulset_revision_label) in "HΦ".
    iApply "HΦ". iApply (PodV.deepown_l_restore _ _ _ Hne with "[$]").
Qed.

Lemma wp_setPodRevision pod_l (pod : PodV.t) revision :
  {{{ PodV.deepown_l pod_l pod 1 }}}
    @! statefulset.setPodRevision #pod_l #revision
  {{{ RET #(); PodV.deepown_l pod_l (with_pod_revision pod revision) 1 }}}.
Proof.
  wp_start as "Hpod".
  iDestruct (PodV.deepown_l_split with "Hpod") as
    "(%Hne & Htm & Hmeta & Hspec & Hstatus)".
  iDestruct "Hmeta" as (cm) "[Hm Hmeta]".
  iNamed "Hmeta". wp_auto_keep.
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [ls|] eqn:Hlabels.
  - iDestruct "Hdeepown_labels_some" as (ls_c) "[Hlabels %Heq]". subst ls_c.
    iDestruct (own_map_not_nil with "Hlabels") as %Hnonnull.
    wp_if_destruct; first done.
    wp_apply (wp_map_insert go.string with "Hlabels") as "Hlabels".
    iCombineNamed "Hdeepown_*" as "Hrest".
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Labels' :=
        Some (<[statefulset_revision_label := revision]> ls) |>) 1)
      with "[Hm Hrest Hlabels]" as "Hmeta".
    { iExists cm. iFrame "Hm". rewrite /ObjectMetaV.deepown /=.
      iNamed "Hrest". iFrame. repeat (iSplit; first done).
      all: try (iPureIntro; tauto). }
    iApply "HΦ". rewrite /with_pod_revision Hlabels /=.
    iApply (PodV.deepown_l_merge _ _ _ _ Hne with "[$]").
  - assert (cm.(v1.ObjectMeta.Labels') = map.nil) as Hnil by (apply Hdeepown_labels_none; done).
    rewrite Hnil. wp_auto_keep.
    wp_apply wp_map_make1 as "%labels_l Hlabels".
    wp_apply (wp_map_insert go.string with "Hlabels") as "Hlabels".
    iDestruct (own_map_not_nil with "Hlabels") as %Hnonnull.
    iCombineNamed "Hdeepown_*" as "Hrest".
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Labels' :=
        Some (<[statefulset_revision_label := revision]> ∅) |>) 1)
      with "[Hm Hrest Hlabels]" as "Hmeta".
    { iExists (cm <| v1.ObjectMeta.Labels' := labels_l |>).
      iFrame "Hm". rewrite /ObjectMetaV.deepown /=.
      iNamed "Hrest". iFrame. repeat (iSplit; first done).
      all: try (iPureIntro; tauto). }
    iApply "HΦ". rewrite /with_pod_revision Hlabels /=.
    iApply (PodV.deepown_l_merge _ _ _ _ Hne with "[$]").
Unshelve. all: apply _.
Qed.

Lemma wp_podRevisionMatches pod_l (pod : PodV.t) dq revision :
  {{{ PodV.deepown_l pod_l pod dq }}}
    @! statefulset.podRevisionMatches #pod_l #revision
  {{{ (matches : bool), RET #matches;
      ⌜ matches = true ↔ pod_revision_member revision pod ⌝ ∗
      PodV.deepown_l pod_l pod dq
  }}}.
Proof.
  wp_start as "Hpod". wp_auto_keep.
  wp_apply (wp_getPodRevision with "Hpod") as "Hpod".
  iApply "HΦ". iFrame.
  iPureIntro. unfold pod_revision_member. rewrite bool_decide_eq_true. done.
Qed.
End proof.
