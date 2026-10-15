From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status_same_meta.
From New.proof.kubernetes_model.tx Require Export update_status.
From New.proof.kubernetes_model Require Import common_update get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

(* A variant of [wp_State__updateStatusTx] built on
   [wp_State__update_status_same_meta_au]: the request keeps the stored metadata
   except for the resource version ([Hmeta_same]), so the metadata fragment may
   be held at any fraction and is returned unchanged. Each attempt writes at the
   currently stored resource version and conflicts are retried; the request
   must be valid, so the write always succeeds. The input is only read, at
   fraction [dq_in]. *)
Lemma wp_State__updateStatusTx_same_meta γ l kind namespace i kobj dq_in uid dq kmeta kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_status_update" ∷ ⌜ KObjectV.valid_status_update kind namespace kmeta kstatus kobj ⌝ ∗
      "%Hmeta_same" ∷ ⌜ ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj dq_in ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatusTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj', RET (#(interface.ok i'), #interface.nil);
      KObjectV.deepown_i i kobj dq_in ∗
      own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
      ⌜ KObjectV.valid kobj' ⌝ ∗
      ⌜ KObjectV.status_updated kobj kobj' ⌝ ∗
      ⌜ KObjectV.same_kind kobj kobj' ∧
        ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj') kmeta ⌝ ∗
      KObjectV.deepown_i i' kobj' 1 ∗
      own_status_frag γ (KObjectV.key kobj) uid 1 (KObjectV.status kobj')
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  pose proof (valid_status_update_request_ok _ _ _ _ _ Hvalid_status_update) as (Hkind_matches & Hname_not_empty & Huid_nonempty & Hns_matches & Hrv_valid &
    Hvalid_typemeta & Hlabels & Hannotations & Howners & Hfinalizers & Hmanaged_fields).
  wp_auto.
  (* A conflict leaves every fragment as it was, so the loop just keeps them. *)
  set I := (
    "obj" ∷ obj_ptr ↦ interface.ok i ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj dq_in ∗
    "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
    "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus)%I.
  iAssert I with "[obj Hdeepown_i Hown_meta_frag Hown_status_frag]" as "Hloop_inv".
  { iFrame. }
  wp_for "Hloop_inv".
  wp_apply (wp_deepCopy i kobj dq_in with "[$Hdeepown_i]").
  iIntros (i_copy) "[Hdeepown_i_copy Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i_copy" as (kobj_l) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hkobj_l_not_null & Htypemeta & Hdeepown_metadata & Hdeepown_spec & Hdeepown_status)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_metadata]").
  { iPureIntro. split. 1: done. right. done. }
  iIntros "Hdeepown_metadata". wp_auto.
  wp_apply (wp_GetName_deepown_kobject i_copy kobj_l kobj with
    "[$Hdeepown_metadata]"). 1: done.
  iIntros "Hdeepown_metadata". wp_auto.
  rewrite bool_decide_false //. wp_auto.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  rewrite Hkey_new.
  wp_apply (wp_State__get_some γ l (KObjectV.key kobj) uid dq (DfracOwn 1) kmeta None (Some kstatus)
    with "[$Hown_meta_frag $Hown_status_frag]").
  { iFrame "#". }
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_existing & %Hextra_valid_existing & %Hkey_existing & %Hmeta_eq &
    Hdeepown_existing_i & Hown_meta_frag & _ & Hown_status_frag & %Hstatus_eq)".
  wp_auto.
  iDestruct "Hdeepown_existing_i" as (existing_l) "[%Hvalid_interface_existing Hdeepown_existing_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_existing_l") as
    "(%Hexisting_l_not_null & Htypemeta_existing & Hdeepown_existing_metadata & Hdeepown_existing_spec &
      Hdeepown_existing_status)".
  wp_apply (wp_GetResourceVersion_deepown_kobject existing_i existing_l existing_kobj with
    "[$Hdeepown_existing_metadata]"). 1: done.
  iIntros "Hdeepown_existing_metadata". wp_auto.
  wp_apply (wp_SetResourceVersion_deepown_kobject i_copy kobj_l kobj with
    "[$Hdeepown_metadata]"). 1: done.
  iIntros "Hdeepown_metadata". wp_auto.
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := namespace |>) =
    KObjectV.objectmeta kobj) as Hnamespace_noop.
  { rewrite Hns_matches. destruct (KObjectV.objectmeta kobj); done. }
  iEval (rewrite Hnamespace_noop) in "Hdeepown_metadata".
  set kmeta_rv := (KObjectV.objectmeta kobj <| ObjectMetaV.ResourceVersion' :=
    ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>).
  set kobj_rv := KObjectV.update_objectmeta kobj kmeta_rv.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hkobj_l_not_null with
    "[$Htypemeta $Hdeepown_metadata $Hdeepown_spec $Hdeepown_status]") as
    "Hdeepown_l".
  iAssert (KObjectV.deepown_i i_copy kobj_rv 1) with "[Hdeepown_l]" as
    "Hdeepown_i_copy".
  { iExists kobj_l. iSplit.
    { iPureIntro. subst kobj_rv kmeta_rv. destruct kobj; exact Hvalid_interface. }
    iFrame. }
  assert (valid_resource_version
    (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj))) as
    Hexisting_rv_valid.
  { destruct Hvalid_existing as (_ & Hrv_existing & _). done. }
  (* The request stays valid at the stored resource version. *)
  assert (KObjectV.valid_status_update kind namespace kmeta kstatus kobj_rv) as Hvalid_rv.
  { subst kobj_rv kmeta_rv.
    assert (ObjectMetaV.valid_update kmeta (KObjectV.objectmeta kobj)) as Hmeta.
    { destruct kstatus, kobj;
        rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
        rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
          ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
          ?/DeploymentV.valid_status_update
          in Hvalid_status_update;
        try contradiction; tauto. }
    assert (ObjectMetaV.valid_update kmeta
        ((KObjectV.objectmeta kobj) <| ObjectMetaV.ResourceVersion' :=
          ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>)) as Hmeta_rv.
    { remember (KObjectV.objectmeta kobj) as input_meta eqn:Heq_input_meta in Hmeta |- *.
      destruct input_meta.
      destruct Hmeta as ([Hmeta_simple | Hmeta_release] & Hmeta_labels & Hmeta_annotations & Hmeta_owners &
        Hmeta_finalizers & Hmeta_managed_fields).
      - split.
        + left. revert Hmeta_simple. rewrite /ObjectMetaV.valid_simple_update.
          destruct kmeta; simpl; intuition congruence.
        + split_and!; done.
      - split.
        + right. exact Hmeta_release.
        + split_and!; done. }
    destruct kstatus, kobj;
      rewrite /KObjectV.valid_status_update /= in Hvalid_status_update |- *;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        ?/DeploymentV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update |- *;
      simpl in Hmeta_rv |- *; try contradiction; tauto. }
  wp_apply (wp_State__update_status_same_meta_au γ l kind namespace i_copy kobj_rv).
  iFrame "#". iFrame "Hdeepown_i_copy".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists uid, dq, kmeta, kstatus.
  assert (KObjectV.key kobj_rv = KObjectV.key kobj) as Hkey_rv.
  { subst kobj_rv kmeta_rv. destruct kobj; done. }
  rewrite Hkey_rv.
  iFrame "Hown_meta_frag Hown_status_frag".
  iSplit; first done.
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version
      in Hmeta_same |- *.
    rewrite -Hmeta_same. destruct (KObjectV.objectmeta kobj); done. }
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as "(%Hvalid_updated & %Hstatus_updated & %Hpreserved & Hdeepown_i' &
      Hown_meta_frag & Hown_status_frag)".
    destruct Hpreserved as (Hsame & Hequiv).
    iMod "Hmask" as "_". iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact conflict_error_nil).
    wp_auto.
    wp_for_post.
    iApply "HΦ". iFrame "Hdeepown_i Hown_meta_frag". iFrame. iPureIntro. split_and!; try done.
    + subst kobj_rv kmeta_rv.
      revert Hstatus_updated.
      destruct kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hstatus); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence.
    + subst kobj_rv kmeta_rv. destruct kobj, kobj'; done.
  - (* Another writer advanced the resource version: retry. *)
    iIntros (err) "(%Hconflict & Hown_meta_frag & Hown_status_frag)".
    iMod "Hmask" as "_". iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict err with "[]").
    replace (bool_decide (conflict_error err)) with true by
      (symmetry; apply bool_decide_true; done).
    wp_auto.
    wp_for_post.
    iFrame.
Qed.

End proof.
