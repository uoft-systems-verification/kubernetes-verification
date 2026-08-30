From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status.
From New.proof.kubernetes_model Require Import common_update get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__updateStatusTx_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_status,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_status ∗
      "%Hvalid_status_update" ∷ ⌜ KObjectV.valid_status_update kind namespace old_meta old_status kobj ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' old_spec kobj',
      "%Hvalid_updated" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hstatus_updated" ∷ ⌜ KObjectV.status_updated old_spec kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.status kobj'),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatusTx" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)".
  iNamed "H".
  destruct (Classical_Prop.classic (
      kind = KObjectV.kind kobj ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ∧
      namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
      valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
      valid_labels (KObjectV.objectmeta kobj).(ObjectMetaV.Labels') ∧
      valid_annotations (KObjectV.objectmeta kobj).(ObjectMetaV.Annotations') ∧
      valid_owner_references (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') ∧
      valid_finalizers (KObjectV.objectmeta kobj).(ObjectMetaV.Finalizers') ∧
      valid_managed_fields (KObjectV.objectmeta kobj).(ObjectMetaV.ManagedFields')))
    as [Hvalid_status_update_input|Hinvalid_status_update_input].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (old_meta old_status) "[Hau_pre Hclose]".
    iNamed "Hau_pre".
    exfalso. apply Hinvalid_status_update_input.
    destruct old_status, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update;
      try contradiction; tauto.
  }
  destruct Hvalid_status_update_input as
    (Hkind_matches & Hname_not_empty & Huid_nonempty & Hns_matches & Hrv_valid &
      Hvalid_typemeta & Hlabels & Hannotations & Howners &
      Hfinalizers & Hmanaged_fields).
  wp_method_call. rewrite /apimodel.State__updateStatusTxⁱᵐᵖˡ. wp_call. wp_auto.
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_status,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_status ∗
      "%Hvalid_status_update" ∷
        ⌜ KObjectV.valid_status_update kind namespace old_meta old_status kobj ⌝ ∗
      "%Hvalid_simple_update" ∷
        ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' old_spec kobj',
      "%Hvalid_updated" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hstatus_updated" ∷ ⌜ KObjectV.status_updated old_spec kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.status kobj'),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
  )%I.
  iAssert I with "[obj Hdeepown_i Hau]" as "Hloop_inv".
  { iExists i. iFrame. }
  wp_for "Hloop_inv".
  wp_apply (wp_deepCopy i_orig kobj with "[Hdeepown_i_orig]").
  { iFrame "#". iExact "Hdeepown_i_orig". }
  iIntros (i_copy) "[Hdeepown_i_copy Hdeepown_i_orig]". wp_auto.
  iDestruct "Hdeepown_i_copy" as (kobj_l) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hkobj_l_not_null & Htypemeta & Hdeepown_metadata & Hdeepown_spec & Hdeepown_status)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_metadata]").
  { iPureIntro. split. 1: done. right. done. }
  iIntros "Hdeepown_metadata". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_metadata]").
  iIntros "Hdeepown_metadata". wp_auto.
  rewrite bool_decide_false //. wp_auto.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  wp_apply (wp_State__get_some_au γ l key).
  iFrame "#".
  iMod "Hau" as (old_meta old_status) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  rewrite Hkey_new.
  iExists (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), (DfracOwn 1),
    old_meta, None, (Some old_status).
  iFrame "Hown_meta_frag Hown_status_frag".
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_existing & %Hextra_valid_existing &
    %Hkey_existing & %Hmeta_eq &
    Hdeepown_existing_i & Hown_meta_frag & _ & (Hown_status_frag & %Hstatus_eq))".
  iMod ("Habort" with "[Hown_meta_frag Hown_status_frag]") as "Hau".
  { iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  clear old_meta old_status Hvalid_status_update Hvalid_simple_update Hmeta_eq Hstatus_eq.
  iDestruct "Hdeepown_existing_i" as (existing_l) "[%Hvalid_interface_existing Hdeepown_existing_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_existing_l") as
    "(%Hexisting_l_not_null & Htypemeta_existing & Hdeepown_existing_metadata & Hdeepown_existing_spec &
      Hdeepown_existing_status)".
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_existing_metadata]").
  iIntros "Hdeepown_existing_metadata". wp_auto.
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_metadata]").
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
    { iPureIntro. subst kobj_rv kmeta_rv. destruct kobj; done. }
    iFrame. }
  assert (valid_resource_version
    (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj))) as
    Hexisting_rv_valid.
  { destruct Hvalid_existing as (_ & Hrv_existing & _). done. }
  wp_apply (wp_State__update_status_au γ l kind namespace i_copy kobj_rv).
  iFrame "#".
  iFrame "Hdeepown_i_copy".
  iMod "Hau" as (old_meta old_status) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  iExists (KObjectV.key kobj),
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), old_meta, old_status.
  iFrame "Hown_meta_frag Hown_status_frag".
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta kobj)) as Hmeta.
    { destruct old_status, kobj;
        rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
        rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
          ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
          in Hvalid_status_update;
        try contradiction; tauto. }
    assert (ObjectMetaV.valid_update old_meta
        ((KObjectV.objectmeta kobj) <| ObjectMetaV.ResourceVersion' :=
          ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>)) as Hmeta_rv.
    { remember (KObjectV.objectmeta kobj) as input_meta eqn:Heq_input_meta in Hmeta |- *.
      destruct input_meta.
      destruct Hmeta as ([Hmeta_simple | Hmeta_release] & Hmeta_labels & Hmeta_annotations & Hmeta_owners &
        Hmeta_finalizers & Hmeta_managed_fields).
      - split.
        + left. revert Hmeta_simple. rewrite /ObjectMetaV.valid_simple_update.
          destruct old_meta; simpl; intuition congruence.
        + split_and!; done.
      - split.
        + right. exact Hmeta_release.
        + split_and!; done. }
    destruct old_status, kobj;
      rewrite /KObjectV.valid_status_update /= in Hvalid_status_update |- *;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update |- *;
      simpl in Hmeta_rv |- *; try contradiction; tauto. }
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.valid_simple_update in Hvalid_simple_update |- *.
    destruct old_meta, (KObjectV.objectmeta kobj); simpl in *; intuition congruence. }
  iSplit.
  - iIntros (i' old_spec kobj') "Hsuccess".
    iDestruct "Hsuccess" as "(%Hvalid_updated & %Hstatus_updated & Hdeepown_i &
      Hown_meta_frag & Hown_status_frag)".
    assert (KObjectV.status_updated old_spec kobj kobj') as Hstatus_updated_original.
    { subst kobj_rv kmeta_rv.
      revert Hstatus_updated.
      destruct old_spec, kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hspec & Hstatus); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence. }
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' old_spec kobj' with
      "[Hdeepown_i Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iSplit; first done.
      iSplit; first (iPureIntro; exact Hstatus_updated_original).
      iFrame. }
    iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact conflict_error_nil).
    wp_auto.
    wp_for_post.
    iApply "HΦ".
  - iIntros (err) "Hconflict".
    iDestruct "Hconflict" as "(%Hconflict &
      Hown_meta_frag & Hown_status_frag)".
    pose proof (conflict_error_not_nil err Hconflict) as Herr_ne.
    iDestruct "Hclose" as "[Habort _]".
    iMod ("Habort" with "[Hown_meta_frag Hown_status_frag]") as "Hau".
    { iFrame. iFrame "%". }
    iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict err with "[]").
    replace (bool_decide (conflict_error err)) with true by
      (symmetry; apply bool_decide_true; done).
    wp_auto.
    wp_for_post.
    iFrame "s kind namespace".
    iExists i_orig. iFrame.
Qed.

Lemma wp_State__updateStatusTx γ l kind namespace i kobj old_meta old_status :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_status_update" ∷
        ⌜ KObjectV.valid_status_update kind namespace old_meta old_status kobj ⌝ ∗
      "%Hvalid_simple_update" ∷
        ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_status
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatusTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj', RET (#(interface.ok i'), #interface.nil);
      "%Hvalid_updated" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      ∃ old_spec,
      "%Hstatus_updated" ∷ ⌜ KObjectV.status_updated old_spec kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.status kobj')
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ".
  iNamed "H".
  iApply wp_State__updateStatusTx_au.
  iFrame "#".
  iFrame "Hdeepown_i".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert ((
    "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
    "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_status ∗
    "%Hvalid_status_update" ∷
      ⌜ KObjectV.valid_status_update kind namespace old_meta old_status kobj ⌝ ∗
    "%Hvalid_simple_update" ∷
      ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
  )%I) with "[Hown_meta_frag Hown_status_frag]" as "Hpre".
  { iFrame. iFrame "%". }
  iAaccIntro with "Hpre".
  - iIntros "Hpre".
    iNamed "Hpre".
    iFrame. done.
  - iIntros (i' old_spec kobj') "Hpost".
    iModIntro. iNext.
    iApply ("HΦ" $! i' kobj').
    iDestruct "Hpost" as "($ & Hpost)".
    iExists old_spec. iExact "Hpost".
Qed.

End proof.
