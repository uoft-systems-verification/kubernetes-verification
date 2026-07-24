From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update.
From New.proof.kubernetes_model Require Import get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma valid_simple_update_set_resource_version m_old m rv :
  ObjectMetaV.valid_simple_update m_old m →
  ObjectMetaV.valid_simple_update
    m_old (m <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  rewrite /ObjectMetaV.valid_simple_update.
  destruct m_old, m; simpl; intuition congruence.
Qed.

Lemma objectmeta_updated_unset_resource_version_input m rv m' :
  ObjectMetaV.updated (m <| ObjectMetaV.ResourceVersion' := rv |>) m' →
  ObjectMetaV.updated m m'.
Proof.
  rewrite /ObjectMetaV.updated.
  destruct m, m'; simpl; intuition congruence.
Qed.

Lemma wp_State__updateTx_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ key uid kmeta kspec,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_updated" ∷ ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj'),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)".
  iNamed "H".
  wp_method_call. rewrite /apimodel.State__updateTxⁱᵐᵖˡ. wp_call. wp_auto.
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ key uid kmeta kspec,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update
        kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update
        kspec (KObjectV.spec kobj) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated
        (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_updated" ∷ ⌜ ObjectSpecV.updated
        (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj'),
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
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go) as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _).
    eapply ObjectMetaV.valid_name_nonempty_of_valid. done. }
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
  iMod "Hau" as (key0 uid kmeta kspec) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. done. }
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  iExists uid, (DfracOwn 1), kmeta, (Some kspec), None.
  iFrame "Hown_meta_frag Hown_spec_frag".
  iSplit; first done.
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_existing & %Hkey_existing & %Hmeta_eq &
    Hdeepown_existing_i & Hown_meta_frag & (Hown_spec_frag & %Hspec_eq) & _)".
  iMod ("Habort" with "[Hown_meta_frag Hown_spec_frag]") as "Hau".
  { iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  clear uid kmeta kspec Hkey_eq Huid_eq Hvalid_meta_update
    Hvalid_spec_update Hno_deletion_timestamp Hmeta_eq Hspec_eq.
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
  { destruct Hvalid_existing as (_ & Hrv_valid & _). done. }
  assert (KObjectV.valid kobj_rv) as Hvalid_rv.
  { subst kobj_rv kmeta_rv.
    apply valid_update_objectmeta_set_resource_version; done. }
  assert (kind = KObjectV.kind kobj_rv) as Hkind_matches_rv.
  { subst kobj_rv. rewrite KObjectV.kind_update_objectmeta. done. }
  assert (namespace = ObjectMetaV.Namespace' (KObjectV.objectmeta kobj_rv)) as
    Hns_matches_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. simpl. done. }
  wp_apply (wp_State__update_au γ l kind namespace i_copy kobj_rv).
  iFrame "#".
  iFrame "Hdeepown_i_copy".
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iMod "Hau" as (key1 uid1 kmeta1 kspec1) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  iExists key1, uid1, kmeta1, kspec1.
  iFrame "Hown_meta_frag Hown_spec_frag".
  iSplit.
  { iPureIntro. rewrite Hkey_eq. subst kobj_rv kmeta_rv.
    rewrite key_update_objectmeta_set_resource_version. done. }
  iSplit.
  { iPureIntro. rewrite Huid_eq. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta. done. }
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    apply valid_simple_update_set_resource_version. done. }
  iSplit.
  { iPureIntro. subst kobj_rv.
    rewrite KObjectV.spec_update_objectmeta. done. }
  iSplit; first done.
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as "(%Hmeta_updated & %Hspec_updated &
      Hdeepown_i & Hown_meta_frag & Hown_spec_frag)".
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' kobj' with
      "[Hdeepown_i Hown_meta_frag Hown_spec_frag]") as "HΦ".
    { iSplit.
      { iPureIntro. subst kobj_rv kmeta_rv.
        rewrite objectmeta_update_objectmeta in Hmeta_updated.
        eapply objectmeta_updated_unset_resource_version_input. done. }
      iSplit.
      { iPureIntro. subst kobj_rv.
        rewrite KObjectV.spec_update_objectmeta in Hspec_updated. done. }
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
    iDestruct "Hconflict" as "(%Herr_ne & %Hconflict &
      Hown_meta_frag & Hown_spec_frag)".
    iDestruct "Hclose" as "[Habort _]".
    iMod ("Habort" with "[Hown_meta_frag Hown_spec_frag]") as "Hau".
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

Lemma wp_State__updateTx γ l kind namespace i kobj key uid kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec
  }}}
    l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj', RET (#(interface.ok i'), #interface.nil);
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_updated" ∷ ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj')
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ".
  iNamed "H".
  iApply wp_State__updateTx_au.
  iFrame "#".
  iFrame "%".
  iFrame "Hdeepown_i".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert ((
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
    "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
    "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
    "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
    "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
    "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
    "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝
  )%I) with "[Hown_meta_frag Hown_spec_frag]" as "Hpre".
  { iFrame. iFrame "%". }
  iAaccIntro with "Hpre".
  - iIntros "Hpre".
    iNamed "Hpre".
    iFrame. done.
  - iIntros (i' kobj') "Hpost".
    iModIntro. iNext.
    iApply ("HΦ" $! i' kobj' with "Hpost").
Qed.

End proof.
