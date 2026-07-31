From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_release.
From New.proof.kubernetes_model Require Import get.
From New.proof.kubernetes_model.tx Require Import update.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* Transactional update contract for releasing an object from its controller
   parent. Conflicts are retried internally, so the outer atomic update only
   commits the successful metadata and child-relation transition. *)
Lemma wp_State__updateTx_release_au γ l kind namespace i kobj parent_key parent_uid dq :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ key uid old_meta old_spec children,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hold_parent" ∷ ⌜ meta_parent_ref old_meta = Some (parent_key, parent_uid) ⌝ ∗
      "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
      "%Howner_references_only" ∷
        ⌜ ObjectMetaV.equiv_except_resource_version
            (old_meta <| ObjectMetaV.OwnerReferences' :=
              (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
            (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "%Hparent_released" ∷ ⌜ obj_parent_ref kobj' = None ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ KObjectV.key kobj' = key ⌝ ∗
      "%Huid_eq'" ∷ ⌜ (KObjectV.objectmeta kobj').(ObjectMetaV.UID') = uid ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷
        own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      ( "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)". iNamed "H".
  wp_method_call. rewrite /apimodel.State__updateTxⁱᵐᵖˡ.
  wp_call. wp_auto.
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ key uid old_meta old_spec children,
      "Hown_meta_frag" ∷
        own_meta_frag γ key uid 1 old_meta ∗
      "Hown_spec_frag" ∷
        own_spec_frag γ key uid dq old_spec ∗
      "Hown_children_frag" ∷
        own_children_frag γ parent_key parent_uid 1 children ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷
        ⌜ uid =
          (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hold_parent" ∷
        ⌜ meta_parent_ref old_meta =
          Some (parent_key, parent_uid) ⌝ ∗
      "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
      "%Howner_references_only" ∷
        ⌜ ObjectMetaV.equiv_except_resource_version
            (old_meta <| ObjectMetaV.OwnerReferences' :=
              (KObjectV.objectmeta kobj).(
                ObjectMetaV.OwnerReferences') |>)
            (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hspec_eq" ∷
        ⌜ KObjectV.spec kobj = old_spec ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hsame_kind" ∷
        ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "%Hmeta_updated" ∷
        ⌜ ObjectMetaV.updated
            (KObjectV.objectmeta kobj)
            (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_unchanged" ∷
        ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "%Hparent_released" ∷
        ⌜ obj_parent_ref kobj' = None ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ KObjectV.key kobj' = key ⌝ ∗
      "%Huid_eq'" ∷
        ⌜ (KObjectV.objectmeta kobj').(ObjectMetaV.UID') =
          uid ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      ( "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
  )%I.
  iAssert I with "[obj Hdeepown_i Hau]" as "Hloop_inv".
  { iExists i. iFrame. }
  wp_for "Hloop_inv".
  wp_apply (wp_deepCopy i_orig kobj with "[Hdeepown_i_orig]").
  { iFrame "#". iExact "Hdeepown_i_orig". }
  iIntros (i_copy)
    "[Hdeepown_i_copy Hdeepown_i_orig]". wp_auto.
  iDestruct "Hdeepown_i_copy" as
    (kobj_l) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hkobj_l_not_null & Htypemeta & Hdeepown_metadata &
      Hdeepown_spec & Hdeepown_status)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with
    "[$Hdeepown_metadata]").
  { iPureIntro. split; [done|]. right. done. }
  iIntros "Hdeepown_metadata". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_metadata]").
  iIntros "Hdeepown_metadata". wp_auto.
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go)
    as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _).
    eapply ObjectMetaV.valid_name_nonempty_of_valid. done. }
  rewrite bool_decide_false //. wp_auto.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' :=
      ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches.
    destruct kobj; done. }
  wp_apply (wp_State__get_some_au γ l key).
  iFrame "#".
  iMod "Hau" as
    (key0 uid old_meta old_spec children)
    "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. done. }
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  iExists uid, (DfracOwn 1), old_meta, None, None.
  iFrame "Hown_meta_frag".
  iSplit; first done.
  iSplit; first done.
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as
    "(%Hvalid_existing & %Hkey_existing & %Hmeta_eq &
      Hdeepown_existing_i & Hown_meta_frag & _ & _)".
  iMod ("Habort" with
    "[Hown_meta_frag Hown_spec_frag Hown_children_frag]")
    as "Hau".
  { iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  clear uid old_meta old_spec children Hkey_eq Huid_eq
    Hold_parent Hchild Howner_references_only Hspec_eq Hmeta_eq.
  iDestruct "Hdeepown_existing_i" as
    (existing_l)
    "[%Hvalid_interface_existing Hdeepown_existing_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof
    (KObjectV.deepown_l_split with "Hdeepown_existing_l")
    as "(%Hexisting_l_not_null & Htypemeta_existing &
      Hdeepown_existing_metadata & Hdeepown_existing_spec &
      Hdeepown_existing_status)".
  wp_apply (wp_GetResourceVersion_deepown with
    "[$Hdeepown_existing_metadata]").
  iIntros "Hdeepown_existing_metadata". wp_auto.
  wp_apply (wp_SetResourceVersion_deepown with
    "[$Hdeepown_metadata]").
  iIntros "Hdeepown_metadata". wp_auto.
  assert ((KObjectV.objectmeta kobj <|
      ObjectMetaV.Namespace' := namespace |>) =
    KObjectV.objectmeta kobj) as Hnamespace_noop.
  { rewrite Hns_matches.
    destruct (KObjectV.objectmeta kobj); done. }
  iEval (rewrite Hnamespace_noop) in "Hdeepown_metadata".
  set kmeta_rv :=
    (KObjectV.objectmeta kobj <|
      ObjectMetaV.ResourceVersion' :=
        ObjectMetaV.ResourceVersion'
          (KObjectV.objectmeta existing_kobj) |>).
  set kobj_rv := KObjectV.update_objectmeta kobj kmeta_rv.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _
    Hkobj_l_not_null with
    "[$Htypemeta $Hdeepown_metadata $Hdeepown_spec
      $Hdeepown_status]") as "Hdeepown_l".
  iAssert (KObjectV.deepown_i i_copy kobj_rv 1)
    with "[Hdeepown_l]" as "Hdeepown_i_copy".
  { iExists kobj_l. iSplit.
    { iPureIntro. subst kobj_rv kmeta_rv.
      destruct kobj; done. }
    iFrame. }
  assert (valid_resource_version
    (ObjectMetaV.ResourceVersion'
      (KObjectV.objectmeta existing_kobj)))
    as Hexisting_rv_valid.
  { destruct Hvalid_existing as (_ & Hrv_valid & _).
    done. }
  assert (KObjectV.valid kobj_rv) as Hvalid_rv.
  { subst kobj_rv kmeta_rv.
    apply valid_update_objectmeta_set_resource_version;
      done. }
  assert (kind = KObjectV.kind kobj_rv)
    as Hkind_matches_rv.
  { subst kobj_rv.
    rewrite KObjectV.kind_update_objectmeta. done. }
  assert (namespace =
    ObjectMetaV.Namespace' (KObjectV.objectmeta kobj_rv))
    as Hns_matches_rv.
  { subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta. simpl. done. }
  assert (obj_parent_ref kobj_rv = None)
    as Hnew_parent_rv.
  { subst kobj_rv kmeta_rv.
    unfold obj_parent_ref.
    rewrite objectmeta_update_objectmeta.
    exact Hnew_parent. }
  wp_apply (wp_State__update_release_au γ l kind namespace
    i_copy kobj_rv parent_key parent_uid dq).
  iFrame "#".
  iFrame "Hdeepown_i_copy".
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  iMod "Hau" as
    (key1 uid1 old_meta1 old_spec1 children1)
    "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  iExists key1, uid1, old_meta1, old_spec1, children1.
  iFrame "Hown_meta_frag Hown_spec_frag Hown_children_frag".
  iSplit.
  { iPureIntro. rewrite Hkey_eq.
    subst kobj_rv kmeta_rv.
    rewrite key_update_objectmeta_set_resource_version.
    done. }
  iSplit.
  { iPureIntro. rewrite Huid_eq.
    subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta. done. }
  iSplit; first done.
  iSplit; first done.
  iSplit.
  { iPureIntro.
    subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in
      Howner_references_only |- *.
    destruct old_meta1, (KObjectV.objectmeta kobj);
      simpl in *.
    exact Howner_references_only. }
  iSplit.
  { iPureIntro. subst kobj_rv.
    rewrite KObjectV.spec_update_objectmeta. done. }
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as
      "(%Hvalid' & %Hsame_kind & %Hmeta_updated &
        %Hspec_unchanged & %Hparent_released &
        %Hkey_eq' & %Huid_eq' & Hdeepown_i &
        Hrelease_result)".
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' kobj' with
      "[Hdeepown_i Hrelease_result]") as "HΦ".
    { iSplit; first done.
      iSplit.
      { iPureIntro. subst kobj_rv.
        destruct kobj, kobj'; simpl in *; done. }
      iSplit.
      { iPureIntro. subst kobj_rv kmeta_rv.
        rewrite objectmeta_update_objectmeta in Hmeta_updated.
        eapply objectmeta_updated_unset_resource_version_input.
        done. }
      iFrame. iFrame "%". }
    iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil))
      with false by
      (symmetry; apply bool_decide_false;
       exact conflict_error_nil).
    wp_auto.
    wp_for_post.
    iApply "HΦ".
  - iIntros (err) "Hconflict".
    iDestruct "Hconflict" as
      "(%Hconflict & Hown_meta_frag &
        Hown_spec_frag & Hown_children_frag)".
    pose proof (conflict_error_not_nil err Hconflict) as Herr_ne.
    iDestruct "Hclose" as "[Habort _]".
    iMod ("Habort" with
      "[Hown_meta_frag Hown_spec_frag Hown_children_frag]")
      as "Hau".
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

Lemma wp_State__updateTx_release γ l kind namespace i kobj
    key uid old_meta old_spec children parent_key parent_uid dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hold_parent" ∷ ⌜ meta_parent_ref old_meta = Some (parent_key, parent_uid) ⌝ ∗
      "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
      "%Howner_references_only" ∷
        ⌜ ObjectMetaV.equiv_except_resource_version
            (old_meta <| ObjectMetaV.OwnerReferences' :=
              (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
            (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj',
      RET (#(interface.ok i'), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "%Hparent_released" ∷ ⌜ obj_parent_ref kobj' = None ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ KObjectV.key kobj' = key ⌝ ∗
      "%Huid_eq'" ∷ ⌜ (KObjectV.objectmeta kobj').(ObjectMetaV.UID') = uid ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      ( "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply (wp_State__updateTx_release_au γ l kind namespace
    i kobj parent_key parent_uid dq).
  iFrame "#". iFrame "%". iFrame "Hdeepown_i".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert ((
    "Hown_meta_frag" ∷
      own_meta_frag γ key uid 1 old_meta ∗
    "Hown_spec_frag" ∷
      own_spec_frag γ key uid dq old_spec ∗
    "Hown_children_frag" ∷
      own_children_frag γ parent_key parent_uid 1 children ∗
    "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
    "%Huid_eq" ∷
      ⌜ uid =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
    "%Hold_parent" ∷
      ⌜ meta_parent_ref old_meta =
        Some (parent_key, parent_uid) ⌝ ∗
    "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
    "%Howner_references_only" ∷
      ⌜ ObjectMetaV.equiv_except_resource_version
          (old_meta <| ObjectMetaV.OwnerReferences' :=
            (KObjectV.objectmeta kobj).(
              ObjectMetaV.OwnerReferences') |>)
          (KObjectV.objectmeta kobj) ⌝ ∗
    "%Hspec_eq" ∷
      ⌜ KObjectV.spec kobj = old_spec ⌝
  )%I) with
    "[Hown_meta_frag Hown_spec_frag Hown_children_frag]"
    as "Hpre".
  { iFrame. iFrame "%". }
  iAaccIntro with "Hpre".
  - iIntros "Hpre". iNamed "Hpre". iFrame. done.
  - iIntros (i' kobj') "Hpost".
    iModIntro. iNext.
    iApply ("HΦ" $! i' kobj' with "Hpost").
Qed.

Lemma wp_State__PodUpdateTx_release γ l namespace pod_l pod
    key uid old_meta old_spec children parent_key parent_uid dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid pod ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_parent" ∷ ⌜ meta_parent_ref pod.(PodV.ObjectMeta') = None ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hold_parent" ∷ ⌜ meta_parent_ref old_meta = Some (parent_key, parent_uid) ⌝ ∗
      "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
      "%Howner_references_only" ∷
        ⌜ ObjectMetaV.equiv_except_resource_version
            (old_meta <| ObjectMetaV.OwnerReferences' :=
              pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences') |>)
            pod.(PodV.ObjectMeta') ⌝ ∗
      "%Hspec_eq" ∷ ⌜ pod.(PodV.Spec') = old_spec ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec old_spec) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodUpdateTx" #namespace #pod_l
  {{{ pod_l' pod',
      RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') ⌝ ∗
      "%Hspec_unchanged" ∷ ⌜ pod'.(PodV.Spec') = old_spec ⌝ ∗
      "%Hparent_released" ∷ ⌜ meta_parent_ref pod'.(PodV.ObjectMeta') = None ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ PodV.key pod' = key ⌝ ∗
      "%Huid_eq'" ∷ ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') = uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l' pod' 1 ∗
      "Hown_children_frag" ∷
        own_children_frag γ parent_key parent_uid 1
          (children ∖ {[key]}) ∗
      ( "Hown_meta_frag" ∷
          own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
        "Hown_spec_frag" ∷
          own_spec_frag γ key uid dq
            (ObjectSpecV.PodSpec old_spec)
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call.
  rewrite /apimodel.State__PodUpdateTxⁱᵐᵖˡ.
  wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.Pod) #pod_l)
      (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__updateTx_release γ l PodV.kind namespace
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) key uid old_meta
    (ObjectSpecV.PodSpec old_spec) children
    parent_key parent_uid dq
    with "[$Hinit $Hisk $Hdeepown_i $Hown_meta_frag
      $Hown_spec_frag $Hown_children_frag]").
  { iPureIntro.
    rewrite KObjectV.valid_eq_valid2 /=.
    split_and!; try done.
    f_equal. done. }
  iIntros (i' kobj') "Hpost".
  iDestruct "Hpost" as
    "(%Hvalid' & %Hsame_kind & %Hmeta_updated &
      %Hspec_unchanged & %Hparent_released &
      %Hkey_eq' & %Huid_eq' & Hdeepown_i &
      Hrelease_result)".
  destruct kobj' as [pod'|rs'|pvc'|sts']; try done.
  iDestruct "Hdeepown_i" as
    (pod_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. rewrite Hi'.
  change (go.PointerType api_core_v1.Pod)
    with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace
    (if decide
      (go.PointerType v1.Pod = go.PointerType v1.Pod)
     then #pod_l' else #null)%V
    with (#pod_l')%V by (rewrite decide_True; done).
  replace
    (bool_decide
      (go.PointerType v1.Pod = go.PointerType v1.Pod))
    with true by
      (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  assert (pod'.(PodV.Spec') = old_spec)
    as Hpod_spec_unchanged.
  { injection Hspec_unchanged. done. }
  iApply "HΦ". iFrame. iPureIntro.
  rewrite KObjectV.valid_eq_valid2 /= in Hvalid'.
  split_and!; done.
Qed.

End proof.
