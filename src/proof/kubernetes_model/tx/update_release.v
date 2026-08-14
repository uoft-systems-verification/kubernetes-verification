From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_release update_release_terminating.
From New.proof.kubernetes_model Require Import get get_observed.
From New.proof.kubernetes_model.tx Require Import common_update.
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
    "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
    "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
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
            (old_meta <| ObjectMetaV.OwnerReferences' := (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
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
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}),
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
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}),
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
  { pose proof Hvalid as Hvalid_copy.
    destruct Hvalid_copy as (_ & _ & Hmeta & _).
    unfold ObjectMetaV.valid_named_create in Hmeta. tauto. }
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
  assert (KObjectV.valid_named_create kind namespace kobj_rv)
    as Hvalid_create_rv.
  { subst kobj_rv kmeta_rv.
    rewrite /KObjectV.valid_named_create
      KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta
      objectmeta_update_objectmeta KObjectV.spec_update_objectmeta.
    destruct Hvalid as (Hkind & Htypemeta & Hmeta & Hspec).
    split_and!; done. }
  assert ((KObjectV.objectmeta kobj_rv).(ObjectMetaV.UID') ≠ ""%go)
    as Huid_nonempty_rv.
  { subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta /=.
    exact Huid_nonempty. }
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
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta /=. exact Hexisting_rv_valid. }
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
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
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
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
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
      "%Hvalid" ∷ ⌜ PodV.valid_named_create namespace pod ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
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
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
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
  assert (KObjectV.valid_named_create PodV.kind namespace
      (KObjectV.Pod pod)) as Hvalid_kobj.
  { rewrite /KObjectV.valid_named_create /=. split; done. }
  wp_apply (wp_State__updateTx_release γ l PodV.kind namespace
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) key uid old_meta
    (ObjectSpecV.PodSpec old_spec) children
    parent_key parent_uid dq
    with "[$Hinit $Hisk $Hdeepown_i $Hown_meta_frag
      $Hown_spec_frag $Hown_children_frag]").
  { iPureIntro.
    split_and!.
    - exact Hvalid_kobj.
    - exact Huid_nonempty.
    - done.
    - exact Hns_matches.
    - exact Hnew_parent.
    - exact Hkey_eq.
    - exact Huid_eq.
    - exact Hold_parent.
    - exact Hchild.
    - exact Howner_references_only.
    - change (ObjectSpecV.PodSpec pod.(PodV.Spec') =
        ObjectSpecV.PodSpec old_spec).
      f_equal. exact Hspec_eq. }
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

(** A terminating-object release deliberately carries no strong metadata or
    specification reference.  The observation rules out resurrection of the
    observed UID, but the object may already be absent and a stale request may
    fail update validation.  Accordingly this rule promises only invariant
    preservation and termination when the transaction returns. *)
Lemma wp_State__updateTx_release_terminating γ l kind namespace i kobj :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hterminating" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
  }}}
    l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i)
  {{{ (ret err : interface.t), RET (#ret, #err);
      (∃ i' kobj',
        ⌜ ret = interface.ok i' ∧ err = interface.nil ∧ KObjectV.same_kind kobj kobj' ⌝ ∗
        KObjectV.deepown_i i' kobj' 1) ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__updateTxⁱᵐᵖˡ. wp_call. wp_auto.
  iApply (wp_fupd _).
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1)%I.
  iAssert I with "[obj Hdeepown_i]" as "Hloop_inv".
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
  { iPureIntro. split; [done|]. right. done. }
  iIntros "Hdeepown_metadata". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_metadata]"). iIntros "Hdeepown_metadata". wp_auto.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go) as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _). unfold ObjectMetaV.valid_named_create in Hmeta. tauto. }
  rewrite bool_decide_false //. wp_auto.
  set key := {| KKey.Kind' := kind; KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
    KKey.Namespace' := namespace |}.
  assert (key = KObjectV.key kobj) as Hkey.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  wp_apply (wp_State__get_observed γ l key (KObjectV.objectmeta kobj).(ObjectMetaV.UID')).
  { rewrite Hkey. iFrame "#". }
  iIntros (existing_ret get_err) "Hget".
  iDestruct "Hget" as "[%Hnot_found | Hget]".
  { destruct Hnot_found as [-> Hnot_found].
    pose proof (not_found_error_not_nil _ Hnot_found) as Hget_err_ne.
    wp_auto.
    destruct get_err as [get_err_ok|]; [|done].
    wp_auto. wp_for_post.
    iApply ("HΦ" $! interface.nil (interface.ok get_err_ok)). iRight. done. }
  iDestruct "Hget" as (existing_i existing_kobj)
    "[(%Hret & %Hget_err & %Hvalid_existing & %Hkey_existing & %Hexisting_terminating) Hdeepown_existing_i]".
  subst existing_ret get_err. wp_auto.
  iDestruct "Hdeepown_existing_i" as (existing_l) "[%Hvalid_interface_existing Hdeepown_existing_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_existing_l") as
    "(%Hexisting_l_not_null & Htypemeta_existing & Hdeepown_existing_metadata & Hdeepown_existing_spec &
      Hdeepown_existing_status)".
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_existing_metadata]").
  iIntros "Hdeepown_existing_metadata". wp_auto.
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_metadata]"). iIntros "Hdeepown_metadata". wp_auto.
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := namespace |>) = KObjectV.objectmeta kobj)
    as Hnamespace_noop by (rewrite Hns_matches; destruct (KObjectV.objectmeta kobj); done).
  iEval (rewrite Hnamespace_noop) in "Hdeepown_metadata".
  set kmeta_rv := KObjectV.objectmeta kobj <| ObjectMetaV.ResourceVersion' :=
    ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>.
  set kobj_rv := KObjectV.update_objectmeta kobj kmeta_rv.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hkobj_l_not_null with
    "[$Htypemeta $Hdeepown_metadata $Hdeepown_spec $Hdeepown_status]") as "Hdeepown_l".
  iAssert (KObjectV.deepown_i i_copy kobj_rv 1) with "[Hdeepown_l]" as "Hdeepown_i_copy".
  { iExists kobj_l. iSplit.
    { iPureIntro. subst kobj_rv kmeta_rv. destruct kobj; done. }
    iFrame. }
  assert (valid_resource_version (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj)))
    as Hexisting_rv_valid by (destruct Hvalid_existing as (_ & Hrv & _); done).
  assert (KObjectV.valid_named_create kind namespace kobj_rv) as Hvalid_create_rv.
  { subst kobj_rv kmeta_rv. rewrite /KObjectV.valid_named_create
      KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta objectmeta_update_objectmeta
      KObjectV.spec_update_objectmeta.
    destruct Hvalid as (Hkind & Htypemeta & Hmeta & Hspec). split_and!; done. }
  assert (ObjectMetaV.UID' (KObjectV.objectmeta kobj_rv) ≠ ""%go) as Huid_nonempty_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta /=. exact Huid_nonempty. }
  assert (obj_parent_ref kobj_rv = None) as Hnew_parent_rv.
  { subst kobj_rv kmeta_rv. unfold obj_parent_ref. rewrite objectmeta_update_objectmeta. exact Hnew_parent. }
  assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj_rv) ≠ None) as Hterminating_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. exact Hterminating. }
  assert (KObjectV.key kobj_rv = KObjectV.key kobj) as Hkey_rv.
  { subst kobj_rv kmeta_rv. rewrite key_update_objectmeta_set_resource_version. done. }
  assert (ObjectMetaV.UID' (KObjectV.objectmeta kobj_rv) =
      ObjectMetaV.UID' (KObjectV.objectmeta kobj)) as Huid_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. done. }
  assert (valid_resource_version (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj_rv))) as Hrv_valid_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. exact Hexisting_rv_valid. }
  assert (kind = KObjectV.kind kobj_rv) as Hkind_matches_rv.
  { subst kobj_rv. rewrite KObjectV.kind_update_objectmeta. exact Hkind_matches. }
  assert (namespace = ObjectMetaV.Namespace' (KObjectV.objectmeta kobj_rv)) as Hns_matches_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. exact Hns_matches. }
  iAssert (own_deletion_observed_frag γ (KObjectV.key kobj_rv)
      (ObjectMetaV.UID' (KObjectV.objectmeta kobj_rv))) as "#Hown_deletion_observed_frag_rv".
  { rewrite Hkey_rv Huid_rv. iFrame "#". }
  wp_apply (wp_State__update_release_terminating γ l kind namespace i_copy kobj_rv with
    "[$Hinit $Hisk $Hdeepown_i_copy $Hown_deletion_observed_frag_rv]").
  { iPureIntro. split_and!; assumption. }
  iIntros (updated_ret update_err) "Hupdate".
  iDestruct "Hupdate" as "[Hsuccess | %Herror]".
  - iDestruct "Hsuccess" as (updated_i updated_kobj)
      "[(%Hupdated_ret & %Hupdate_nil & %Hsame_kind) Hdeepown_updated_i]".
    subst updated_ret update_err. wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact conflict_error_nil).
    wp_auto. wp_for_post. iApply ("HΦ" $! (interface.ok updated_i) interface.nil).
    iLeft. iExists updated_i, updated_kobj. iFrame. iPureIntro. split_and!; try done.
    subst kobj_rv. destruct kobj, updated_kobj; simpl in *; done.
  - destruct Herror as [Hconflict | [Hupdate_err_ne Hnot_conflict]].
    + pose proof (conflict_error_not_nil _ Hconflict) as Hupdate_err_ne.
      wp_auto. wp_apply (wp_IsConflict update_err with "[]").
      replace (bool_decide (conflict_error update_err)) with true by
        (symmetry; apply bool_decide_true; done).
      wp_auto. wp_for_post. iFrame "HΦ s kind namespace". iExists i_orig. iFrame.
    + wp_auto. wp_apply (wp_IsConflict update_err with "[]").
      replace (bool_decide (conflict_error update_err)) with false by
        (symmetry; apply bool_decide_false; done).
      wp_auto. wp_for_post. iApply ("HΦ" $! updated_ret update_err). iRight. done.
Qed.

Lemma wp_State__PodUpdateTx_release_terminating γ l namespace pod_l pod
    parent_key parent_uid phase :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid_named_create namespace pod ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hterminating" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      "%Hnew_parent" ∷ ⌜ meta_parent_ref pod.(PodV.ObjectMeta') = None ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase
  }}}
    l @! (go.PointerType apimodel.State) @! "PodUpdateTx" #namespace #pod_l
  {{{ (pod_l' : loc) (err : interface.t), RET (#pod_l', #err);
      own_terminating_children_frag γ parent_key parent_uid phase
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodUpdateTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.Pod) #pod_l) (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__updateTx_release_terminating γ l PodV.kind namespace
    (interface.mk (go.PointerType v1.Pod) #pod_l) (KObjectV.Pod pod) with
    "[$Hinit $Hisk $Hdeepown_i $Hown_deletion_observed_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (ret err) "[Hsuccess | %Herr]".
  2: { wp_auto. destruct err as [err_ok|]; [|done]. wp_auto.
    iApply ("HΦ" $! null (interface.ok err_ok)). iFrame. }
  iDestruct "Hsuccess" as (updated_i updated_kobj)
    "[(%Hret & %Herr_nil & %Hsame_kind) Hdeepown_updated_i]".
  subst ret err. wp_auto.
  iDestruct "Hdeepown_updated_i" as (updated_l) "[%Hvalid_updated Hdeepown_updated_l]".
  destruct updated_kobj as [updated_pod| | |]; try done.
  unfold KObjectV.valid_interface in Hvalid_updated. rewrite Hvalid_updated.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod). cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod) then #updated_l else #null)%V
    with (#updated_l)%V by (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto. iApply ("HΦ" $! updated_l interface.nil). iFrame.
Qed.

End proof.
