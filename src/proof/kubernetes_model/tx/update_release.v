From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_release update_release_terminating.
From New.proof.kubernetes_model Require Import common_update get get_observed.
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
    "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_spec children,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') dq old_spec ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hchild" ∷ ⌜ KObjectV.key kobj ∈ children ⌝ ∗
      "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[KObjectV.key kobj]}),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)". iNamed "H".
  destruct (Classical_Prop.classic (
      KObjectV.valid_create kind namespace kobj ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ∧
      valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ∧
      valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
      namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')))
    as [Hvalid_update_input|Hinvalid_update_input].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (old_meta old_spec children) "[Hau_pre Hclose]".
    iNamed "Hau_pre".
    exfalso. apply Hinvalid_update_input.
    revert Hvalid_update.
    destruct old_spec, kobj; rewrite /KObjectV.valid_update /=;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        /KObjectV.valid_create /=;
      try contradiction; tauto.
  }
  destruct Hvalid_update_input as
    (Hvalid & Hname_nonempty & Hvalid_typemeta & Huid_nonempty & Hrv_valid &
      Hns_matches).
  assert (kind = KObjectV.kind kobj) as Hkind_matches.
  { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create in Hvalid;
      tauto. }
  wp_method_call. rewrite /apimodel.State__updateTxⁱᵐᵖˡ.
  wp_call. wp_auto.
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_spec children,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') dq old_spec ∗
      "Hown_children_frag" ∷
        own_children_frag γ parent_key parent_uid 1 children ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hchild" ∷ ⌜ KObjectV.key kobj ∈ children ⌝ ∗
      "%Hspec_eq" ∷
        ⌜ KObjectV.spec kobj = old_spec ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "%Hspec_unchanged" ∷
        ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷
        own_children_frag γ parent_key parent_uid 1 (children ∖ {[KObjectV.key kobj]}),
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
  iMod "Hau" as (old_meta old_spec children) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  rewrite Hkey_new.
  iExists (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), (DfracOwn 1),
    old_meta, None, None.
  iFrame "Hown_meta_frag".
  iSplit; first done.
  iSplit; first done.
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as
    "(%Hvalid_existing & %Hextra_valid_existing & %Hkey_existing & %Hmeta_eq &
      Hdeepown_existing_i & Hown_meta_frag & _ & _)".
  iMod ("Habort" with
    "[Hown_meta_frag Hown_spec_frag Hown_children_frag]")
    as "Hau".
  { iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  clear old_meta old_spec children Hvalid_update Hchild Hspec_eq Hmeta_eq.
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
  { destruct Hvalid_existing as (_ & Hrv_existing & _).
    done. }
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
  iMod "Hau" as (old_meta old_spec children) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  iExists (KObjectV.key kobj),
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), old_meta, old_spec, children.
  iFrame "Hown_meta_frag Hown_spec_frag Hown_children_frag".
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    assert (KObjectV.valid_create kind namespace kobj ∧
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ∧
        valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ∧
        valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
        namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
        ObjectMetaV.valid_update old_meta (KObjectV.objectmeta kobj) ∧
        ObjectSpecV.valid_update old_spec (KObjectV.spec kobj)) as
      (Hcreate & Hname & Htypemeta & Huid & _ & Hnamespace & Hmeta & Hspec).
    { revert Hvalid_update.
      destruct old_spec, kobj; rewrite /KObjectV.valid_update /=;
        rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
          ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
          ?/PodV.valid_create ?/ReplicaSetV.valid_create
          ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
          /KObjectV.valid_create /=;
        try contradiction; tauto. }
    assert (KObjectV.valid_create kind namespace
        (KObjectV.update_objectmeta kobj
          ((KObjectV.objectmeta kobj) <| ObjectMetaV.ResourceVersion' :=
            ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>))) as Hcreate_rv.
    { revert Hcreate.
      destruct kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]]; simpl;
        rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
          ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create;
        intros (Hkind & Hns_nonempty & Hns_valid & Htypemeta_create & Hmeta_create & Hspec_create);
        split_and!; try done; destruct meta; done. }
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
    destruct old_spec, kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]]; destruct meta; simpl in *;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        /KObjectV.valid_create /= in Hcreate_rv |- *;
      try contradiction; tauto. }
  iSplit.
  { iPureIntro. exact Hchild. }
  iSplit.
  { iPureIntro. subst kobj_rv.
    rewrite KObjectV.spec_update_objectmeta. exact Hspec_eq. }
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as
      "(%Hvalid' & %Hupdated & %Hspec_unchanged & Hdeepown_i & Hrelease_result)".
    assert (KObjectV.updated kobj kobj') as Hupdated_original.
    { subst kobj_rv kmeta_rv.
      revert Hupdated.
      destruct kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hspec); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence. }
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' kobj' with
      "[Hdeepown_i Hrelease_result]") as "HΦ".
    { iSplit; first done.
      iSplit; first (iPureIntro; exact Hupdated_original).
      iSplit; first done.
      iFrame. }
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
    old_meta old_spec children parent_key parent_uid dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hchild" ∷ ⌜ KObjectV.key kobj ∈ children ⌝ ∗
      "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') dq old_spec ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj', RET (#(interface.ok i'), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[KObjectV.key kobj]})
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply (wp_State__updateTx_release_au γ l kind namespace
    i kobj parent_key parent_uid dq).
  iFrame "#". iFrame "%". iFrame "Hdeepown_i".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert ((
    "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
    "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') dq old_spec ∗
    "Hown_children_frag" ∷
      own_children_frag γ parent_key parent_uid 1 children ∗
    "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
    "%Hchild" ∷ ⌜ KObjectV.key kobj ∈ children ⌝ ∗
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
    iApply ("HΦ" $! i' kobj').
    iExact "Hpost".
Qed.

Lemma wp_State__PodUpdateTx_release γ l namespace pod_l pod
    key uid old_meta old_spec children parent_key parent_uid dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hnew_parent" ∷ ⌜ meta_parent_ref pod.(PodV.ObjectMeta') = None ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update PodV.kind namespace old_meta (ObjectSpecV.PodSpec old_spec) (KObjectV.Pod pod) ⌝ ∗
      "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hspec_eq" ∷ ⌜ pod.(PodV.Spec') = old_spec ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec old_spec) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodUpdateTx" #namespace #pod_l
  {{{ pod_l' pod', RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hupdated" ∷ ⌜ PodV.updated pod pod' ⌝ ∗
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
  assert (KObjectV.key (KObjectV.Pod pod) = key) as Hkobj_key.
  { rewrite Hkey_eq. done. }
  assert ((KObjectV.objectmeta (KObjectV.Pod pod)).(ObjectMetaV.UID') = uid)
    as Hkobj_uid.
  { simpl. symmetry. exact Huid_eq. }
  iEval (rewrite Hkey_eq Huid_eq) in "Hown_meta_frag Hown_spec_frag".
  wp_apply (wp_State__updateTx_release γ l PodV.kind namespace
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) old_meta (ObjectSpecV.PodSpec old_spec) children
    parent_key parent_uid dq
    with "[$Hinit $Hisk $Hdeepown_i $Hown_meta_frag
      $Hown_spec_frag $Hown_children_frag]").
  { iPureIntro.
    split_and!.
    - exact Hnew_parent.
    - exact Hvalid_update.
    - rewrite Hkobj_key. exact Hchild.
    - change (ObjectSpecV.PodSpec pod.(PodV.Spec') =
        ObjectSpecV.PodSpec old_spec).
      f_equal. exact Hspec_eq. }
  iIntros (i' kobj') "Hpost".
  iDestruct "Hpost" as
    "(%Hvalid' & %Hupdated & %Hspec_unchanged & Hdeepown_i & Hrelease_result)".
  assert ((KObjectV.objectmeta kobj').(ObjectMetaV.Name') = pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta kobj').(ObjectMetaV.Namespace') =
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta kobj').(ObjectMetaV.UID') = pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
    as (Hname_updated & Hnamespace_updated & Huid_updated).
  { destruct kobj'; rewrite /KObjectV.updated /PodV.updated /= in Hupdated |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hupdated; tauto. }
  pose proof (kobject_updated_parent_ref _ _ Hupdated) as Hparent_updated.
  destruct kobj' as [pod'|rs'|pvc'|sts']; simpl in Hupdated; try done.
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
  assert (meta_parent_ref pod'.(PodV.ObjectMeta') = None) as Hparent_released.
  { unfold obj_parent_ref in Hparent_updated. simpl in Hparent_updated.
    rewrite Hparent_updated. exact Hnew_parent. }
  assert (PodV.key pod' = key) as Hkey_eq'.
  { rewrite Hkey_eq /PodV.key /PodV.meta_key.
    simpl in Hname_updated, Hnamespace_updated.
    rewrite Hname_updated Hnamespace_updated. done. }
  assert (pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') = uid) as Huid_eq'.
  { rewrite Huid_eq. simpl in Huid_updated. exact Huid_updated. }
  iEval (rewrite Hkobj_key) in "Hrelease_result".
  iApply "HΦ". iSplit.
  { iPureIntro. rewrite KObjectV.valid_eq_valid2 /= in Hvalid'. done. }
  iFrame. iFrame "%".
Qed.

(** A terminating-object release deliberately carries no strong metadata or
    specification reference.  The observation rules out resurrection of the
    observed UID, but the object may already be absent and a stale request may
    fail update validation.  Accordingly this rule promises only invariant
    preservation and termination when the transaction returns. *)
Lemma wp_State__updateTx_release_terminating γ l kind namespace i kobj :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hvalid_typemeta" ∷ ⌜ valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hterminating" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
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
  { exact Hname_nonempty. }
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
    "[(%Hret & %Hget_err & %Hvalid_existing & %Hextra_valid_existing &
      %Hkey_existing & %Hexisting_terminating) Hdeepown_existing_i]".
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
  assert (KObjectV.valid_create kind namespace kobj_rv) as Hvalid_create_rv.
  { subst kobj_rv kmeta_rv.
    revert Hvalid.
    destruct kobj as [[tm meta spec status]|[tm meta spec status]|
      [tm meta spec status]|[tm meta spec status]]; simpl;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create;
      intros (Hkind & Hns_nonempty & Hns_valid & Htypemeta_create & Hmeta_create & Hspec_create);
      split_and!; try done; destruct meta; done. }
  assert ((KObjectV.objectmeta kobj_rv).(ObjectMetaV.Name') ≠ ""%go) as Hname_nonempty_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. exact Hname_nonempty. }
  assert (valid_typemeta (KObjectV.kind kobj_rv) (KObjectV.typemeta kobj_rv))
    as Hvalid_typemeta_rv.
  { subst kobj_rv.
    rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
    exact Hvalid_typemeta. }
  assert (ObjectMetaV.UID' (KObjectV.objectmeta kobj_rv) ≠ ""%go) as Huid_nonempty_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta /=. exact Huid_nonempty. }
  assert (obj_parent_ref kobj_rv = None) as Hnew_parent_rv.
  { subst kobj_rv kmeta_rv. unfold obj_parent_ref. rewrite objectmeta_update_objectmeta. exact Hnew_parent. }
  assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj_rv) ≠ None) as Hterminating_rv.
  { subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta. exact Hterminating. }
  assert (KObjectV.key kobj_rv = KObjectV.key kobj) as Hkey_rv.
  { subst kobj_rv kmeta_rv.
    rewrite /KObjectV.key KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
    destruct (KObjectV.objectmeta kobj); done. }
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
  - destruct (Classical_Prop.classic (conflict_error update_err)) as
      [Hconflict|Hnot_conflict].
    + pose proof (conflict_error_not_nil _ Hconflict) as Hupdate_err_ne.
      wp_auto. wp_apply (wp_IsConflict update_err with "[]").
      replace (bool_decide (conflict_error update_err)) with true by
        (symmetry; apply bool_decide_true; done).
      wp_auto. wp_for_post. iFrame "HΦ s kind namespace". iExists i_orig. iFrame.
    + pose proof Herror as Hupdate_err_ne.
      wp_auto. wp_apply (wp_IsConflict update_err with "[]").
      replace (bool_decide (conflict_error update_err)) with false by
        (symmetry; apply bool_decide_false; done).
      wp_auto. wp_for_post. iApply ("HΦ" $! updated_ret update_err). iRight. done.
Qed.

Lemma wp_State__PodUpdateTx_release_terminating γ l namespace pod_l pod :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid_create PodV.kind namespace pod ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hvalid_typemeta" ∷ ⌜ valid_typemeta PodV.kind pod.(PodV.TypeMeta') ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hterminating" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      "%Hnew_parent" ∷ ⌜ meta_parent_ref pod.(PodV.ObjectMeta') = None ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
  }}}
    l @! (go.PointerType apimodel.State) @! "PodUpdateTx" #namespace #pod_l
  {{{ (pod_l' : loc) (err : interface.t), RET (#pod_l', #err);
      (∃ pod', ⌜ err = interface.nil ⌝ ∗ PodV.deepown_l pod_l' pod' 1) ∨
      ⌜ err ≠ interface.nil ⌝
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
    iApply ("HΦ" $! null (interface.ok err_ok)). iRight. done. }
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
  wp_auto. iApply ("HΦ" $! updated_l interface.nil). iLeft.
  iExists updated_pod. iSplit; first done. iFrame.
Qed.

End proof.
