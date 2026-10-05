From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status.
From New.proof.kubernetes_model Require Import common_update get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
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
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid_updated" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hstatus_updated" ∷ ⌜ KObjectV.status_updated kobj kobj' ⌝ ∗
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
        ?/DeploymentV.valid_status_update
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
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid_updated" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hstatus_updated" ∷ ⌜ KObjectV.status_updated kobj kobj' ⌝ ∗
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
  wp_apply (wp_deepCopy i_orig kobj (DfracOwn 1) with "[Hdeepown_i_orig]").
  { iFrame "#". iExact "Hdeepown_i_orig". }
  iIntros (i_copy) "[Hdeepown_i_copy Hdeepown_i_orig]". wp_auto.
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
  wp_apply (wp_State__get_some_au γ l key).
  iFrame "#".
  iMod "Hau" as (old_meta old_status) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  rewrite Hkey_new.
  iExists (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), (DfracOwn 1), (DfracOwn 1),
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
  wp_apply (wp_State__update_status_au γ l kind namespace i_copy kobj_rv (DfracOwn 1)).
  iFrame "#".
  iFrame "Hdeepown_i_copy".
  iMod "Hau" as (old_meta old_status) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  assert (KObjectV.valid_status_update kind namespace old_meta old_status kobj_rv)
    as Hvalid_status_update_rv.
  { subst kobj_rv kmeta_rv.
    assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta kobj)) as Hmeta.
    { destruct old_status, kobj;
        rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
        rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
          ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
          ?/DeploymentV.valid_status_update
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
        ?/DeploymentV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update |- *;
      simpl in Hmeta_rv |- *; try contradiction; tauto. }
  iExists (KObjectV.key kobj),
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), (DfracOwn 1), old_meta, None, old_status.
  iFrame "Hown_meta_frag Hown_status_frag".
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv. destruct kobj; done. }
  iSplit.
  { iPureIntro. eapply valid_status_update_request_ok. exact Hvalid_status_update_rv. }
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.valid_simple_update in Hvalid_simple_update |- *.
    destruct old_meta, (KObjectV.objectmeta kobj); simpl in *; intuition congruence. }
  iSplit; first (iPureIntro; by left).
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as "(%Hvalid_updated & %Hstatus_updated_if_valid & _ & Hdeepown_i &
      _ & Hown_meta_frag & _ & Hown_status_frag)".
    pose proof (Hstatus_updated_if_valid Hvalid_status_update_rv) as Hstatus_updated.
    assert (KObjectV.status_updated kobj kobj') as Hstatus_updated_original.
    { subst kobj_rv kmeta_rv.
      revert Hstatus_updated.
      destruct kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hstatus); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence. }
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' kobj' with
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
    iDestruct "Hconflict" as "(%Herr_ne & %Hconflict_if_valid & _ &
      Hown_meta_frag & _ & Hown_status_frag)".
    pose proof (Hconflict_if_valid Hvalid_status_update_rv) as Hconflict.
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

(* A transactional status write for a caller that owns the status fragment and
   holds shares of the metadata and, optionally, spec fragments, as the
   ReplicaSet controller does. Each attempt writes at the currently stored
   resource version and conflicts are retried, so the write fails only if the
   request itself is invalid. The input is only read, at fraction [dq_in]. *)
Lemma wp_State__updateStatusTx_shared γ l kind namespace i kobj dq_in
    uid dq kmeta kspec_o kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hrequest_ok" ∷ ⌜ status_update_request_ok kind namespace kobj ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hmeta_frac" ∷ ⌜ dq = DfracOwn 1 ∨
        ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj dq_in ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
      "Hown_spec_frag" ∷ match kspec_o with
      | Some kspec => own_spec_frag γ (KObjectV.key kobj) uid dq kspec
      | None => True
      end ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatusTx" #kind #namespace #(interface.ok i)
  {{{ (ret : val), RET ret;
      KObjectV.deepown_i i kobj dq_in ∗
      ((∃ i' kobj',
        ⌜ ret = (#(interface.ok i'), #interface.nil)%V ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
          KObjectV.status_updated kobj kobj' ⌝ ∗
        ⌜ KObjectV.same_kind kobj kobj' ∧
          KObjectV.typemeta kobj' = KObjectV.typemeta kobj ∧
          ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj') (KObjectV.objectmeta kobj) ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ (KObjectV.key kobj) uid dq (KObjectV.objectmeta kobj') ∗
        match kspec_o with
        | Some kspec => own_spec_frag γ (KObjectV.key kobj) uid dq kspec ∗ ⌜ KObjectV.spec kobj' = kspec ⌝
        | None => True
        end ∗
        own_status_frag γ (KObjectV.key kobj) uid 1 (KObjectV.status kobj')) ∨
       (∃ err,
        ⌜ ret = (#interface.nil, #err)%V ⌝ ∗
        ⌜ err ≠ interface.nil ∧ ¬ KObjectV.valid_status_update kind namespace kmeta kstatus kobj ⌝ ∗
        own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
        match kspec_o with
        | Some kspec => own_spec_frag γ (KObjectV.key kobj) uid dq kspec
        | None => True
        end ∗
        own_status_frag γ (KObjectV.key kobj) uid 1 kstatus))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  pose proof Hrequest_ok as (Hkind_matches & Hname_not_empty & Huid_nonempty & Hns_matches & Hrv_valid &
    Hvalid_typemeta & Hlabels & Hannotations & Howners & Hfinalizers & Hmanaged_fields).
  wp_auto.
  (* A conflict leaves every fragment as it was, so the loop just keeps them. *)
  set I := (
    "obj" ∷ obj_ptr ↦ interface.ok i ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj dq_in ∗
    "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
    "Hown_spec_frag" ∷ match kspec_o with
    | Some kspec => own_spec_frag γ (KObjectV.key kobj) uid dq kspec
    | None => True
    end ∗
    "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus)%I.
  iAssert I with "[obj Hdeepown_i Hown_meta_frag Hown_spec_frag Hown_status_frag]" as "Hloop_inv".
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
  wp_apply (wp_State__get_some γ l (KObjectV.key kobj) uid dq (DfracOwn 1) kmeta kspec_o (Some kstatus)
    with "[$Hown_meta_frag $Hown_spec_frag $Hown_status_frag]").
  { iFrame "#". }
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_existing & %Hextra_valid_existing & %Hkey_existing & %Hmeta_eq &
    Hdeepown_existing_i & Hown_meta_frag & Hspec_get & Hown_status_frag & %Hstatus_eq)".
  iAssert (match kspec_o with
    | Some kspec => own_spec_frag γ (KObjectV.key kobj) uid dq kspec
    | None => True
    end)%I with "[Hspec_get]" as "Hown_spec_frag".
  { destruct kspec_o; [iDestruct "Hspec_get" as "[$ _]"|done]. }
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
  (* A valid request stays valid at the stored resource version. *)
  assert (KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
    KObjectV.valid_status_update kind namespace kmeta kstatus kobj_rv) as Hvalid_rv.
  { intros Hvalid_status_update. subst kobj_rv kmeta_rv.
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
  wp_apply (wp_State__update_status_au γ l kind namespace i_copy kobj_rv (DfracOwn 1)).
  iFrame "#". iFrame "Hdeepown_i_copy".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists (KObjectV.key kobj), uid, dq, kmeta, kspec_o, kstatus.
  assert (KObjectV.key kobj_rv = KObjectV.key kobj) as Hkey_rv.
  { subst kobj_rv kmeta_rv. destruct kobj; done. }
  rewrite Hkey_rv.
  iFrame "Hown_meta_frag Hown_spec_frag Hown_status_frag".
  iSplit; first done.
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite /status_update_request_ok in Hrequest_ok |- *.
    destruct kobj; simpl in *; intuition. }
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.valid_simple_update in Hvalid_simple_update |- *.
    destruct kmeta, (KObjectV.objectmeta kobj); simpl in *; intuition congruence. }
  iSplit.
  { iPureIntro. destruct Hmeta_frac as [->|Hequiv]; [by left|right].
    subst kobj_rv kmeta_rv. rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version
      in Hequiv |- *.
    rewrite -Hequiv. destruct (KObjectV.objectmeta kobj); done. }
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as "(%Hvalid_updated & %Hstatus_updated_if_valid & %Hpreserved & Hdeepown_i' &
      _ & Hown_meta_frag & Hown_spec_frag & Hown_status_frag)".
    iMod "Hmask" as "_". iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact conflict_error_nil).
    wp_auto.
    wp_for_post.
    iApply "HΦ". iFrame "Hdeepown_i". iLeft.
    iExists i', kobj'. iFrame. iPureIntro. split_and!; try done.
    + intros Hvalid_status_update.
      pose proof (Hstatus_updated_if_valid (Hvalid_rv Hvalid_status_update)) as Hstatus_updated.
      subst kobj_rv kmeta_rv.
      revert Hstatus_updated.
      destruct kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hstatus); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence.
    + subst kobj_rv kmeta_rv. destruct Hpreserved as (Hsame & _ & _).
      destruct kobj, kobj'; done.
    + subst kobj_rv kmeta_rv. destruct Hpreserved as (_ & Htm & _).
      destruct kobj; done.
    + subst kobj_rv kmeta_rv. destruct Hpreserved as (_ & _ & Hequiv).
      rewrite objectmeta_update_objectmeta in Hequiv.
      rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version
        in Hequiv |- *.
      rewrite Hequiv. destruct (KObjectV.objectmeta kobj); done.
  - iIntros (err) "(%Herr_ne & %Hconflict_if_valid & _ & Hown_meta_frag & Hown_spec_frag & Hown_status_frag)".
    iMod "Hmask" as "_". iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict err with "[]").
    destruct (decide (conflict_error err)) as [Hconflict|Hnot_conflict].
    + (* Another writer advanced the resource version: retry. *)
      replace (bool_decide (conflict_error err)) with true by
        (symmetry; apply bool_decide_true; done).
      wp_auto.
      wp_for_post.
      iFrame.
    + (* Any other error means the request itself is invalid. *)
      replace (bool_decide (conflict_error err)) with false by
        (symmetry; apply bool_decide_false; done).
      wp_auto.
      wp_for_post.
      iApply "HΦ". iFrame "Hdeepown_i". iRight.
      iExists err. iFrame. iPureIntro. split; first done. split; first done.
      intros Hvalid_status_update.
      apply Hnot_conflict, Hconflict_if_valid, Hvalid_rv, Hvalid_status_update.
Qed.

End proof.
