From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update.
From New.proof.kubernetes_model Require Import common_update get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

Lemma wp_State__updateTx_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_spec,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_spec ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.spec kobj'),
      COMM ▷ Φ (#(interface.ok i'), #interface.nil)%V
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)".
  iNamed "H".
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
    iMod "Hau" as (old_meta old_spec) "[Hau_pre Hclose]".
    iNamed "Hau_pre".
    exfalso. apply Hinvalid_update_input.
    revert Hvalid_update.
    destruct old_spec, kobj; rewrite /KObjectV.valid_update /=;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/DeploymentV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        ?/DeploymentV.valid_create
        /KObjectV.valid_create /=;
      try contradiction; tauto.
  }
  destruct Hvalid_update_input as
    (Hvalid & Hname_nonempty & Hvalid_typemeta & Huid_nonempty & Hrv_valid &
      Hns_matches).
  assert (kind = KObjectV.kind kobj) as Hkind_matches.
  { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        ?/DeploymentV.valid_create in Hvalid;
      tauto. }
  wp_method_call. rewrite /apimodel.State__updateTxⁱᵐᵖˡ. wp_call. wp_auto.
  set I := (∃ i_orig,
    "Hobj_ptr" ∷ obj_ptr ↦ interface.ok i_orig ∗
    "Hdeepown_i_orig" ∷ KObjectV.deepown_i i_orig kobj 1 ∗
    "Hau" ∷ AU <{ ∃∃ old_meta old_spec,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_spec ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hvalid_simple_update" ∷
        ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
    }> @ ⊤, ∅ <{ ∀∀ i' kobj',
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.spec kobj'),
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
  iMod "Hau" as (old_meta old_spec) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  rewrite Hkey_new.
  iExists (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), (DfracOwn 1),
    old_meta, (Some old_spec), None.
  iFrame "Hown_meta_frag Hown_spec_frag".
  iSplit; first done.
  iIntros (existing_i existing_kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_existing & %Hextra_valid_existing &
    %Hkey_existing & %Hmeta_eq &
    Hdeepown_existing_i & Hown_meta_frag & (Hown_spec_frag & %Hspec_eq) & _)".
  iMod ("Habort" with "[Hown_meta_frag Hown_spec_frag]") as "Hau".
  { iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  clear old_meta old_spec Hvalid_update Hvalid_simple_update Hmeta_eq Hspec_eq.
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
  wp_apply (wp_State__update_au γ l kind namespace i_copy kobj_rv).
  iFrame "#".
  iFrame "Hdeepown_i_copy".
  iMod "Hau" as (old_meta old_spec) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iModIntro.
  iExists (KObjectV.key kobj),
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID'), old_meta, old_spec.
  iFrame "Hown_meta_frag Hown_spec_frag".
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
          ?/DeploymentV.valid_update
          ?/PodV.valid_create ?/ReplicaSetV.valid_create
          ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
          ?/DeploymentV.valid_create
          /KObjectV.valid_create /=;
        try contradiction; tauto. }
    assert (KObjectV.valid_create kind namespace
        (KObjectV.update_objectmeta kobj
          ((KObjectV.objectmeta kobj) <| ObjectMetaV.ResourceVersion' :=
            ObjectMetaV.ResourceVersion' (KObjectV.objectmeta existing_kobj) |>))) as Hcreate_rv.
    { revert Hcreate.
      destruct kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]]; simpl;
        rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
          ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
          ?/DeploymentV.valid_create;
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
        [tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]]; destruct meta; simpl in *;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/DeploymentV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        ?/DeploymentV.valid_create
        /KObjectV.valid_create /= in Hcreate_rv |- *;
      try contradiction; tauto. }
  iSplit.
  { iPureIntro. subst kobj_rv kmeta_rv.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.valid_simple_update in Hvalid_simple_update |- *.
    destruct old_meta, (KObjectV.objectmeta kobj); simpl in *; intuition congruence. }
  iSplit.
  - iIntros (i' kobj') "Hsuccess".
    iDestruct "Hsuccess" as
      "(%Hvalid' & %Hupdated &
        Hdeepown_i & Hown_meta_frag & Hown_spec_frag)".
    assert (KObjectV.updated kobj kobj') as Hupdated_original.
    { subst kobj_rv kmeta_rv.
      revert Hupdated.
      destruct kobj, kobj'; simpl; try done;
        intros (Htypemeta & Hmeta & Hspec); split_and!; try done.
      all: rewrite /ObjectMetaV.updated in Hmeta |- *;
        destruct ObjectMeta', ObjectMeta'0; simpl in *; intuition congruence. }
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! i' kobj' with
      "[Hdeepown_i Hown_meta_frag Hown_spec_frag]") as "HΦ".
    { iSplit.
      { iPureIntro. exact Hvalid'. }
      iSplit.
      { iPureIntro. exact Hupdated_original. }
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
      Hown_meta_frag & Hown_spec_frag)".
    pose proof (conflict_error_not_nil err Hconflict) as Herr_ne.
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

Lemma wp_State__updateTx γ l kind namespace i kobj old_meta old_spec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_spec
  }}}
    l @! (go.PointerType apimodel.State) @! "updateTx" #kind #namespace #(interface.ok i)
  {{{ i' kobj', RET (#(interface.ok i'), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 (KObjectV.spec kobj')
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ".
  iNamed "H".
  iApply wp_State__updateTx_au.
  iFrame "#".
  iFrame "Hdeepown_i".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert ((
    "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_meta ∗
    "Hown_spec_frag" ∷ own_spec_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') 1 old_spec ∗
    "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
    "%Hvalid_simple_update" ∷
      ⌜ ObjectMetaV.valid_simple_update old_meta (KObjectV.objectmeta kobj) ⌝
  )%I) with "[Hown_meta_frag Hown_spec_frag]" as "Hpre".
  { iFrame. iFrame "%". }
  iAaccIntro with "Hpre".
  - iIntros "Hpre".
    iNamed "Hpre".
    iFrame. done.
  - iIntros (i' kobj') "Hpost".
    iModIntro. iNext.
    iApply ("HΦ" $! i' kobj').
    iExact "Hpost".
Qed.

Lemma wp_State__PodUpdateTx γ l namespace pod_l pod key uid kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_update" ∷ ⌜ KObjectV.valid_update PodV.kind namespace kmeta kspec (KObjectV.Pod pod) ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta pod.(PodV.ObjectMeta') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec
  }}}
    l @! (go.PointerType apimodel.State) @!
      "PodUpdateTx" #namespace #pod_l
  {{{ pod_l' pod', RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hupdated" ∷ ⌜ PodV.updated pod pod' ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ PodV.key pod' = key ⌝ ∗
      "%Huid_eq'" ∷ ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') = uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l' pod' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec'))
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodUpdateTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.Pod) #pod_l)
      (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_Pod|]. iFrame. }
  iEval (rewrite Hkey_eq Huid_eq) in "Hown_meta_frag Hown_spec_frag".
  wp_apply (wp_State__updateTx γ l PodV.kind namespace
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) kmeta kspec
    with "[$Hinit $Hisk $Hdeepown_i $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro. split; done. }
  iIntros (i' kobj') "Hpost".
  iDestruct "Hpost" as
    "(%Hvalid' & %Hupdated & Hdeepown_i & Hown_meta_frag & Hown_spec_frag)".
  assert ((KObjectV.objectmeta kobj').(ObjectMetaV.Name') = pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta kobj').(ObjectMetaV.Namespace') =
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta kobj').(ObjectMetaV.UID') = pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
    as (Hname_updated & Hnamespace_updated & Huid_updated).
  { destruct kobj'; rewrite /KObjectV.updated /PodV.updated /= in Hupdated |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hupdated; tauto. }
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; simpl in Hupdated; try done.
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace
    (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
     then #pod_l' else #null)%V
    with (#pod_l')%V by (rewrite decide_True; done).
  replace
    (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  assert (PodV.key pod' = key) as Hkey_eq'.
  { rewrite Hkey_eq /PodV.key /PodV.meta_key.
    simpl in Hname_updated, Hnamespace_updated.
    rewrite Hname_updated Hnamespace_updated. done. }
  assert (pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') = uid)
    as Huid_eq'.
  { rewrite Huid_eq. simpl in Huid_updated. exact Huid_updated. }
  iApply "HΦ". iSplit.
  { iPureIntro. rewrite KObjectV.valid_eq_valid2 /= in Hvalid'. done. }
  assert (KObjectV.key (KObjectV.Pod pod) = key) as Hkobj_key.
  { rewrite Hkey_eq. done. }
  assert ((KObjectV.objectmeta (KObjectV.Pod pod)).(ObjectMetaV.UID') = uid)
    as Hkobj_uid.
  { simpl. symmetry. exact Huid_eq. }
  iEval (rewrite Hkobj_key Hkobj_uid) in "Hown_meta_frag Hown_spec_frag".
  iFrame. iFrame "%".
Qed.

Lemma wp_State__ReplicaSetUpdateTx γ l namespace rs_l rs key uid kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid_named_create namespace rs ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ReplicaSetV.key rs ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec
  }}}
    l @! (go.PointerType apimodel.State) @!
      "ReplicaSetUpdateTx" #namespace #rs_l
  {{{ rs_l' rs', RET (#rs_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ ReplicaSetV.valid rs' ⌝ ∗
      "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated rs.(ReplicaSetV.ObjectMeta') rs'.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hspec_updated" ∷
        ⌜ ObjectSpecV.updated (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ ReplicaSetV.key rs' = key ⌝ ∗
      "%Huid_eq'" ∷ ⌜ rs'.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') = uid ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l' rs' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec'))
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetUpdateTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
      (KObjectV.ReplicaSet rs) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists rs_l. iSplit; [done|]. iFrame. }
  assert (KObjectV.valid_named_create ReplicaSetV.kind namespace
      (KObjectV.ReplicaSet rs)) as Hvalid_kobj.
  { rewrite /KObjectV.valid_named_create /=. split; done. }
  wp_apply (wp_State__updateTx γ l ReplicaSetV.kind namespace
    (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
    (KObjectV.ReplicaSet rs) key uid kmeta kspec
    with "[$Hinit $Hisk $Hdeepown_i $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro.
    split_and!; done. }
  iIntros (i' kobj') "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
  iDestruct "Hdeepown_i" as (rs_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  cbn [interface.ty interface.v].
  replace
    (if decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)
     then #rs_l' else #null)%V
    with (#rs_l')%V by (rewrite decide_True; done).
  replace
    (bool_decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  assert (ReplicaSetV.key rs' = key) as Hkey_eq'.
  { rewrite Hkey_eq /ReplicaSetV.key /ReplicaSetV.meta_key.
    destruct Hmeta_updated as
      (Hname & _ & Hnamespace & _).
    rewrite Hname Hnamespace. done. }
  assert (rs'.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') = uid)
    as Huid_eq'.
  { rewrite Huid_eq.
    destruct Hmeta_updated as
      (_ & _ & _ & _ & Huid & _).
    exact Huid. }
  iApply "HΦ". iFrame. iPureIntro.
  rewrite KObjectV.valid_eq_valid2 /= in Hvalid'.
  split_and!; done.
Qed.

End proof.
