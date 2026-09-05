From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.
From New.proof.kubernetes_model Require Import common_delete.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* Atomic update contract for releasing an object from its controller parent.
   The request changes only metadata: its spec is exactly the value currently
   stored. Ordinary update preserves status, so status ownership can remain
   framed around this contract. The parent relation and [own_children_frag]
   are updated atomically with the object. *)
Lemma wp_State__update_release_au γ l kind namespace i kobj parent_key parent_uid dq :
  ∀ Φ,
  is_pkg_init apimodel ∗
  is_kubernetes γ l ∗
  "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
  "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
  (|={⊤, ∅}=> ∃ key uid old_meta old_spec children,
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
    "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
    "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
    "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
    "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
    "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝ ∗
    "Hclose" ∷ (
      (∀ i' kobj',
        ( "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
          "%Hupdated" ∷ ⌜ KObjectV.updated kobj kobj' ⌝ ∗
          "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
          "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
          "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}))
        ={∅, ⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
      (∀ err,
        ( "%Hconflict" ∷ ⌜ conflict_error err ⌝ ∗
          "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
          "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
          "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children)
        ={∅, ⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
    )%I
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
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
    iMod "Hau" as (key uid old_meta old_spec children) "H". iNamed "H".
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
  wp_method_call. rewrite /apimodel.State__updateⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_".
  rewrite exception_do_unseal /exception_do_def. wp_auto.
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro. split; [done|]. right. done. }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType [])
    with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  assert (namespace =
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')) as Hnamespace_new.
  { done. }
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i'|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <-Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    exfalso. done.
  }
  assert (∃ old_i, phys_state !! key = Some old_i)
    as [old_i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ old_kobj, abs_state !! key = Some old_kobj)
    as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <-Hdom_eq.
    apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _
    Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
    as "(Hdeepown_old_i & Hother_rep)".
  destruct old_i as [old_i|].
  2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as
    (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l &
      Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso. rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  { exfalso. eapply valid_resource_version_non_empty; done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. exact Hrv_valid. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict)
      as Herr_not_nil.
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with
      "[Hown_meta_frag Hown_spec_frag Hown_children_frag]")
      as "HΦ".
    { iFrame. iPureIntro. exact Herr_conflict. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _
        Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  }
  set P :=
    ObjectMetaV.equiv_except_resource_version
      ((KObjectV.objectmeta old_kobj) <|
        ObjectMetaV.OwnerReferences' :=
          (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
      (KObjectV.objectmeta kobj) ∧
    KObjectV.spec old_kobj = KObjectV.spec kobj ∧
    meta_parent_ref (KObjectV.objectmeta old_kobj) =
      Some (parent_key, parent_uid).
  destruct (Classical_Prop.classic P) as [Hdecide'|Hdecide'].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta kobj) ∧
        ObjectSpecV.valid_update old_spec (KObjectV.spec kobj)) as
      (Hvalid_meta_update & Hvalid_spec_update).
    { destruct old_spec, kobj; rewrite /KObjectV.valid_update /= in Hvalid_update |- *;
        rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
          ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
          ?/DeploymentV.valid_update in Hvalid_update;
        try contradiction; tauto. }
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (cview.own_auth_frag_lookup key old_kobj Hlookup_abs Hchild with
      "Hinv_Hown_children Hown_children_frag") as "%Hliving_parent".
    apply cview.living_obj_parent_ref_eq_some in Hliving_parent as [_ Hstored_parent].
    assert (meta_parent_ref old_meta = Some (parent_key, parent_uid)) as Hold_parent.
    { rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_eq.
      rewrite /obj_parent_ref /meta_parent_ref in Hstored_parent |- *.
      destruct (KObjectV.objectmeta old_kobj), old_meta; simpl in *.
      inversion Hmeta_eq; subst. exact Hstored_parent. }
    assert (ObjectMetaV.equiv_except_resource_version
        (old_meta <| ObjectMetaV.OwnerReferences' :=
          (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
        (KObjectV.objectmeta kobj)) as Howner_references_only.
    { destruct Hvalid_meta_update as [[Hsimple | Hrelease] _]; last exact Hrelease.
      exfalso.
      unfold obj_parent_ref in Hnew_parent.
      assert (meta_parent_ref old_meta = meta_parent_ref (KObjectV.objectmeta kobj))
        as Hparent_eq.
      { rewrite /ObjectMetaV.valid_simple_update /meta_parent_ref in Hsimple |- *.
        destruct old_meta, (KObjectV.objectmeta kobj); simpl in *.
        decompose [and] Hsimple. subst. done. }
      rewrite Hold_parent Hnew_parent in Hparent_eq. discriminate. }
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    iPoseProof (kview.own_spec_exists with
      "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = old_spec) as Hstored_spec_eq.
    { eapply Hspec_found; done. }
    exfalso. apply Hdecide'. unfold P.
    split_and!.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in
        Hmeta_eq Howner_references_only |- *.
      destruct (KObjectV.objectmeta old_kobj), old_meta,
        (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. done.
    - congruence.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_eq.
      rewrite /meta_parent_ref in Hold_parent |- *.
      destruct (KObjectV.objectmeta old_kobj), old_meta; simpl in *.
      inversion Hmeta_eq; subst. done.
  }
  unfold P in Hdecide'.
  destruct Hdecide' as
    (Howner_references_only_old & Hspec_old & Hold_parent_old).
  assert ((KObjectV.objectmeta kobj <|
    ObjectMetaV.Namespace' :=
      ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>) =
    KObjectV.objectmeta kobj) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with
    "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l
      $Hdeepown_st_old_l]") as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with
    "Hinv_Hown_abs") as "%Hauth_old". 1: done.
  destruct Hauth_old as
    (Hkey_old & Hvalid_old_kobj & Huid_old_in &
      Hno_speculative_parent_reference_old & Huid_unique_old).
  iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
    as "%Habs_extra_valid".
  assert (KObjectV.extra_valid old_kobj) as Hextra_valid_old.
  { exact (Habs_extra_valid key old_kobj Hlookup_abs). }
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  assert (ObjectSpecV.valid_update (KObjectV.spec old_kobj) (KObjectV.spec kobj))
    as Hvalid_spec_update.
  { rewrite <-Hspec_old.
    pose proof Hvalid_old_kobj as Hvalid_old_copy.
    destruct Hvalid_old_copy as (_ & _ & _ & Hvalid_old_spec & _).
    destruct (KObjectV.spec old_kobj); simpl.
    - apply PodSpecV.valid_update_refl. exact Hvalid_old_spec.
    - apply ReplicaSetSpecV.valid_update_refl.
      destruct Hvalid_old_spec as (Hvalid_create & _). exact Hvalid_create.
    - apply PersistentVolumeClaimSpecV.valid_update_refl.
      destruct Hvalid_old_spec as (Hvalid_create & _). exact Hvalid_create.
    - apply StatefulSetSpecV.valid_update_refl.
      destruct Hvalid_old_spec as (Hvalid_create & _). exact Hvalid_create.
    - apply DeploymentSpecV.valid_update_refl.
      destruct Hvalid_old_spec as ((replicas & Hreplicas & Hnonneg) & Hrest).
      split; last exact Hrest.
      rewrite Hreplicas. exact Hnonneg. }
  assert (ObjectMetaV.valid_update (KObjectV.objectmeta old_kobj)
      (KObjectV.objectmeta kobj)) as Hvalid_meta_update_actual.
  { rewrite /ObjectMetaV.valid_update. split.
    - right. exact Howner_references_only_old.
    - assert (ObjectMetaV.valid_create (KObjectV.kind kobj)
          (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')
          (KObjectV.objectmeta kobj)) as Hvalid_create_meta.
      { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
          rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
            ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
            ?/DeploymentV.valid_create
            ?/DeploymentV.valid_create in Hvalid;
          tauto. }
      rewrite /ObjectMetaV.valid_create in Hvalid_create_meta.
      rewrite decide_False in Hvalid_create_meta.
      1: exact Hname_nonempty.
      destruct Hvalid_create_meta as
        (_ & _ & Hlabels & Hannotations & Howners & Hfinalizers & Hmanaged_fields).
      split_and!; done. }
  assert (KObjectV.valid_update
      (KObjectV.kind kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')
      (KObjectV.objectmeta old_kobj) (KObjectV.spec old_kobj) kobj)
    as Hvalid_update_actual.
  { destruct old_kobj, kobj; rewrite /KObjectV.valid_update /=;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/DeploymentV.valid_update
        ?/DeploymentV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        ?/DeploymentV.valid_create
        ?/DeploymentV.valid_create
        /KObjectV.valid_create /= in Hvalid |- *;
      simpl in Hvalid_meta_update_actual, Hvalid_spec_update;
      try contradiction; tauto. }
  assert (update_prepared_for_helper
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') old_kobj kobj kobj) as Hprepared.
  { rewrite /update_prepared_for_helper. split_and!.
    - right. done.
    - right. exact e0.
    - exact Hkey_old_new.
    - rewrite <-e0.
      destruct kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]]; destruct meta; done. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate_ok _ _ _ _ _ _ _
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') kobj with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (updated_kobj)
    "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hhelper_updated)".
  pose proof Hhelper_updated as
    (Hstatus_eq & Hhelper_spec_eq & Hhelper_result_updated & _).
  assert (update_objects_equiv_except_resource_version updated_kobj updated_kobj)
    as Hequiv_updated_refl.
  { rewrite /update_objects_equiv_except_resource_version
      /ObjectMetaV.equiv_except_resource_version.
    destruct updated_kobj; done. }
  pose proof (Hhelper_result_updated kobj updated_kobj Hprepared Hequiv_updated_refl)
    as Hupdated_kobj.
  pose proof (applyValidationAndDefaultingOnUpdate_updated_implies_valid
    (KObjectV.kind kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') old_kobj kobj kobj updated_kobj
    Hvalid_old_kobj Hvalid_update_actual Hprepared Hhelper_updated)
    as Hvalid_updated_kobj.
  assert (KObjectV.same_kind kobj updated_kobj ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.Name') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID'))
    as (Hsame_kind & Hname_updated & Hnamespace_updated & Huid_updated).
  { destruct kobj, updated_kobj;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated
        /DeploymentV.updated /= in Hupdated_kobj |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hupdated_kobj |- *; tauto. }
  assert (KObjectV.key old_kobj = KObjectV.key updated_kobj) as Hsame_key.
  { rewrite Hkey_old_new /KObjectV.key.
    rewrite Hname_updated Hnamespace_updated.
    destruct kobj, updated_kobj; simpl in Hsame_kind |- *; try done. }
  assert (KObjectV.spec updated_kobj = KObjectV.spec old_kobj)
    as Hspec_updated_old.
  { apply Hhelper_spec_eq. symmetry. exact Hspec_old. }
  wp_auto.
  wp_apply (wp_shouldDeleteDuringUpdate_general with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (should_delete)
    "(Hdeepown_l & Hdeepown_old_l & %Hshould_delete)".
  destruct should_delete; wp_auto.
  {
    iApply fupd_wp.
    iMod "Hau" as
      (key0 uid old_meta old_spec children) "H".
    iNamed "H".
    iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso. apply (Hshould_delete eq_refl). exact Hold_living.
  }
  wp_apply (wp_storageObjectDeepEqual with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!; done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  {
    assert (storage_object_normalize updated_kobj =
      storage_object_normalize old_kobj) as Hstorage_eq.
    { apply Hifv. done. }
    assert (meta_parent_ref (KObjectV.objectmeta updated_kobj) =
      meta_parent_ref (KObjectV.objectmeta old_kobj)) as Hparent_storage.
    { assert (KObjectV.objectmeta
          (storage_object_normalize updated_kobj) =
        KObjectV.objectmeta
          (storage_object_normalize old_kobj)) as Hnormalized.
      { rewrite Hstorage_eq. done. }
      rewrite /storage_object_normalize
        !objectmeta_update_objectmeta in Hnormalized.
      rewrite /meta_parent_ref.
      destruct (KObjectV.objectmeta updated_kobj),
        (KObjectV.objectmeta old_kobj); simpl in *.
      inversion Hnormalized. done. }
    assert (meta_parent_ref (KObjectV.objectmeta updated_kobj) = None)
      as Hupdated_parent_none.
    { change (obj_parent_ref updated_kobj = None).
      rewrite (kobject_updated_parent_ref _ _ Hupdated_kobj) Hnew_parent. done. }
    rewrite Hold_parent_old in Hparent_storage.
    congruence.
  }
  wp_apply (wp_State__generateNewRVAndUpdate with
    "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv)
    "(%Hlookup_phys_used_rv & %Hvalid_rv &
      Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with
    "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l &
      Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_SetResourceVersion_deepown_kobject i1 l1 updated_kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  set new_kmeta :=
    (KObjectV.objectmeta updated_kobj <|
      ObjectMetaV.ResourceVersion' := rv |>).
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta.
    destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
  iPoseProof (own_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_update with
    "Hinv_Hown_abs Hown_meta_frag Hown_spec_frag") as
    "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
  assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta kobj) ∧
      ObjectSpecV.valid_update old_spec (KObjectV.spec kobj)) as
    (Hvalid_meta_update_frag & Hvalid_spec_update_frag).
  { destruct old_spec, kobj; rewrite /KObjectV.valid_update /= in Hvalid_update |- *;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/DeploymentV.valid_update in Hvalid_update;
      try contradiction; tauto. }
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  iPoseProof (kview.own_meta_exists2 with
    "Hinv_Hown_abs Hown_meta_frag")
    as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
  iPoseProof (cview.own_auth_frag_lookup key old_kobj Hlookup_abs Hchild with
    "Hinv_Hown_children Hown_children_frag") as "%Hliving_parent".
  apply cview.living_obj_parent_ref_eq_some in Hliving_parent as [_ Hstored_parent].
  assert (meta_parent_ref old_meta = Some (parent_key, parent_uid)) as Hold_parent.
  { rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in Hmeta_eq.
    rewrite /obj_parent_ref /meta_parent_ref in Hstored_parent |- *.
    destruct (KObjectV.objectmeta old_kobj), old_meta; simpl in *.
    inversion Hmeta_eq; subst. exact Hstored_parent. }
  assert (ObjectMetaV.equiv_except_resource_version
      (old_meta <| ObjectMetaV.OwnerReferences' :=
        (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
      (KObjectV.objectmeta kobj)) as Howner_references_only.
  { destruct Hvalid_meta_update_frag as [[Hsimple | Hrelease] _]; last exact Hrelease.
    exfalso.
    unfold obj_parent_ref in Hnew_parent.
    assert (meta_parent_ref old_meta = meta_parent_ref (KObjectV.objectmeta kobj))
      as Hparent_eq.
    { rewrite /ObjectMetaV.valid_simple_update /meta_parent_ref in Hsimple |- *.
      destruct old_meta, (KObjectV.objectmeta kobj); simpl in *.
      decompose [and] Hsimple. subst. done. }
    rewrite Hold_parent Hnew_parent in Hparent_eq. discriminate. }
  iPoseProof (kview.own_meta_living Hlookup_abs with
    "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
  iPoseProof (kview.own_spec_exists with
    "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
  assert (KObjectV.spec old_kobj = old_spec) as Hstored_spec_eq.
  { eapply Hspec_found; done. }
  assert (update_objects_equiv_except_resource_version updated_kobj new_kobj)
    as Hequiv_updated_new.
  { unfold new_kobj, new_kmeta, update_objects_equiv_except_resource_version.
    destruct updated_kobj; simpl; split_and!; try done.
    all: rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version; destruct ObjectMeta'; done. }
  pose proof (Hhelper_result_updated kobj new_kobj Hprepared Hequiv_updated_new)
    as Hupdated_new.
  assert (KObjectV.same_kind kobj new_kobj ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Name') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp'))
    as (Hsame_kind_new & Hname_new & Hnamespace_stored_new & Huid_new &
      Hdeletion_timestamp_new).
  { destruct kobj, new_kobj;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated
        /DeploymentV.updated /= in Hupdated_new |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hupdated_new |- *; tauto. }
  assert (KObjectV.valid new_kobj) as Hvalid_new.
  { unfold new_kobj, new_kmeta.
    pose proof Hvalid_updated_kobj as
      (Hupdated_valid_typemeta & _ & Hupdated_valid_meta & Hupdated_valid_spec &
        Hupdated_valid_status).
    split_and!.
    - rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
      exact Hupdated_valid_typemeta.
    - rewrite objectmeta_update_objectmeta. exact Hvalid_rv.
    - rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
      destruct (KObjectV.objectmeta updated_kobj); simpl in *; done.
    - rewrite KObjectV.spec_update_objectmeta. exact Hupdated_valid_spec.
    - rewrite KObjectV.status_update_objectmeta. exact Hupdated_valid_status. }
  assert (kview.valid_k_uid_obj key uid new_kobj)
    as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split.
    - rewrite Hkey_eq /KObjectV.key.
      rewrite Hname_new Hnamespace_stored_new.
      destruct kobj, new_kobj; simpl in Hsame_kind_new |- *; try done.
    - split.
      + rewrite Huid_eq. symmetry. exact Huid_new.
      + split.
        * exact Hvalid_new.
        * unfold new_kobj.
          apply KObjectV.extra_valid_update_objectmeta.
          rewrite /KObjectV.extra_valid Hspec_updated_old.
          exact Hextra_valid_old.
  }
  assert (obj_parent_ref new_kobj = None) as Hnew_parent_none.
  { rewrite (kobject_updated_parent_ref _ _ Hupdated_new) Hnew_parent. done. }
  iPoseProof (kview.own_meta_living Hlookup_abs with
    "Hinv_Hown_abs Hown_meta_frag") as "%Hold_deletion_timestamp_none".
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') =
      None) as Hnew_deletion_timestamp_none.
  { assert (Hold_meta_none : old_meta.(ObjectMetaV.DeletionTimestamp') = None).
    { pose proof Hmeta_eq as Hmeta_fields.
      rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_fields.
      pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hmeta_fields)
        as Hdeletion_timestamp.
      simpl in Hdeletion_timestamp. rewrite <-Hdeletion_timestamp.
      exact Hold_deletion_timestamp_none. }
    assert (Hrequest_none :
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') = None).
    { pose proof Howner_references_only as Hmeta_fields.
      rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_fields.
      pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hmeta_fields) as Hdt.
      simpl in Hdt.
      change (ObjectMetaV.DeletionTimestamp' old_meta =
        ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj)) in Hdt.
      rewrite -Hdt. exact Hold_meta_none. }
    rewrite Hdeletion_timestamp_new. exact Hrequest_none. }
  iMod (kview.update_meta_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag)".
  { exact Hvalid_kuid_new. }
  { exact Hnew_deletion_timestamp_none. }
  { unfold no_speculative_parent_reference.
    intros kind' name' uid' Hparent.
    unfold meta_parent_ref_is in Hparent.
    unfold obj_parent_ref in Hnew_parent_none.
    rewrite Hnew_parent_none in Hparent. done. }
  { exact Hlookup_abs. }
  { unfold new_kobj. rewrite KObjectV.spec_update_objectmeta.
    symmetry. exact Hspec_updated_old. }
  { unfold new_kobj. rewrite KObjectV.status_update_objectmeta.
    symmetry. exact Hstatus_eq. }
  iPoseProof (cview.own_auth_frag_lookup key old_kobj Hlookup_abs Hchild with
    "Hinv_Hown_children Hown_children_frag") as "%Hold_living_parent".
  assert (Hold_terminating_parent_none :
      terminating_children.terminating_obj_parent_ref old_kobj = None).
  { unfold terminating_children.terminating_obj_parent_ref.
    rewrite Hold_deletion_timestamp_none. done. }
  assert (Hnew_terminating_parent_none :
      terminating_children.terminating_obj_parent_ref new_kobj = None).
  { unfold terminating_children.terminating_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [exact Hnew_parent_none|done]. }
  iMod (cview.release_child_vs key old_kobj new_kobj with
    "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "(Hinv_Hown_children & Hown_children_frag)".
  { exact Hlookup_abs. }
  { exact Hold_living_parent. }
  { unfold living_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [done|exact Hnew_parent_none]. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta Huid_obj Huid_eq.
    symmetry. exact Huid_updated. }
  iMod (terminating_children.update_same_parent_vs
    γ.(γ_terminating_children) abs_state key old_kobj new_kobj with
    "Hinv_Hown_terminating_children") as
    "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { rewrite Hold_terminating_parent_none Hnew_terminating_parent_none. done. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with
    "Hinv_Hown_deletion_observations") as
    "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    rewrite Huid_obj Huid_eq. symmetry.
    exact Huid_updated. }
  { intros Hold_terminating.
    exfalso. apply Hold_terminating. exact Hold_deletion_timestamp_none. }
  iClear "Hown_meta_frag Hown_spec_frag".
  iDestruct "Hclose" as "[Hclose_success _]".
  iMod ("Hclose_success" $! i1' new_kobj with
    "[Hdeepown_i1' Hown_children_frag]") as "HΦ".
  { iSplit.
    { iPureIntro. exact Hvalid_new. }
    iSplit; first (iPureIntro; exact Hupdated_new).
    iSplit.
    { iPureIntro. unfold new_kobj.
      rewrite KObjectV.spec_update_objectmeta.
      rewrite Hspec_updated_old Hstored_spec_eq. done. }
    iFrame "Hdeepown_i1' Hown_children_frag". }
  iModIntro.
  iAssert (([∗ map] i; obj ∈
      <[key:=interface.ok i1]> phys_state;
      <[key:=new_kobj]> abs_state,
      match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  rewrite return_val_unseal /return_val_def. wp_auto.
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame "#". iFrame.
    iPureIntro. split_and!. all: try done.
  }
  iExact "HΦ".
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem.
Qed.

End proof.
