From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common update.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!go.IntoValInj KKey.t}.
Local Set Default Proof Using "All".

Lemma storage_object_normalize_status_eq obj1 obj2 :
  storage_object_normalize obj1 = storage_object_normalize obj2 →
  KObjectV.status obj1 = KObjectV.status obj2.
Proof.
  intros Hstorage.
  assert (KObjectV.status (storage_object_normalize obj1) =
          KObjectV.status (storage_object_normalize obj2)) as Hstatus_eq.
  { rewrite Hstorage. done. }
  rewrite /storage_object_normalize !KObjectV.status_update_objectmeta in Hstatus_eq.
  exact Hstatus_eq.
Qed.

Lemma wp_State__update_status_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ key uid kmeta kstatus,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 kstatus ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_status_update" ∷ ⌜ ObjectStatusV.valid_update kstatus (KObjectV.status kobj) ⌝ ∗
      (* Hno_deletion_timestamp ensures that the status update doesn't delete the object. *)
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hclose" ∷ (
          ∀ i' err kobj',
            ( ( ⌜ err = interface.nil ⌝ ∗
                ⌜ KObjectV.valid kobj' ⌝ ∗
                ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
                ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
                ⌜ ObjectStatusV.updated (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
                KObjectV.deepown_i i' kobj' 1 ∗
                own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
                own_status_frag γ key uid 1 (KObjectV.status kobj')) ∨
              ( ⌜ err ≠ interface.nil ⌝ ∗
                ⌜ conflict_error err ⌝ ∗
                own_meta_frag γ key uid 1 kmeta ∗
                own_status_frag γ key uid 1 kstatus)
            )
              ={∅,⊤}=∗ ▷ Φ ((if decide (err = interface.nil) then #(interface.ok i') else #interface.nil), #err)%V
      )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__updateStatusⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro. split. 1: done. right. done. }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go) as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _). apply ObjectMetaV.valid_name_nonempty_of_valid. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  assert (namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')) as Hnamespace_new.
  { done. }
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i'|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <- Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { unfold key. rewrite Hkind_matches. rewrite Hns_matches. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    exfalso.
    done.
  }
  assert (∃ old_i, phys_state !! key = Some old_i) as [old_i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ old_kobj, abs_state !! key = Some old_kobj) as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
    as "(Hdeepown_old_i & Hother_rep)".
  destruct old_i as [old_i|].
  2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l & Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  1: {
    exfalso.
    destruct Hvalid as (_ & _ & Hmeta_valid & _).
    pose proof (ObjectMetaV.valid_uid_of_valid _ Hmeta_valid) as Huid_valid.
    pose proof (valid_uid_non_empty _ Huid_valid) as Huid_nonempty. done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    exfalso.
    rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  {
    exfalso.
    destruct Hvalid as (_ & Hrv_valid & _).
    pose proof (valid_resource_version_non_empty _ Hrv_valid) as Hrv_nonempty. done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. destruct Hvalid as (_ & Hrv_valid & _). done. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "(%Herr_not_nil & %Herr_conflict)". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iMod ("Hclose" $! i1 err kobj with "[Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iRight. iSplit; first done. iSplit; first done. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExactEq "HΦ".
    rewrite decide_False; done.
  }
  set P := ObjectMetaV.valid_simple_update (KObjectV.objectmeta old_kobj) (KObjectV.objectmeta kobj) ∧
    ObjectStatusV.valid_update (KObjectV.status old_kobj) (KObjectV.status kobj).
  destruct (bool_decide(P)) eqn:Hdecide'.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found".
    assert (KObjectV.status old_kobj = kstatus) as Hstatus_eq.
    { eapply Hstatus_found; done. }
    apply bool_decide_eq_false in Hdecide'.
    exfalso. apply Hdecide'. unfold P.
    split.
    - rewrite /ObjectMetaV.valid_simple_update in Hvalid_meta_update |- *.
      rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version in Hmeta_eq.
      destruct (KObjectV.objectmeta old_kobj), kmeta, (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. tauto.
    - rewrite Hstatus_eq. done.
  }
  apply bool_decide_eq_true in Hdecide'.
  unfold P in Hdecide'. destruct Hdecide' as [Hvalid_meta_old Hvalid_status_old].
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>)
    = (KObjectV.objectmeta kobj)) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]")
    as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with "Hinv_Hown_abs") as "%Hauth_old".
  1: done.
  destruct Hauth_old as (Hkey_old & Hvalid_old_kobj & Huid_old_in &
    Hno_speculative_parent_reference_old & Huid_unique_old).
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (updated_kobj) "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hvalid_updated_kobj & %Hsame_key
    & %Hsame_kind & %Hupdated_meta & %Hspec_eq & %Hupdated_status)". wp_auto.
  set P' := ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta old_kobj) = None.
  destruct (bool_decide(P')) eqn:Hdecide''.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    apply bool_decide_eq_false in Hdecide''.
    exfalso. apply Hdecide''. unfold P'.
    rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hmeta_eq).
    exact Hno_deletion_timestamp.
  }
  apply bool_decide_eq_true in Hdecide''. unfold P' in Hdecide''.
  wp_apply (wp_shouldDeleteDuringUpdate with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros "(Hdeepown_l & Hdeepown_old_l)". wp_auto.
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!. all: done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  {
    assert (storage_object_normalize updated_kobj = storage_object_normalize old_kobj) as Hstorage_eq.
    { apply Hifv. done. }
    assert (ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta old_kobj))
      as Hupdated_meta_old.
    { eapply storage_object_normalize_objectmeta_updated; done. }
    assert (ObjectStatusV.updated (KObjectV.status kobj) (KObjectV.status old_kobj))
      as Hupdated_status_old.
    { assert (KObjectV.status updated_kobj = KObjectV.status old_kobj) as Hstatus_updated_old.
      { eapply storage_object_normalize_status_eq. done. }
      rewrite <-Hstatus_updated_old. done. }
    assert (KObjectV.same_kind kobj old_kobj) as Hsame_kind_old.
    { destruct kobj, old_kobj; simpl in *; try done.
      all: unfold KObjectV.key in Hkey_old_new; simpl in Hkey_old_new; congruence. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (update_own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
      as "Hown_meta_frag".
    iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found".
    assert (KObjectV.status old_kobj = kstatus) as Hstatus_eq.
    { eapply Hstatus_found; done. }
    iMod ("Hclose" $! old_i1 interface.nil old_kobj with
      "[Hdeepown_old_i1 Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iLeft.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iFrame "Hdeepown_old_i1 Hown_meta_frag".
      rewrite Hstatus_eq. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExactEq "HΦ".
    rewrite decide_True; done.
  }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv) "(%Hlookup_phys_used_rv & %Hvalid_rv & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 updated_kobj) as ->.
  { destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  set new_kmeta := (KObjectV.objectmeta updated_kobj <| ObjectMetaV.ResourceVersion' := rv |>).
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta. destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  assert (kview.valid_k_uid_obj key uid new_kobj) as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split_and!.
    - unfold new_kobj, new_kmeta.
      rewrite key_update_objectmeta_set_resource_version.
      rewrite <- Hsame_key. done.
    - unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      rewrite Huid_eq.
      symmetry. eapply objectmeta_updated_set_resource_version_uid. done.
    - unfold new_kobj, new_kmeta.
      eapply valid_update_objectmeta_set_resource_version; done.
  }
  iMod (kview.update_status_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag] [$Hown_status_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag & Hown_status_frag)".
  { exact Hvalid_kuid_new. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_no_speculative_parent_reference;
      [exact Hvalid_meta_old|exact Hupdated_meta|exact Hno_speculative_parent_reference_old]. }
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta.
    rewrite KObjectV.spec_update_objectmeta. symmetry. done. }
  iMod (cview.simple_update_vs key old_kobj new_kobj with "[$Hinv_Hown_children]")
    as "Hinv_Hown_children".
  { done. }
  { unfold new_kobj, new_kmeta, obj_parent_ref.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_parent_ref; done. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    symmetry. eapply valid_simple_update_updated_set_resource_version_uid; done. }
  assert (KObjectV.same_kind kobj new_kobj) as Hsame_kind_new.
  { unfold new_kobj. destruct kobj, updated_kobj; done. }
  assert (KObjectV.valid new_kobj) as Hvalid_new_kobj.
  { destruct Hvalid_kuid_new as (_ & _ & Hvalid_new_kobj). done. }
  iMod ("Hclose" $! i1' interface.nil new_kobj with
    "[Hdeepown_i1' Hown_meta_frag Hown_status_frag]") as "HΦ".
  { iLeft.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      eapply objectmeta_updated_set_resource_version; done. }
    iSplit.
    { iPureIntro. unfold new_kobj.
      rewrite KObjectV.status_update_objectmeta. done. }
    iFrame. }
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[key:=interface.ok i1]> phys_state; <[key:=new_kobj]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H".
    iFrame "#". iFrame. iPureIntro. split_and!.
    all: try done.
    eapply update_tombed_uid_update_eq_used_uid_sub; [done|done|].
    unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_uid; done.
  }
  iExactEq "HΦ".
  rewrite decide_True; done.
Unshelve.
all: try done.
Qed.

Lemma wp_State__update_status γ l kind namespace i kobj key uid kmeta kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_status_update" ∷ ⌜ ObjectStatusV.valid_update kstatus (KObjectV.status kobj) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 kstatus
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i)
  {{{ i' err kobj', RET ((if decide (err = interface.nil) then #(interface.ok i') else #interface.nil), #err);
      (⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
        ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectStatusV.updated (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj')) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_status_frag γ key uid 1 kstatus)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__update_status_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iIntros (i' err kobj') "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i' err kobj').
  iDestruct "Hpost" as "[Hpost|Hpost]".
  - iLeft. iExact "Hpost".
  - iRight. iDestruct "Hpost" as "($ & _ & $ & $)".
Qed.

End proof.
