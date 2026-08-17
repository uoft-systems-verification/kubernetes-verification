From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".


Lemma wp_State__update_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
    "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
    "%Hrv_valid" ∷ ⌜ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ key uid kmeta kspec,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      (* Hno_deletion_timestamp ensures that the update doesn't delete the object *)
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
	    "Hclose" ∷ (
	      (∀ i' kobj',
	        ( ⌜ KObjectV.valid kobj' ⌝ ∗
	          ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
	          ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
	          ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
	          KObjectV.deepown_i i' kobj' 1 ∗
	          own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
	          own_spec_frag γ key uid 1 (KObjectV.spec kobj'))
          ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
	      (∀ err,
	        ( ⌜ conflict_error err ⌝ ∗
	          own_meta_frag γ key uid 1 kmeta ∗
	          own_spec_frag γ key uid 1 kspec)
          ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
	    )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__updateⁱᵐᵖˡ. wp_call.
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
  { pose proof Hvalid as Hvalid_copy.
    destruct Hvalid_copy as (_ & _ & Hmeta & _).
    unfold ObjectMetaV.valid_named_create in Hmeta. tauto. }
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
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
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
  1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso.
    rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  {
    exfalso. eapply valid_resource_version_non_empty; done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. exact Hrv_valid. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_not_nil.
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with "[Hown_meta_frag Hown_spec_frag]") as "HΦ".
    { iSplit; first done. iFrame. }
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
    iExact "HΦ".
  }
  set P := ObjectMetaV.valid_simple_update (KObjectV.objectmeta old_kobj) (KObjectV.objectmeta kobj) ∧
    ObjectSpecV.valid_update (KObjectV.spec old_kobj) (KObjectV.spec kobj).
  destruct (bool_decide(P)) eqn:Hdecide'.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = kspec) as Hspec_eq.
    { eapply Hspec_found; done. }
    apply bool_decide_eq_false in Hdecide'.
    exfalso. apply Hdecide'. unfold P.
    split.
    - rewrite /ObjectMetaV.valid_simple_update in Hvalid_meta_update |- *.
      rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version in Hmeta_eq.
      destruct (KObjectV.objectmeta old_kobj), kmeta, (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. tauto.
    - rewrite Hspec_eq. done.
  }
  apply bool_decide_eq_true in Hdecide'.
  unfold P in Hdecide'. destruct Hdecide' as [Hvalid_meta_old Hvalid_spec_old].
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>)
    = (KObjectV.objectmeta kobj)) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]")
    as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with
    "Hinv_Hown_abs") as "%Hauth_old".
  1: done.
  destruct Hauth_old as (Hkey_old & Hvalid_old_kobj & Huid_old_in &
    Hno_speculative_parent_reference_old & Huid_unique_old).
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; try done.
    left. done. }
  iIntros (updated_kobj) "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hvalid_updated_kobj
    & %Hsame_key & %Htypemeta_eq & %Hupdated_meta &
    %Hupdated_spec & %Hspec_eq_if_unchanged & %Hstatus_eq)". wp_auto.
  set P' := ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta old_kobj) = None.
  destruct (bool_decide(P')) eqn:Hdecide''.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
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
  wp_apply (wp_shouldDeleteDuringUpdate_false with "[$Hdeepown_l $Hdeepown_old_l]").
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
    assert (ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec old_kobj))
      as Hupdated_spec_old.
    { assert (KObjectV.spec updated_kobj = KObjectV.spec old_kobj) as Hspec_updated_old.
      { eapply storage_object_normalize_spec_eq. done. }
      rewrite <-Hspec_updated_old. done. }
    assert (KObjectV.same_kind kobj old_kobj) as Hsame_kind_old.
    { destruct kobj, old_kobj; simpl in *; try done.
      all: unfold KObjectV.key in Hkey_old_new;
        simpl in Hkey_old_new; congruence. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (update_own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
      as "Hown_meta_frag".
    iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = kspec) as Hspec_eq.
    { eapply Hspec_found; done. }
    iDestruct "Hclose" as "[Hclose_success _]".
	    iMod ("Hclose_success" $! old_i1 old_kobj with
	      "[Hdeepown_old_i1 Hown_meta_frag Hown_spec_frag]") as "HΦ".
	    { iSplit; first (iPureIntro; exact Hvalid_old_kobj).
	      iSplit; first done.
	      iSplit; first done.
	      iSplit; first done.
      iFrame "Hdeepown_old_i1 Hown_meta_frag".
      rewrite Hspec_eq. iFrame. }
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
    iExact "HΦ".
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
  iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  assert (kview.valid_k_uid_obj key uid new_kobj) as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split.
    - unfold new_kobj, new_kmeta.
      rewrite key_update_objectmeta_set_resource_version.
      rewrite Hkey_new.
      rewrite <-Hkey_old_new.
      exact Hsame_key.
    - split.
      + unfold new_kobj, new_kmeta.
        rewrite objectmeta_update_objectmeta.
        rewrite Huid_eq.
        symmetry. eapply objectmeta_updated_set_resource_version_uid. done.
      + unfold new_kobj, new_kmeta.
        eapply valid_update_objectmeta_set_resource_version; done.
  }
  iMod (kview.update_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag] [$Hown_spec_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag & Hown_spec_frag)".
  { exact Hvalid_kuid_new. }
  { assert (Hdeletion_timestamp :
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')).
    { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
      eapply valid_simple_update_updated_set_resource_version_deletion_timestamp;
        done. }
    rewrite -Hdeletion_timestamp. exact Hdecide''. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_no_speculative_parent_reference;
      [exact Hvalid_meta_old|exact Hupdated_meta|exact Hno_speculative_parent_reference_old]. }
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta.
    rewrite KObjectV.status_update_objectmeta. symmetry. done. }
  iMod (cview.simple_update_vs key old_kobj new_kobj with "[$Hinv_Hown_children]")
    as "Hinv_Hown_children".
  { done. }
  { assert (Hdeletion_timestamp :
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')).
    { unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      eapply valid_simple_update_updated_set_resource_version_deletion_timestamp;
        done. }
    unfold living_obj_parent_ref, obj_parent_ref.
    rewrite Hdeletion_timestamp.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [done|].
    unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_parent_ref; done. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    symmetry. eapply valid_simple_update_updated_set_resource_version_uid; done. }
  iMod (terminating_children.update_same_parent_vs
    γ.(γ_terminating_children) abs_state key old_kobj new_kobj with
    "Hinv_Hown_terminating_children") as
    "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { unfold terminating_children.terminating_obj_parent_ref, obj_parent_ref.
    assert (Hdeletion_timestamp :
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')).
    { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
      eapply valid_simple_update_updated_set_resource_version_deletion_timestamp;
        done. }
    rewrite Hdeletion_timestamp.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [|done].
    unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_parent_ref; done. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with
    "Hinv_Hown_deletion_observations") as
    "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    symmetry.
    eapply valid_simple_update_updated_set_resource_version_uid; done. }
  { intros Hold_terminating.
    assert (Hdeletion_timestamp :
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')).
    { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
      eapply valid_simple_update_updated_set_resource_version_deletion_timestamp;
        done. }
    rewrite -Hdeletion_timestamp. exact Hold_terminating. }
  assert (KObjectV.same_kind kobj new_kobj) as Hsame_kind_new.
  { unfold new_kobj.
    destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  iDestruct "Hclose" as "[Hclose_success _]".
  iMod ("Hclose_success" $! i1' new_kobj with
    "[Hdeepown_i1' Hown_meta_frag Hown_spec_frag]") as "HΦ".
  { iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      eapply valid_update_objectmeta_set_resource_version; done. }
    iSplit.
    { iPureIntro. exact Hsame_kind_new. }
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      eapply objectmeta_updated_set_resource_version; done. }
    iSplit.
    { iPureIntro. unfold new_kobj.
      rewrite KObjectV.spec_update_objectmeta. done. }
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
    iFrame "#". iFrame. iNext. iFrame. iPureIntro. split_and!.
    all: try done.
  }
  iExact "HΦ".
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem.
Qed.

Lemma wp_State__update γ l kind namespace i kobj key uid kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hrv_valid" ∷ ⌜ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ⌝ ∗
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
    l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i)
  {{{ ret err i' kobj', RET (ret, #err);
      (⌜ err = interface.nil ⌝ ∗
        ⌜ ret = #(interface.ok i') ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
        ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj')) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ret = #interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_spec_frag γ key uid 1 kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__update_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iSplit.
  - iIntros (i' kobj') "Hpost".
    iMod "Hmask" as "_".
    iModIntro. iNext.
    iApply ("HΦ" $! #(interface.ok i') interface.nil i' kobj').
    iLeft. iSplit; first done.
    iSplit; first done.
    iExact "Hpost".
  - iIntros (err) "Hpost".
    iDestruct "Hpost" as "(%Hconflict & Hown_meta_frag & Hown_spec_frag)".
    pose proof (conflict_error_not_nil err Hconflict) as Herr_ne.
    iMod "Hmask" as "_".
    iModIntro. iNext.
    iApply ("HΦ" $! #interface.nil err i kobj).
    iRight. iSplit; first done.
    iSplit; first done.
    iFrame.
Qed.

End proof.
