From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_get.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* An Available reservation fragment entails that the key is absent from the
   authoritative object map. Therefore lookup takes the concrete NotFound
   branch and preserves the fragment for a subsequent named create. *)
Lemma wp_State__get_reserved_au γ l key dq :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=>
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key ∗
      "Hclose" ∷ (∀ err,
        ⌜ not_found_error err ⌝ ∗
        own_available_reserved_frag γ dq key
          ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
  ) -∗
  WP l @! (go.PointerType apimodel.State) @! "get" #key {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)".
  iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__getⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer".
  simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_map_lookup2_KKey (go.InterfaceType [])
    with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  { apply bool_decide_eq_true in Hdecide.
    assert (∃ i, phys_state !! key = Some i) as [i Hlookup_phys] by done.
    assert (∃ kobj, abs_state !! key = Some kobj) as [kobj Hlookup_abs].
    { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom.
      eexists. done. }
    iApply fupd_wp.
    iMod "Hau" as "H". iNamed "H".
    iPoseProof (kview.own_reservation_valid
      with "[$Hinv_Hown_abs] [$Hown_reserved_frag]") as
      "%Hreservation_valid".
    destruct Hreservation_valid as [_ Hlookup_abs_none].
    rewrite Hlookup_abs in Hlookup_abs_none. done. }
  apply bool_decide_eq_false in Hdecide.
  assert (phys_state !! key = None) as Hlookup_phys.
  { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done].
    exfalso. apply Hdecide. done. }
  rewrite /is_Some Hlookup_phys. wp_auto.
  wp_apply (wp_NewNotFound
    {| schema.GroupResource.Group' := ""%go;
       schema.GroupResource.Resource' := key.(KKey.Kind') |}
    key.(KKey.Name')).
  iIntros (err_l) "%Hnot_found". wp_auto.
  set err := interface.mk_ok
    (go.PointerType api_errors.StatusError) #err_l.
  iApply fupd_wp.
  iMod "Hau" as "H". iNamed "H".
  iMod ("Hclose" $! err with "[$Hown_reserved_frag]") as "HΦ".
  { done. }
  iModIntro.
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ".
Qed.

Lemma wp_State__get_reserved γ l key dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}
    l @! (go.PointerType apimodel.State) @! "get" #key
  {{{ err, RET (#interface.nil, #err);
      "%Hnot_found" ∷ ⌜ not_found_error err ⌝ ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hisk & Hown_reserved_frag) HΦ".
  iApply wp_State__get_reserved_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iFrame "Hown_reserved_frag".
  iIntros (err) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! err with "Hpost").
Qed.

Lemma wp_State__get_deleting_reserved_au γ l key uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=>
      "Hown_reserved_frag" ∷ own_deleting_reserved_frag γ 1 key uid ∗
      "Hclose" ∷
        ((∀ i kobj,
          ⌜ KObjectV.valid kobj ⌝ ∗
          ⌜ KObjectV.extra_valid kobj ⌝ ∗
          ⌜ key = KObjectV.key kobj ⌝ ∗
          ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') = uid ⌝ ∗
          ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
          KObjectV.deepown_i i kobj 1 ∗
          own_deleting_reserved_frag γ 1 key uid
            ={∅,⊤}=∗ ▷ Φ (#(interface.ok i), #interface.nil)%V) ∧
        (∀ err,
          ⌜ not_found_error err ⌝ ∗
          own_available_reserved_frag γ 1 key
            ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V))
  ) -∗
  WP l @! (go.PointerType apimodel.State) @! "get" #key {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)".
  iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__getⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer".
  simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_map_lookup2_KKey (go.InterfaceType [])
    with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  - apply bool_decide_eq_true in Hdecide.
    destruct Hdecide as [i Hlookup_phys].
    assert (∃ kobj, abs_state !! key = Some kobj) as
      [kobj Hlookup_abs].
    { apply elem_of_dom. rewrite <-Hdom_eq. apply elem_of_dom.
      eexists. done. }
    iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _
      Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
      as "(Hdeepown_i & Hother_rep)".
    destruct i as [i|].
    2: { simpl. iDestruct "Hdeepown_i" as %[]. }
    rewrite Hlookup_phys. wp_auto.
    wp_apply (wp_deepCopy with "[$Hpkg $Hdeepown_i]").
    iIntros (i') "(Hdeepown_i' & Hdeepown_i)". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as "H". iNamed "H".
    iPoseProof (kview.own_reservation_valid with
      "Hinv_Hown_abs Hown_reserved_frag") as "%Hreservation_valid".
    destruct Hreservation_valid as [_ [Habsent|
      (ticket_obj & Hticket_lookup & Hticket_uid & Hticket_terminating)]].
    { rewrite Hlookup_abs in Habsent. done. }
    assert (ticket_obj = kobj) as -> by congruence.
    iPoseProof (kview.own_auth_valid key kobj with
      "Hinv_Hown_abs") as "%Hvalid_obj".
    specialize (Hvalid_obj Hlookup_abs).
    destruct Hvalid_obj as [Hkey [Hvalid _]].
    iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
      as "%Habs_extra_valid".
    assert (KObjectV.extra_valid kobj) as Hextra_valid.
    { exact (Habs_extra_valid key kobj Hlookup_abs). }
    iDestruct "Hclose" as "[Hclose _]".
    iMod ("Hclose" $! i' kobj with
      "[Hdeepown_i' Hown_reserved_frag]") as "HΦ".
    { iFrame. iPureIntro. split_and!; done. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { iApply "Hother_rep". iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  - apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys.
    { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <-Hdom_eq.
      apply not_elem_of_dom. done. }
    rewrite /is_Some Hlookup_phys. wp_auto.
    wp_apply (wp_NewNotFound
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := key.(KKey.Kind') |}
      key.(KKey.Name')).
    iIntros (err_l) "%Hnot_found". wp_auto.
    set err := interface.mk_ok
      (go.PointerType api_errors.StatusError) #err_l.
    iApply fupd_wp.
    iMod "Hau" as "H". iNamed "H".
    iMod (kview.recover_available_vs Hlookup_abs with
      "Hinv_Hown_abs Hown_reserved_frag") as
      "(Hinv_Hown_abs & Hown_reserved_frag)".
    iDestruct "Hclose" as "[_ Hclose]".
    iMod ("Hclose" $! err with
      "[Hown_reserved_frag]") as "HΦ".
    { iFrame. done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
Qed.

Lemma wp_State__get_deleting_reserved γ l key uid :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_reserved_frag" ∷ own_deleting_reserved_frag γ 1 key uid
  }}}
    l @! (go.PointerType apimodel.State) @! "get" #key
  {{{ ret err, RET (#ret, #err);
      (∃ i kobj,
        ⌜ ret = interface.ok i ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj ⌝ ∗
        ⌜ KObjectV.extra_valid kobj ⌝ ∗
        ⌜ key = KObjectV.key kobj ⌝ ∗
        ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') = uid ⌝ ∗
        ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        KObjectV.deepown_i i kobj 1 ∗
        own_deleting_reserved_frag γ 1 key uid) ∨
      (⌜ ret = interface.nil ⌝ ∗
        ⌜ not_found_error err ⌝ ∗
        own_available_reserved_frag γ 1 key)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hisk & Hown_reserved_frag) HΦ".
  iApply wp_State__get_deleting_reserved_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iFrame "Hown_reserved_frag".
  iSplit.
  - iIntros (i kobj) "Hpost".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! (interface.ok i) interface.nil).
    iLeft. iExists i, kobj. iFrame. done.
  - iIntros (err) "Hpost".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! interface.nil err).
    iRight. iFrame. done.
Qed.

Lemma wp_State__PersistentVolumeClaimMutGet_reserved γ l key namespace name dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "PersistentVolumeClaim"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}
    l @! (go.PointerType apimodel.State) @!
      "PersistentVolumeClaimMutGet" #namespace #name
  {{{ err, RET (#null, #err);
      "%Hnot_found" ∷ ⌜ not_found_error err ⌝ ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hisk & %Hkey_def & Hown_reserved_frag) HΦ".
  subst key.
  wp_method_call.
  rewrite /apimodel.State__PersistentVolumeClaimMutGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__get_reserved γ l
    {| KKey.Kind' := "PersistentVolumeClaim"%go;
       KKey.Namespace' := namespace;
       KKey.Name' := name |} dq
    with "[$Hinit $Hisk $Hown_reserved_frag]").
  iIntros (err) "Hpost". iNamed "Hpost".
  destruct err as [err_v|].
  2: { exfalso. exact (not_found_error_nil Hnot_found). }
  wp_auto.
  iApply ("HΦ" $! (interface.ok err_v) with "[$Hown_reserved_frag]").
  done.
Qed.

(* The public typed Get wrapper preserves the concrete NotFound result returned
   by [PersistentVolumeClaimMutGet]. *)
Lemma wp_State__PersistentVolumeClaimGet_reserved γ l key namespace name dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "PersistentVolumeClaim"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}
    l @! (go.PointerType apimodel.State) @!
      "PersistentVolumeClaimGet" #namespace #name
  {{{ err, RET (#null, #err);
      "%Hnot_found" ∷ ⌜ not_found_error err ⌝ ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ dq key
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hisk & %Hkey_def & Hown_reserved_frag) HΦ".
  wp_method_call.
  rewrite /apimodel.State__PersistentVolumeClaimGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__PersistentVolumeClaimMutGet_reserved
    γ l key namespace name dq
    with "[$Hinit $Hisk $Hown_reserved_frag]").
  { iPureIntro. exact Hkey_def. }
  iIntros (err) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

End proof.
