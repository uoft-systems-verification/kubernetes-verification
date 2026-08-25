From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(** Lookup through a deletion observation is intentionally weaker than lookup
    through a metadata fragment.  The key may be absent or may have been reused
    by a different UID.  Only the same-UID case is known to be terminating. *)
Lemma wp_State__get_observed γ l key uid :
  {{{ "#Hpkg" ∷ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ key uid
  }}}
    l @! (go.PointerType apimodel.State) @! "get" #key
  {{{ ret err, RET (#ret, #err);
      (⌜ ret = interface.nil ∧ not_found_error err ⌝ ∨
      ∃ i kobj,
        ⌜ ret = interface.ok i ∧ err = interface.nil ∧
          KObjectV.valid kobj ∧ KObjectV.extra_valid kobj ∧
          key = KObjectV.key kobj ∧
          ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') = uid →
            (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None) ⌝ ∧
        KObjectV.deepown_i i kobj 1)%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hisk".
  wp_method_call. rewrite /apimodel.State__getⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer".
  simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_map_lookup2_KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  - apply bool_decide_eq_true in Hdecide.
    destruct Hdecide as [i Hlookup_phys].
    assert (∃ kobj, abs_state !! key = Some kobj) as [kobj Hlookup_abs].
    { apply elem_of_dom. rewrite <-Hdom_eq. apply elem_of_dom.
      eexists. done. }
    iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hlookup_phys Hlookup_abs
      with "Hinv_Hphys_abs_rep") as "(Hdeepown_i & Hother_rep)".
    destruct i as [i|].
    2: { simpl. iDestruct "Hdeepown_i" as %[]. }
    rewrite Hlookup_phys. wp_auto.
    wp_apply (wp_deepCopy with "[$Hpkg $Hdeepown_i]").
    iIntros (i') "(Hdeepown_i' & Hdeepown_i)". wp_auto.
    iPoseProof (kview.own_auth_valid key kobj with "Hinv_Hown_abs") as "%Hvalid_obj".
    specialize (Hvalid_obj Hlookup_abs).
    destruct Hvalid_obj as [Hkey [Hvalid _]].
    iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
      as "%Habs_extra_valid".
    assert (KObjectV.extra_valid kobj) as Hextra_valid.
    { exact (Habs_extra_valid key kobj Hlookup_abs). }
    iPoseProof (deletion_observation.auth_frag_valid with
      "Hinv_Hown_deletion_observations Hown_deletion_observed_frag") as "%Hobserved".
    destruct Hobserved as [_ Hterminating].
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { iApply "Hother_rep". iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! (interface.ok i') interface.nil).
    iRight. iExists i', kobj. iFrame.
    iPureIntro. split_and!; try done.
    intros Huid. eapply Hterminating; done.
  - apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys.
    { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    rewrite /is_Some Hlookup_phys. wp_auto.
    wp_apply (wp_NewNotFound
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := key.(KKey.Kind') |}
      key.(KKey.Name')).
    iIntros (err_l) "%Hnot_found". wp_auto.
    set err := interface.mk_ok (go.PointerType api_errors.StatusError) #err_l.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! interface.nil err).
    iLeft. iPureIntro. split; done.
Qed.

End proof.
