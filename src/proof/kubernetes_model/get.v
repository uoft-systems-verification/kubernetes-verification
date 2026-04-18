From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma wp_State__get γ l key :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      ⌜ err = interface.nil ⌝ ∗
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      KObjectV.deepown_i i kobj 1
      ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
Admitted.

Lemma wp_State__get_none γ l key uid :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Htomb" ∷ own_tombstone_frag γ uid
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      ⌜ err = interface.nil ⌝ ∗
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      ⌜ uid ≠ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      KObjectV.deepown_i i kobj 1
      ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof. Admitted.

Lemma wp_State__get_some_au γ l key :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ uid dq kmeta kspec_o kstatus_o,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec
      | None => True
      end ∗
      "Hown_status_frag" ∷ match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus
      | None => True
      end ∗
      "Hclose" ∷ (∀ i kobj,
        ⌜ KObjectV.valid kobj ⌝ ∗
        ⌜ key = KObjectV.key kobj ⌝ ∗
        ⌜ kmeta = KObjectV.objectmeta kobj ⌝ ∗
        KObjectV.deepown_i i kobj 1 ∗
        own_meta_frag γ key uid dq kmeta ∗
        match kspec_o with
        | Some kspec => own_spec_frag γ key uid dq kspec ∗ ⌜ kspec = KObjectV.spec kobj ⌝
        | None => True
        end ∗
        match kstatus_o with
        | Some kstatus => own_status_frag γ key uid dq kstatus ∗ ⌜ kstatus = KObjectV.status kobj ⌝
        | None => True
        end
          ={∅,⊤}=∗ ▷ Φ (#i, #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "get" #key {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <- Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kspec_o kstatus_o) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    done.
  }
  assert (∃ i, phys_state !! key = Some i) as [i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ kobj, abs_state !! key = Some kobj) as [kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom.
    eexists. done. }
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
  as "(Hdeepown_i & Hother_rep)".
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_i]").
  iIntros (i') "(Hdeepown_i' & Hdeepown_i)". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (uid dq kmeta kspec_o kstatus_o) "H". iNamed "H".
  iPoseProof (kview.own_auth_valid key kobj with "Hinv_Hown_abs") as "%Hin_auth".
  destruct (Hin_auth Hlookup_abs) as [Hkey_eq [Hwf _]].
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag")
    as "(%Hname_eq & %Hns_eq & %Huid_eq & %Hmeta_wf)".
  iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
    as "(%obj & %Hlookup_abs' & %Hmeta_eq & %Huid_in)".
  assert (obj = kobj) as ->.
  { rewrite Hlookup_abs in Hlookup_abs'. inversion Hlookup_abs'. done. }
  destruct kspec_o as [kspec|]; destruct kstatus_o as [kstatus|].
  1, 2: iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found";
        assert (kspec = KObjectV.spec kobj) as Hkspec_eq by
          (symmetry; eapply Hspec_found; [exact Hlookup_abs|];
           rewrite Hmeta_eq; symmetry; exact Huid_eq).
  1, 3: iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found";
        assert (kstatus = KObjectV.status kobj) as Hkstatus_eq by
          (symmetry; eapply Hstatus_found; [exact Hlookup_abs|];
           rewrite Hmeta_eq; symmetry; exact Huid_eq).
  all: iMod ("Hclose" $! i' kobj with "[Hown_meta_frag Hown_spec_frag Hown_status_frag Hdeepown_i']") as "HΦ";
    [iFrame; iPureIntro; split_and!; done|].
  all: iModIntro.
  all: iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
    with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep";
    [iApply "Hother_rep"; iFrame|].
  all: iCombineNamed "Hinv_*" as "H".
  all: wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]");
    [iNamed "H"; iFrame; iFrame "#"; done|].
  all: iApply "HΦ".
Qed.

Lemma wp_State__get_some γ l key uid dq kmeta kspec_o kstatus_o :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec
      | None => True
      end ∗
      "Hown_status_frag" ∷ match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus
      | None => True
      end
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i kobj, RET (#i, #interface.nil);
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      ⌜ kmeta = KObjectV.objectmeta kobj ⌝ ∗
      KObjectV.deepown_i i kobj 1 ∗
      own_meta_frag γ key uid dq kmeta ∗
      match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec ∗ ⌜ kspec = KObjectV.spec kobj ⌝
      | None => True
      end ∗
      match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus ∗ ⌜ kstatus = KObjectV.status kobj ⌝
      | None => True
      end
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__get_some_au.
  iFrame "#". iFrame.
  iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
  iIntros (i kobj) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i kobj with "Hpost").
Qed.

End proof.
