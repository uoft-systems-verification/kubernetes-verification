From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

(* TODO: have a more informative spec that specifies in which case the object is deleted from the state map *)
Lemma wp_State__delete_au γ l key options_c options:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
    ( |={⊤,∅}=> ∃ uid kmeta parent_key parent_uid children,
      "%Hkey_in" ∷ ⌜key ∈ children⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ ( ∀ err kmeta',
        (* delete succeeds as uid and rv matches *)
        ⌜ delete_preconditions_match kmeta options ⌝ ∗
        ⌜err = interface.nil⌝ ∗
        ( (* the object is marked as deleting (DeletionTimestamp is set) but still exists *)
          ⌜kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None⌝ ∗
          own_meta_frag γ key uid 1 kmeta' ∗
          own_children_frag γ parent_key parent_uid 1 children
          ∨
          (* the object is deleted *)
          own_tombstone_frag γ uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
        )
        ∨
        (* delete fails as the delete preconditions do not match *)
        ⌜ ¬ delete_preconditions_match kmeta options ⌝ ∗
        ⌜err ≠ interface.nil⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_children_frag γ parent_key parent_uid 1 children
          ={∅,⊤}=∗ ▷ Φ (# err)
      )
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "delete" #key #options_c {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
Admitted.

Lemma wp_State__delete γ l key options_c options uid kmeta parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #options_c
  {{{ err kmeta', RET #err;
      ( ⌜ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ( ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
          own_meta_frag γ key uid 1 kmeta' ∗
          own_children_frag γ parent_key parent_uid 1 children
          ∨
          own_tombstone_frag γ uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
        )
      ∨
        ⌜ ¬ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_children_frag γ parent_key parent_uid 1 children
      )
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__delete_au.
  iFrame "#". iFrame.
  iApply fupd_mask_intro; [set_solver|iIntros "Hmask"].
  iSplit. 1: done.
  iIntros (err kmeta') "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! err kmeta' with "Hpost").
Qed.

End proof.
