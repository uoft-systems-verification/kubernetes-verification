From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG KKey.t (KKey.t * types.UID.t) KObjectV.t obj_parent_ref obj_ref Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma wp_State__create_nameless_au γ l kind namespace i kobj parent_key parent_uid:
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    ⌜ KObjectV.valid_nameless_create kind namespace kobj ⌝ ∗
    ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    KObjectV.deepown_i i kobj 1 ∗
    |={⊤,∅}=> ∃ dq children,
      own_children_frag γ parent_key parent_uid dq children ∗
      ( ∀ i' kobj' key uid,
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ ObjectMetaV.nameless_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
        ⌜ key = (KObjectV.key kobj') ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
        own_children_frag γ parent_key parent_uid dq (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅
          ={∅,⊤}=∗ ▷ Φ (#i', #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i {{ Φ }}.
Proof. Admitted.

Lemma wp_State__create_nameless γ l kind namespace i kobj parent_key parent_uid dq children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_nameless_create kind namespace kobj ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hpr" ∷ ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid dq children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' key uid, RET (#i', #interface.nil);
      ⌜ KObjectV.valid kobj' ⌝ ∗
      ⌜ ObjectMetaV.nameless_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
      ⌜ key = (KObjectV.key kobj') ⌝ ∗
      ⌜ key ∉ children ⌝ ∗
      ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      KObjectV.deepown_i i' kobj' 1 ∗
      own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
      own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
      own_children_frag γ parent_key parent_uid dq (children ∪ {[key]}) ∗
      own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__create_nameless_au.
  iFrame "#". iFrame. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
  iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
  iIntros (i' kobj' key uid) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i' kobj' key uid with "Hpost").
Qed.

End proof.