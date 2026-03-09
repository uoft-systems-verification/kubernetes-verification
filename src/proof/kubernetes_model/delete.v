From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma wp_State__delete_au γ l key uid_ptr uid_o rv_ptr rv_o (reserved: bool):
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    match uid_o with
    | Some uid => uid_ptr ↦ uid
    | None => ⌜ uid_ptr = null ⌝
    end ∗
    match rv_o with
    | Some rv => rv_ptr ↦ rv
    | None => ⌜ rv_ptr = null ⌝
    end ∗
    ( |={⊤,∅}=> ∃ child_uid kmeta parent_key parent_uid children err kmeta',
      ⌜key ∈ children⌝ ∗
      own_meta_frag γ key child_uid 1 kmeta ∗
      own_children_frag γ parent_key parent_uid 1 children ∗
      ( (* delete succeeds as uid and rv matches *)
        ⌜match uid_o with
        | Some uid => uid = child_uid
        | None => True
        end⌝ ∗
        ⌜match rv_o with
        | Some rv => rv = ObjectMetaV.ResourceVersion' kmeta
        | None => True
        end⌝ ∗ 
        ⌜err = interface.nil⌝ ∗
        ( (* the object is marked as deleting (DeletionTimestamp is set) but still exists *)
          ⌜ObjectMetaV.deleting kmeta kmeta'⌝ ∗
          own_meta_frag γ key child_uid 1 kmeta' ∗
          own_children_frag γ parent_key parent_uid 1 children
          ∨
          (* the object is deleted *)
          own_tombstone_frag γ child_uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
        )
        ∨
        (* delete fails as uid or rv doesn't match *)
        (⌜∃ uid, uid_o = Some uid ∧ uid ≠ child_uid⌝ ∨ ⌜∃ rv, rv_o = Some rv ∧ rv ≠ ObjectMetaV.ResourceVersion' kmeta⌝) ∗
        ⌜err ≠ interface.nil⌝ ∗
        own_meta_frag γ key child_uid 1 kmeta ∗
        own_children_frag γ parent_key parent_uid 1 children
          ={∅,⊤}=∗ Φ (# err)
      )
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "delete" #key #uid_ptr #rv_ptr {{ Φ }}.
Proof. Admitted.

End proof.
