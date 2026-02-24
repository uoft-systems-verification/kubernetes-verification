From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG KKey.t (KKey.t * types.UID.t) KObjectV.t obj_parent_ref obj_ref Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma wp_State__get γ l key:
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
Proof. Admitted.

Lemma wp_State__get_none γ l key uid:
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

Lemma wp_State__get_some_au γ l key:
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ uid dq kmeta kspec_o kstatus_o i kobj,
      ⌜ uid = kmeta.(ObjectMetaV.UID') ⌝ ∗
      own_meta_frag γ key uid dq kmeta ∗
      match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec
      | None => True
      end ∗
      match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus
      | None => True
      end ∗
      ( ⌜ KObjectV.valid kobj ⌝ ∗
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
          ={∅,⊤}=∗ Φ (#i, #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "get" #key {{ Φ }}.
Proof. Admitted.

End proof.
