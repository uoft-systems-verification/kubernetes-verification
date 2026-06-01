From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__CreatePolicy γ l resource :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "%Hresource_nonempty" ∷ ⌜ resource ≠ ""%go ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "CreatePolicy" #resource
  {{{ policy_id, RET (#policy_id, #interface.nil);
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id 1
        (iammodel.IdentityPolicy.mk policy_id resource)
  }}}.
Proof. Admitted.

End proof.
