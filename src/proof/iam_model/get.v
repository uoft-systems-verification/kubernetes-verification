From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__GetIdentityPolicy γ l policy_id q policy :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy
  }}}
    l @! (go.PointerType iammodel.State) @! "GetIdentityPolicy" #policy_id
  {{{ RET (#policy, #interface.nil);
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy
  }}}.
Proof. Admitted.

End proof.
