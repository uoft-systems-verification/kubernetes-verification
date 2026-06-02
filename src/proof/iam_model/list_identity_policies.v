From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.
From iris.algebra Require Import gset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__ListIdentityPolicies γ l identity q policy_ids :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hidentity" ∷ own_iam_identity_frag γ identity q policy_ids
  }}}
    l @! (go.PointerType iammodel.State) @! "ListIdentityPolicies" #identity
  {{{ sl policy_id_list, RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* policy_id_list ∗
      "Hidentity" ∷ own_iam_identity_frag γ identity q policy_ids ∗
      "%Hpolicy_id_list_nodup" ∷ ⌜ NoDup policy_id_list ⌝ ∗
      "%Hpolicy_id_list_dom" ∷ ⌜
        list_to_set (C:=gset iammodel.PolicyID.t) policy_id_list = dom policy_ids ⌝
  }}}.
Proof. Admitted.

End proof.
