From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__AttachIdentityPolicy
    γ l identity policy_ids policy_id policy resource attachments q :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 policy_ids ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments ∗
      "%Hresource_eq" ∷ ⌜ resource = policy.(iammodel.IdentityPolicy.Resource') ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "AttachIdentityPolicy" #identity #policy_id
  {{{ n, RET #interface.nil;
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 (<[policy_id := tt]> policy_ids) ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 (<[identity := n]> attachments) ∗
      "%Hn_positive" ∷ ⌜ (1 ≤ n)%nat ⌝
  }}}.
Proof. Admitted.

End proof.
