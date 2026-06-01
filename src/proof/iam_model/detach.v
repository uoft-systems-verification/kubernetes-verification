From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__DetachIdentityPolicy
    γ l identity policy_ids policy_id policy resource attachments q :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "%Hattached" ∷ ⌜ policy_ids !! policy_id = Some tt ⌝ ∗
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 policy_ids ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments ∗
      "%Hresource_eq" ∷ ⌜ resource = policy.(iammodel.IdentityPolicy.Resource') ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "DetachIdentityPolicy" #identity #policy_id
  {{{ attachments', RET #interface.nil;
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 (delete policy_id policy_ids) ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments' ∗
      "%Hattachments_other" ∷ ⌜ ∀ identity',
        identity' ≠ identity →
        attachments' !! identity' = attachments !! identity' ⌝ ∗
      "%Hattachments_identity" ∷ ⌜
        (attachments !! identity = Some 1%nat ∧
          attachments' !! identity = None) ∨
        ∃ n, attachments !! identity = Some n ∧
          (2 ≤ n)%nat ∧
          attachments' !! identity = Some (n - 1)%nat ⌝
  }}}.
Proof. Admitted.

End proof.
