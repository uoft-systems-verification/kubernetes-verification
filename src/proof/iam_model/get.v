From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export common.

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
Proof.
  iIntros (Φ) "(#Hiam & Hpolicy) HΦ".
  iDestruct "Hiam" as (mu_l) "[#Hmu #Hiam_inv]".
  wp_method_call. rewrite /iammodel.State__GetIdentityPolicyⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock;
    [iFrame "#"; iEval (rewrite is_pkg_init_unfold /=);
     iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iDestruct (own_policies_auth_frag_lookup with "Hinv_Hown_policies_auth Hpolicy")
    as %Hpolicy_lookup.
  rewrite exception_do_unseal /exception_do_def.
  wp_apply (wp_map_lookup2 iammodel.PolicyID iammodel.IdentityPolicy
    with "[$Hinv_Hown_phys_policies]") as "Hinv_Hown_phys_policies".
  rewrite Hpolicy_lookup /=.
  wp_auto.
  iCombineNamed "Hinv_*" as "H".
  rewrite return_val_unseal /return_val_def. wp_auto.
  wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#%".
    iEval (rewrite is_pkg_init_unfold /=).
    iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]. }
  iApply "HΦ". iFrame.
Unshelve.
  all: unfold iammodel.PolicyID.t; apply _.
Qed.

End proof.
