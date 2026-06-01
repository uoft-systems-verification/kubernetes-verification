Require Export New.proof.sync.
From New.code Require Export iam_model.
Require Export New.generatedproof.iam_model.
From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model.algebra Require Export ghost_map_wrapper.
From New.proof.iam_model.algebra Require Export policy_attachment.
From iris.bi.lib Require Import fractional.

Class iamModelG Σ := {
  #[global] iam_model_allG :: allG Σ;
  #[global] iam_model_resource_accessG :: iamResourceAccessG Σ;
}.

Record IamGname := mk_γiam {
  γ_identities : gname;
  γ_policies : gname;
  γ_resource_access : gname;
}.

Section inv.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

#[local]
Instance policy_id_set_zero_val : ZeroVal policy_id_set :=
  {| zero_val := ∅ |}.

Definition own_iam_identities_auth γ (identities : identity_map) : iProp Σ :=
  own_identities_auth γ.(γ_identities) identities.

Definition own_iam_identity_frag
    γ (identity : iammodel.IdentityID.t) q (policy_ids : gmap iammodel.PolicyID.t unit) : iProp Σ :=
  own_identity_frag γ.(γ_identities) identity q policy_ids.

Definition own_iam_policies_auth γ (policies : policy_map) : iProp Σ :=
  own_policies_auth γ.(γ_policies) policies.

Definition own_iam_policy_frag
    γ (policy_id : iammodel.PolicyID.t) q (policy : iammodel.IdentityPolicy.t) : iProp Σ :=
  own_policy_frag γ.(γ_policies) policy_id q policy.

Definition own_iam_attachments_auth γ
    (identities : identity_map) (policies : policy_map)
    (observed_resources : gset iammodel.ResourceName.t) : iProp Σ :=
  own_attachments_auth γ.(γ_resource_access)
    identities policies observed_resources.

Definition own_iam_attachments_frag
    γ (resource : iammodel.ResourceName.t) dq
    (resource_identities : gmap iammodel.IdentityID.t nat) : iProp Σ :=
  own_attachments_frag γ.(γ_resource_access) resource dq resource_identities.

Definition iam_inv γ l : iProp Σ :=
  ∃ (phys_identities_l : loc) (phys_policies_l : loc)
    (phys_used_policy_ids_l : loc)
    (phys_identities : identity_map)
    (phys_policies : policy_map)
    (phys_used_policy_ids : policy_id_set)
    (observed_resources : gset iammodel.ResourceName.t),
    "Hstate_identities_addr" ∷ l.[(iammodel.State.t), "identities"] ↦ phys_identities_l ∗
    "Hstate_policies_addr" ∷ l.[(iammodel.State.t), "policies"] ↦ phys_policies_l ∗
    "Hstate_used_policy_ids_addr" ∷
      l.[(iammodel.State.t), "usedPolicyIds"] ↦ phys_used_policy_ids_l ∗
    "Hown_phys_identities" ∷ phys_identities_l ↦$ phys_identities ∗
    "Hown_phys_policies" ∷ phys_policies_l ↦$ phys_policies ∗
    "Hown_phys_used_policy_ids" ∷ phys_used_policy_ids_l ↦$ phys_used_policy_ids ∗
    "Hown_identities_auth" ∷ own_iam_identities_auth γ phys_identities ∗
    "Hown_policies_auth" ∷ own_iam_policies_auth γ phys_policies ∗
    "Hown_attachments_auth" ∷
      own_iam_attachments_auth γ phys_identities phys_policies observed_resources ∗
    "%Hattached_policy_exists" ∷ ⌜ ∀ identity policy_ids policy_id,
      phys_identities !! identity = Some policy_ids →
      policy_ids !! policy_id = Some tt →
      ∃ policy, phys_policies !! policy_id = Some policy ⌝ ∗
    "%Hexisting_policy_used" ∷ ⌜ ∀ policy_id policy,
      phys_policies !! policy_id = Some policy →
      phys_used_policy_ids !! policy_id = Some tt ⌝.

Definition is_iam γ l : iProp Σ :=
  ∃ (mu_l : loc),
    "Hmu" ∷ l.[(iammodel.State.t), "mu"] ↦□ mu_l ∗
    "Hiam_inv" ∷ is_Mutex mu_l (iam_inv γ l).

Global Instance own_iam_identities_auth_timeless γ identities :
  Timeless (own_iam_identities_auth γ identities).
Proof. unfold own_iam_identities_auth. apply _. Qed.

Global Instance own_iam_identity_frag_timeless γ identity q policy_ids :
  Timeless (own_iam_identity_frag γ identity q policy_ids).
Proof. unfold own_iam_identity_frag. apply _. Qed.

Global Instance own_iam_identity_frag_fractional γ identity policy_ids :
  Fractional (λ q, own_iam_identity_frag γ identity q policy_ids)%I.
Proof. unfold own_iam_identity_frag. apply _. Qed.

Global Instance own_iam_identity_frag_as_fractional γ identity q policy_ids :
  AsFractional (own_iam_identity_frag γ identity q policy_ids)
    (λ q, own_iam_identity_frag γ identity q policy_ids)%I q.
Proof. split; [done|apply _]. Qed.

Global Instance own_iam_policies_auth_timeless γ policies :
  Timeless (own_iam_policies_auth γ policies).
Proof. unfold own_iam_policies_auth. apply _. Qed.

Global Instance own_iam_policy_frag_timeless γ policy_id q policy :
  Timeless (own_iam_policy_frag γ policy_id q policy).
Proof. unfold own_iam_policy_frag. apply _. Qed.

Global Instance own_iam_policy_frag_fractional γ policy_id policy :
  Fractional (λ q, own_iam_policy_frag γ policy_id q policy)%I.
Proof. unfold own_iam_policy_frag. apply _. Qed.

Global Instance own_iam_policy_frag_as_fractional γ policy_id q policy :
  AsFractional (own_iam_policy_frag γ policy_id q policy)
    (λ q, own_iam_policy_frag γ policy_id q policy)%I q.
Proof. split; [done|apply _]. Qed.

Global Instance own_iam_attachments_auth_timeless γ identities policies observed_resources :
  Timeless (own_iam_attachments_auth γ identities policies observed_resources).
Proof. unfold own_iam_attachments_auth. apply _. Qed.

Global Instance own_iam_attachments_frag_timeless γ resource dq resource_identities :
  Timeless (own_iam_attachments_frag γ resource dq resource_identities).
Proof. unfold own_iam_attachments_frag. apply _. Qed.

End inv.
