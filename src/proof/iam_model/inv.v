Require Export New.proof.sync.
From New.code Require Export iam_model.
From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model.algebra Require Export ghost_map_wrapper.
From New.proof.iam_model.algebra Require Export reversed_identity_policy.

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

Definition own_identities_auth γ (identities : identity_map) : iProp Σ :=
  own_identity_auth γ.(γ_identities) identities.

Definition own_identity γ (identity : iammodel.IdentityID.t) : iProp Σ :=
  ∃ policy_ids, own_identity_frag γ.(γ_identities) identity policy_ids.

Definition own_policies_auth γ (policies : policy_map) : iProp Σ :=
  own_policy_auth γ.(γ_policies) policies.

Definition own_policy γ (policy_id : iammodel.PolicyID.t) : iProp Σ :=
  ∃ policy, own_policy_frag γ.(γ_policies) policy_id policy.

Definition own_resource_access_auth γ
    (identities : identity_map) (policies : policy_map)
    (observed_resources : gset iammodel.ResourceName.t) : iProp Σ :=
  own_reversed_identity_policy_auth γ.(γ_resource_access)
    identities policies observed_resources.

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
    "Hidentities" ∷ own_identities_auth γ phys_identities ∗
    "Hpolicies" ∷ own_policies_auth γ phys_policies ∗
    "Hresource_access" ∷
      own_resource_access_auth γ phys_identities phys_policies observed_resources ∗
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

Global Instance own_identities_auth_timeless γ identities :
  Timeless (own_identities_auth γ identities).
Proof. unfold own_identities_auth. apply _. Qed.

Global Instance own_identity_timeless γ identity :
  Timeless (own_identity γ identity).
Proof. unfold own_identity. apply _. Qed.

Global Instance own_identity_persistent γ identity :
  Persistent (own_identity γ identity).
Proof. unfold own_identity. apply _. Qed.

Global Instance own_policies_auth_timeless γ policies :
  Timeless (own_policies_auth γ policies).
Proof. unfold own_policies_auth. apply _. Qed.

Global Instance own_policy_timeless γ policy_id :
  Timeless (own_policy γ policy_id).
Proof. unfold own_policy. apply _. Qed.

Global Instance own_policy_persistent γ policy_id :
  Persistent (own_policy γ policy_id).
Proof. unfold own_policy. apply _. Qed.

Global Instance own_resource_access_auth_timeless γ identities policies observed_resources :
  Timeless (own_resource_access_auth γ identities policies observed_resources).
Proof. unfold own_resource_access_auth. apply _. Qed.

End inv.
