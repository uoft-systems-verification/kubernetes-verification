From New.proof Require Import prelude.
From New.ghost Require Import ghost_map.
From New.proof.iam_model Require Export aliases.
From iris.bi.lib Require Import fractional.

Section ghost_map_wrapper.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.
Context `{!allG Σ}.

Definition own_identities_auth γ (identities : identity_map) : iProp Σ :=
  ghost_map_auth (K:=iammodel.IdentityID.t) (V:=gmap iammodel.PolicyID.t unit) γ 1 identities.

Definition own_identity_frag
    γ (identity : iammodel.IdentityID.t) q (policy_ids : gmap iammodel.PolicyID.t unit) : iProp Σ :=
  ghost_map_elem (K:=iammodel.IdentityID.t) (V:=gmap iammodel.PolicyID.t unit)
    γ identity (DfracOwn q) policy_ids.

Definition own_policies_auth γ (policies : policy_map) : iProp Σ :=
  ghost_map_auth (K:=iammodel.PolicyID.t) (V:=iammodel.IdentityPolicy.t) γ 1 policies.

Definition own_policy_frag
    γ (policy_id : iammodel.PolicyID.t) q (policy : iammodel.IdentityPolicy.t) : iProp Σ :=
  ghost_map_elem (K:=iammodel.PolicyID.t) (V:=iammodel.IdentityPolicy.t)
    γ policy_id (DfracOwn q) policy.

Global Instance own_identities_auth_timeless γ identities :
  Timeless (own_identities_auth γ identities).
Proof. unfold own_identities_auth. apply _. Qed.

Global Instance own_identity_frag_timeless γ identity q policy_ids :
  Timeless (own_identity_frag γ identity q policy_ids).
Proof. unfold own_identity_frag. apply _. Qed.

Global Instance own_identity_frag_fractional γ identity policy_ids :
  Fractional (λ q, own_identity_frag γ identity q policy_ids)%I.
Proof. unfold own_identity_frag. apply _. Qed.

Global Instance own_identity_frag_as_fractional γ identity q policy_ids :
  AsFractional (own_identity_frag γ identity q policy_ids)
    (λ q, own_identity_frag γ identity q policy_ids)%I q.
Proof. split; [done|apply _]. Qed.

Global Instance own_policies_auth_timeless γ policies :
  Timeless (own_policies_auth γ policies).
Proof. unfold own_policies_auth. apply _. Qed.

Global Instance own_policy_frag_timeless γ policy_id q policy :
  Timeless (own_policy_frag γ policy_id q policy).
Proof. unfold own_policy_frag. apply _. Qed.

Global Instance own_policy_frag_fractional γ policy_id policy :
  Fractional (λ q, own_policy_frag γ policy_id q policy)%I.
Proof. unfold own_policy_frag. apply _. Qed.

Global Instance own_policy_frag_as_fractional γ policy_id q policy :
  AsFractional (own_policy_frag γ policy_id q policy)
    (λ q, own_policy_frag γ policy_id q policy)%I q.
Proof. split; [done|apply _]. Qed.

Lemma own_identities_auth_frag_lookup {γ identities identity q policy_ids} :
  own_identities_auth γ identities -∗
  own_identity_frag γ identity q policy_ids -∗
  ⌜ identities !! identity = Some policy_ids ⌝.
Proof.
  unfold own_identities_auth, own_identity_frag.
  iIntros "Hauth Hfrag".
  iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
  done.
Qed.

Lemma own_policies_auth_frag_lookup {γ policies policy_id q policy} :
  own_policies_auth γ policies -∗
  own_policy_frag γ policy_id q policy -∗
  ⌜ policies !! policy_id = Some policy ⌝.
Proof.
  unfold own_policies_auth, own_policy_frag.
  iIntros "Hauth Hfrag".
  iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
  done.
Qed.

Lemma own_policy_insert_vs {γ policies policy_id policy} :
  policies !! policy_id = None →
  own_policies_auth γ policies ==∗
    own_policies_auth γ (<[policy_id := policy]> policies) ∗
    own_policy_frag γ policy_id 1 policy.
Proof.
  unfold own_policies_auth, own_policy_frag.
  iIntros (Hfresh) "Hauth".
  iMod (ghost_map_insert policy_id policy with "Hauth") as "[$ $]"; done.
Qed.

End ghost_map_wrapper.
