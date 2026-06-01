From New.proof Require Import prelude.
From New.ghost Require Import ghost_map.
From New.proof.iam_model Require Export aliases.

Section ghost_map_wrapper.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.
Context `{!allG Σ}.

Definition own_identity_auth γ (identities : identity_set) : iProp Σ :=
  ghost_map_auth (K:=iammodel.IdentityID.t) (V:=unit)
    γ 1 (gset_to_gmap tt identities).

Definition own_identity_frag
    γ (identity : iammodel.IdentityID.t) : iProp Σ :=
  ghost_map_elem (K:=iammodel.IdentityID.t) (V:=unit)
    γ identity DfracDiscarded tt.

Definition own_policy_auth γ (policies : policy_map) : iProp Σ :=
  ghost_map_auth (K:=iammodel.PolicyID.t) (V:=iammodel.IdentityPolicy.t) γ 1 policies.

Definition own_policy_frag
    γ (policy_id : iammodel.PolicyID.t) (policy : iammodel.IdentityPolicy.t) : iProp Σ :=
  ghost_map_elem (K:=iammodel.PolicyID.t) (V:=iammodel.IdentityPolicy.t)
    γ policy_id DfracDiscarded policy.

Global Instance own_identity_auth_timeless γ identities :
  Timeless (own_identity_auth γ identities).
Proof. unfold own_identity_auth. apply _. Qed.

Global Instance own_identity_frag_timeless γ identity :
  Timeless (own_identity_frag γ identity).
Proof. unfold own_identity_frag. apply _. Qed.

Global Instance own_identity_frag_persistent γ identity :
  Persistent (own_identity_frag γ identity).
Proof. unfold own_identity_frag. apply _. Qed.

Global Instance own_policy_auth_timeless γ policies :
  Timeless (own_policy_auth γ policies).
Proof. unfold own_policy_auth. apply _. Qed.

Global Instance own_policy_frag_timeless γ policy_id policy :
  Timeless (own_policy_frag γ policy_id policy).
Proof. unfold own_policy_frag. apply _. Qed.

Global Instance own_policy_frag_persistent γ policy_id policy :
  Persistent (own_policy_frag γ policy_id policy).
Proof. unfold own_policy_frag. apply _. Qed.

Lemma own_identity_auth_frag_lookup {γ identities identity} :
  own_identity_auth γ identities -∗
  own_identity_frag γ identity -∗
  ⌜ identity ∈ identities ⌝.
Proof.
  unfold own_identity_auth, own_identity_frag.
  iIntros "Hauth Hfrag".
  iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
  iPureIntro.
  apply lookup_gset_to_gmap_Some in Hlookup as [Hidentity _].
  exact Hidentity.
Qed.

Lemma own_policy_auth_frag_lookup {γ policies policy_id policy} :
  own_policy_auth γ policies -∗
  own_policy_frag γ policy_id policy -∗
  ⌜ policies !! policy_id = Some policy ⌝.
Proof.
  unfold own_policy_auth, own_policy_frag.
  iIntros "Hauth Hfrag".
  iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hlookup.
  done.
Qed.

Lemma own_policy_insert_vs {γ policies policy_id policy} :
  policies !! policy_id = None →
  own_policy_auth γ policies ==∗
    own_policy_auth γ (<[policy_id := policy]> policies) ∗
    own_policy_frag γ policy_id policy.
Proof.
  unfold own_policy_auth, own_policy_frag.
  iIntros (Hfresh) "Hauth".
  iMod (ghost_map_insert_persist policy_id policy with "Hauth") as "[$ $]"; done.
Qed.

End ghost_map_wrapper.
