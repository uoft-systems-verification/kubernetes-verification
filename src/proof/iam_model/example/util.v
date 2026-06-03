From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export example_init.
From New.code.iam_model Require Export example.
From iris.algebra Require Import gmap gset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : example.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Definition policy_ids_for_identity
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (identity : iammodel.IdentityID.t) : gmap iammodel.PolicyID.t unit :=
  default (∅ : gmap iammodel.PolicyID.t unit) (abs_identities !! identity).

Lemma wp_identitiesWithPolicyForResource
    identities_l policies_l
    (phys_identities : gmap iammodel.IdentityID.t map.t)
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    resource dq_identities dq_inner dq_policies :
  {{{ "#Hpkg" ∷ is_pkg_init example ∗
      "Hidentities" ∷ identities_l ↦${dq_identities} phys_identities ∗
      "Hidentities_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities, policy_ids_l ↦${dq_inner} policy_ids) ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies
  }}}
    @! example.identitiesWithPolicyForResource
      #identities_l #policies_l #resource
  {{{ sl identity_list, RET #sl;
      "Hidentities" ∷ identities_l ↦${dq_identities} phys_identities ∗
      "Hidentities_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities, policy_ids_l ↦${dq_inner} policy_ids) ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies ∗
      "Hsl" ∷ sl ↦* identity_list ∗
      "%Hidentity_list_nodup" ∷ ⌜ NoDup identity_list ⌝ ∗
      "%Hidentity_list_dom" ∷ ⌜
        list_to_set (C:=gset iammodel.IdentityID.t) identity_list =
        dom (filter (λ '(_, policy_ids),
          attached_policies_for_resource policies policy_ids resource ≠ ∅)
          abs_identities) ⌝
  }}}.
(* FIXME: Proving this needs reusable map.for_range support, including nested
   map iteration through hasPolicyForResource. *)
Proof. Admitted.

Lemma wp_policiesForResource
    identities_l policies_l
    (phys_identities : gmap iammodel.IdentityID.t map.t)
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    identity resource dq_identities dq_inner dq_policies :
  {{{ "#Hpkg" ∷ is_pkg_init example ∗
      "Hidentities" ∷ identities_l ↦${dq_identities} phys_identities ∗
      "Hidentities_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities, policy_ids_l ↦${dq_inner} policy_ids) ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies
  }}}
    @! example.policiesForResource
      #identities_l #policies_l #identity #resource
  {{{ sl policy_id_list, RET #sl;
      "Hidentities" ∷ identities_l ↦${dq_identities} phys_identities ∗
      "Hidentities_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities, policy_ids_l ↦${dq_inner} policy_ids) ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies ∗
      "Hsl" ∷ sl ↦* policy_id_list ∗
      "%Hpolicy_id_list_nodup" ∷ ⌜ NoDup policy_id_list ⌝ ∗
      "%Hpolicy_id_list_dom" ∷ ⌜
        list_to_set (C:=gset iammodel.PolicyID.t) policy_id_list =
        attached_policies_for_resource policies
          (policy_ids_for_identity abs_identities identity) resource ⌝
  }}}.
(* FIXME: Proving this needs reusable map.for_range support for enumerating
   the selected identity's policy-id map. *)
Proof. Admitted.

Lemma wp_missingIdentities
    desired_l current_sl
    (desired : gmap iammodel.IdentityID.t unit)
    (current : list iammodel.IdentityID.t)
    dq_desired dq_current :
  {{{ "#Hpkg" ∷ is_pkg_init example ∗
      "Hdesired" ∷ desired_l ↦${dq_desired} desired ∗
      "Hcurrent" ∷ current_sl ↦*{dq_current} current
  }}}
    @! example.missingIdentities #desired_l #current_sl
  {{{ missing_sl missing, RET #missing_sl;
      "Hdesired" ∷ desired_l ↦${dq_desired} desired ∗
      "Hcurrent" ∷ current_sl ↦*{dq_current} current ∗
      "Hmissing" ∷ missing_sl ↦* missing ∗
      "%Hmissing_nodup" ∷ ⌜ NoDup missing ⌝ ∗
      "%Hmissing_dom" ∷ ⌜
        list_to_set (C:=gset iammodel.IdentityID.t) missing =
        dom desired ∖ list_to_set (C:=gset iammodel.IdentityID.t) current ⌝
  }}}.
(* FIXME: Proving this needs reusable map.for_range support for enumerating
   the desired-identity map while preserving key-set and NoDup facts. *)
Proof. Admitted.

End proof.
