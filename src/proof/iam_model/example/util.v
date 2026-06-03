From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
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

Definition identity_has_policy_for_resource
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (resource : iammodel.ResourceName.t)
    (identity : iammodel.IdentityID.t) : bool :=
  match abs_identities !! identity with
  | Some policy_ids =>
      bool_decide (attached_policies_for_resource policies policy_ids resource ≠ ∅)
  | None => false
  end.

Lemma attached_policies_for_resource_elem
    policies policy_ids resource policy_id :
  policy_id ∈ attached_policies_for_resource policies policy_ids resource ↔
  policy_ids !! policy_id = Some tt ∧
  policy_matches_resource policies resource policy_id = true.
Proof.
  unfold attached_policies_for_resource.
  rewrite elem_of_dom.
  split.
  - intros [[] Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hlookup Hmatches].
    split; done.
  - intros [Hlookup Hmatches].
    exists tt. apply map_lookup_filter_Some. split; done.
Qed.

Lemma attached_policies_for_resource_empty
    policies policy_ids resource :
  (∀ policy_id,
    policy_ids !! policy_id = Some tt →
    policy_matches_resource policies resource policy_id = false) →
  attached_policies_for_resource policies policy_ids resource = ∅.
Proof.
  intros Hnone. apply set_eq. intros policy_id.
  rewrite elem_of_empty attached_policies_for_resource_elem.
  split; [|done].
  intros [Hlookup Hmatches].
  rewrite (Hnone policy_id Hlookup) in Hmatches. done.
Qed.

Lemma current_key_not_in_take `{EqDecision A} `{Countable A} (keys : list A) i key :
  NoDup keys →
  keys !! Z.to_nat i = Some key →
  (0 ≤ i)%Z →
  key ∉ list_to_set (C:=gset A) (take (Z.to_nat i) keys).
Proof.
  intros Hnodup Hlookup Hi_nonneg Hin.
  rewrite elem_of_list_to_set in Hin.
  apply list_elem_of_lookup_1 in Hin as [j Htake_lookup].
  apply lookup_take_Some in Htake_lookup as [Hlookup_j Hj].
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_j Hlookup) as ->.
  lia.
Qed.

Lemma filtered_key_list_dom
    (keys : list iammodel.IdentityID.t)
    (phys_identities : gmap iammodel.IdentityID.t map.t)
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    policies resource :
  list_to_set keys = dom phys_identities →
  dom phys_identities = dom abs_identities →
  list_to_set (C:=gset iammodel.IdentityID.t)
    (filter (λ identity,
      identity_has_policy_for_resource abs_identities policies resource identity)
      keys) =
  dom (filter (λ '(_, policy_ids),
    attached_policies_for_resource policies policy_ids resource ≠ ∅)
    abs_identities).
Proof.
  intros Hkeys_dom Hdom_eq.
  apply set_eq. intros identity.
  rewrite elem_of_list_to_set elem_of_dom.
  split.
  - intros Hin.
    apply list_elem_of_filter in Hin as [Hmatches Hidentity_keys].
    unfold identity_has_policy_for_resource in Hmatches.
    destruct (abs_identities !! identity) as [policy_ids|] eqn:Hlookup;
      [|done].
    destruct (bool_decide
      (attached_policies_for_resource policies policy_ids resource ≠ ∅))
      eqn:Hmatches_eq; [|done].
    apply bool_decide_eq_true in Hmatches_eq.
    exists policy_ids. apply map_lookup_filter_Some. split; done.
  - intros [policy_ids Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hlookup Hnonempty].
    apply list_elem_of_filter. split.
    + unfold identity_has_policy_for_resource. rewrite Hlookup.
      destruct (bool_decide_reflect
        (attached_policies_for_resource policies policy_ids resource ≠ ∅));
        done.
    + assert (identity ∈ list_to_set (C:=gset iammodel.IdentityID.t) keys)
        as Hin_keys.
      { rewrite Hkeys_dom Hdom_eq elem_of_dom.
        eexists. exact Hlookup. }
      rewrite elem_of_list_to_set in Hin_keys. exact Hin_keys.
Qed.

Lemma wp_hasPolicyForResource
    policy_ids_l policies_l
    (policy_ids : gmap iammodel.PolicyID.t unit)
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    resource dq_policy_ids dq_policies :
  {{{ "#Hpkg" ∷ is_pkg_init example ∗
      "HpolicyIDs" ∷ policy_ids_l ↦${dq_policy_ids} policy_ids ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies
  }}}
    @! example.hasPolicyForResource #policy_ids_l #policies_l #resource
  {{{ RET #(bool_decide
        (attached_policies_for_resource policies policy_ids resource ≠ ∅));
      "HpolicyIDs" ∷ policy_ids_l ↦${dq_policy_ids} policy_ids ∗
      "Hpolicies" ∷ policies_l ↦${dq_policies} policies
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  wp_apply (wp_map_for_range_return_or_return (key_type:=iammodel.PolicyID)
    (λ (keys : list iammodel.PolicyID.t) i,
      ∃ (policy_id : iammodel.PolicyID.t),
        "Hpolicies" ∷ policies_l ↦${dq_policies} policies ∗
        "resource" ∷ resource_ptr ↦ resource ∗
        "policies" ∷ policies_ptr ↦ policies_l ∗
        "policyID" ∷ policyID_ptr ↦ policy_id ∗
        "%Hprocessed" ∷ ⌜ ∀ policy_id',
          policy_id' ∈ list_to_set (C:=gset iammodel.PolicyID.t)
            (take (Z.to_nat i) keys) →
          policy_matches_resource policies resource policy_id' = false ⌝)%I
    (λ bv,
      ∃ (policy_id : iammodel.PolicyID.t),
        "Hpolicies" ∷ policies_l ↦${dq_policies} policies ∗
        "resource" ∷ resource_ptr ↦ resource ∗
        "policies" ∷ policies_ptr ↦ policies_l ∗
        "policyID" ∷ policyID_ptr ↦ policy_id ∗
        "%Hreturn" ∷ ⌜ bv = return_val #true ∧
          attached_policies_for_resource policies policy_ids resource ≠ ∅ ⌝)%I
    with "HpolicyIDs").
  iIntros (keys) "%Hkeys".
  iSplitL "Hpolicies resource policies policyID".
  { iExists ""%go. iFrame. iPureIntro.
    rewrite take_0 list_to_set_nil. intros ? Hin.
    rewrite elem_of_empty in Hin. done. }
  iSplitL "".
  { iModIntro. iIntros (i policy_id []) "%Hiter Hbody".
    destruct Hiter as [Hi_bounds [Hkey_lookup Hpolicy_id_lookup]].
    iDestruct "Hbody" as (last_policy_id)
      "(Hpolicies & resource & policies & policyID & %Hprocessed)".
    wp_auto.
    wp_apply (wp_map_lookup2 iammodel.PolicyID iammodel.IdentityPolicy
      with "[$Hpolicies]").
    iIntros "Hpolicies".
    destruct (policies !! policy_id) as [policy|] eqn:Hpolicy_lookup;
      wp_auto.
    - destruct (decide
        (policy.(iammodel.IdentityPolicy.Resource') = resource)) as
        [Hresource_eq|Hresource_ne].
      + replace (bool_decide
          (policy.(iammodel.IdentityPolicy.Resource') = resource)) with true.
        2:{ symmetry. apply bool_decide_eq_true_2. done. }
        wp_auto.
        iRight. iRight. iExists #true. iSplit; [done|].
        iExists policy_id. iFrame. iPureIntro. split; [done|].
        intros Hempty.
        assert (policy_id ∈ attached_policies_for_resource
          policies policy_ids resource) as Hin.
        { apply attached_policies_for_resource_elem.
          split; [exact Hpolicy_id_lookup|].
          unfold policy_matches_resource. rewrite Hpolicy_lookup.
          apply bool_decide_eq_true_2. done. }
        rewrite Hempty elem_of_empty in Hin. done.
      + replace (bool_decide
          (policy.(iammodel.IdentityPolicy.Resource') = resource)) with false.
        2:{ symmetry. apply bool_decide_eq_false_2. done. }
        wp_auto.
        iRight. iLeft. iSplit; [done|].
        iExists policy_id. iFrame. iPureIntro.
        intros policy_id' Hin.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hin by lia.
        rewrite (take_S_r _ _ _ Hkey_lookup) in Hin.
        rewrite elem_of_list_to_set elem_of_app /= in Hin.
        destruct Hin as [Hin|Hin].
        * apply Hprocessed. rewrite elem_of_list_to_set. exact Hin.
        * rewrite elem_of_cons elem_of_nil in Hin.
          destruct Hin as [Heq|[]]. subst policy_id'.
          unfold policy_matches_resource. rewrite Hpolicy_lookup.
          apply bool_decide_eq_false_2. done.
    - iRight. iLeft. iSplit; [done|].
      iExists policy_id. iFrame. iPureIntro.
      intros policy_id' Hin.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hin by lia.
      rewrite (take_S_r _ _ _ Hkey_lookup) in Hin.
      rewrite elem_of_list_to_set elem_of_app /= in Hin.
      destruct Hin as [Hin|Hin].
      * apply Hprocessed. rewrite elem_of_list_to_set. exact Hin.
      * rewrite elem_of_cons elem_of_nil in Hin.
        destruct Hin as [Heq|[]]. subst policy_id'.
        unfold policy_matches_resource. rewrite Hpolicy_lookup. done.
      }
  iIntros (bv) "HpolicyIDs Hresult".
  iDestruct "Hresult" as "[Hdone|Hreturn]".
  - iDestruct "Hdone" as "(-> & Hdone)".
    iDestruct "Hdone" as (last_policy_id)
      "(Hpolicies & resource & policies & policyID & %Hprocessed)".
    assert (attached_policies_for_resource policies policy_ids resource = ∅)
      as Hempty.
    { apply attached_policies_for_resource_empty.
      intros policy_id Hlookup.
      apply Hprocessed.
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      rewrite Nat2Z.id.
      replace (size policy_ids) with (length keys) by done.
      replace (take (length keys) keys) with keys.
      2:{ symmetry. apply take_ge. apply Nat.le_refl. }
      rewrite Hkeys_dom elem_of_dom. eexists. exact Hlookup. }
    wp_auto.
    replace (#false) with
      (#(bool_decide
        (attached_policies_for_resource policies policy_ids resource ≠ ∅))).
    2:{ f_equal. apply bool_decide_eq_false_2.
        rewrite Hempty. intros Hneq. apply Hneq. done. }
    iApply "HΦ". iFrame.
  - iDestruct "Hreturn" as (policy_id)
      "(Hpolicies & resource & policies & policyID & %Hreturn)".
    destruct Hreturn as [-> Hnonempty].
    wp_auto.
    replace (#true) with
      (#(bool_decide
        (attached_policies_for_resource policies policy_ids resource ≠ ∅))).
    2:{ f_equal. apply bool_decide_eq_true_2. done. }
    iApply "HΦ". iFrame.
  Unshelve.
    all: unfold iammodel.PolicyID.t, iammodel.IdentityID.t; apply _.
Qed.

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
(* FIXME: This callback uses Goose's generated "$value" range temporary.
   Ordinary function application substitutes the binder "value", leaving
   "$value" free in the callback body. A sound proof needs either generated
   callbacks that bind "$value", or a map.for_range semantics/principle that
   explicitly accounts for this Goose convention. *)
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
