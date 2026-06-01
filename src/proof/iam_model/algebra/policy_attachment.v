From New.proof Require Import prelude.
From iris.algebra Require Import gmap gset.
From New.code Require Export iam_model.
From New.proof.algebra Require Export counted_reversed_reference.

Module IamRef.

Inductive t :=
| IdentityRef (identity : iammodel.IdentityID.t)
| ResourceRef (resource : iammodel.ResourceName.t).

#[global]
Instance eq_dec : EqDecision t.
Proof. solve_decision. Qed.

#[global]
Instance countable : Countable t.
Proof.
  refine (inj_countable'
    (λ ref,
      match ref with
      | IdentityRef identity => (false, identity)
      | ResourceRef resource => (true, resource)
      end)
    (λ '(tag, name),
      if tag then ResourceRef name else IdentityRef name)
    _).
  intros [identity|resource]; reflexivity.
Qed.

End IamRef.

#[local]
Instance resource_ref_inj : Inj (=) (=) IamRef.ResourceRef.
Proof.
  intros resource1 resource2 Heq.
  inversion Heq. done.
Qed.

Section attachment_defs.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition identity_ref
    (identity : iammodel.IdentityID.t) (_ : gmap iammodel.ResourceName.t nat) : IamRef.t :=
  IamRef.IdentityRef identity.

Definition policy_matches_resource
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (resource : iammodel.ResourceName.t) (policy_id : iammodel.PolicyID.t) : bool :=
  match policies !! policy_id with
  | Some policy => bool_decide (policy.(iammodel.IdentityPolicy.Resource') = resource)
  | None => false
  end.

Definition attached_policies_for_resource
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (policy_ids : gmap iammodel.PolicyID.t unit)
    (resource : iammodel.ResourceName.t) : gset iammodel.PolicyID.t :=
  dom (filter (λ '(policy_id, _),
    policy_matches_resource policies resource policy_id = true) policy_ids).

Definition policy_resources
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t) :
    gset iammodel.ResourceName.t :=
  list_to_set (C:=gset iammodel.ResourceName.t)
    ((λ policy, policy.(iammodel.IdentityPolicy.Resource')) <$> (map_to_list policies).*2).

Definition resources_for_identity_counts
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (policy_ids : gmap iammodel.PolicyID.t unit)
    : gmap iammodel.ResourceName.t nat :=
  list_to_map ((λ resource,
    (resource, size (attached_policies_for_resource policies policy_ids resource))) <$>
    elements (policy_resources policies)).

Definition attachment_state
    (identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t) :
    gmap iammodel.IdentityID.t (gmap iammodel.ResourceName.t nat) :=
  map_imap (λ _ policy_ids, Some (resources_for_identity_counts policies policy_ids))
    identities.

Definition attachment_used_reference_set
    (identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (observed_resources : gset iammodel.ResourceName.t) : gset IamRef.t :=
  set_map IamRef.IdentityRef (dom identities) ∪
  set_map IamRef.ResourceRef observed_resources.

Definition resource_count_refs
    (resources : gmap iammodel.ResourceName.t nat) : gmap IamRef.t nat :=
  kmap (M1:=gmap iammodel.ResourceName.t) (M2:=gmap IamRef.t)
    IamRef.ResourceRef resources.

Definition attachment_ref_counts
    (identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (ref : IamRef.t) : gmap iammodel.IdentityID.t nat :=
  @counted_reversed_reference.reverse_index
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs
    (attachment_state identities policies) ref.

Definition attachment_counts
    (identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (resource : iammodel.ResourceName.t) : gmap iammodel.IdentityID.t nat :=
  attachment_ref_counts identities policies (IamRef.ResourceRef resource).

Local Lemma policy_matches_resource_other
    policies policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  policy_matches_resource policies resource' policy_id = false.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold policy_matches_resource.
  rewrite Hpolicy Hresource.
  apply bool_decide_eq_false_2.
  intros Heq. apply Hneq. symmetry. done.
Qed.

Local Lemma attached_policies_for_resource_insert_other
    policies policy_ids policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource' =
  attached_policies_for_resource policies policy_ids resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold attached_policies_for_resource.
  f_equal.
  apply map_eq. intros policy_id'.
  destruct (decide (policy_id' = policy_id)) as [->|Hne_policy].
  - pose proof (policy_matches_resource_other
      policies policy_id policy resource resource' Hpolicy Hresource Hneq) as Hmatch.
    assert (Hnew_none :
      filter
        (λ '(policy_id0, _),
          policy_matches_resource policies resource' policy_id0 = true)
        (<[policy_id:=tt]> policy_ids) !! policy_id = None).
    { apply map_lookup_filter_None_2. right.
      intros [] _ Hmatches. rewrite Hmatch in Hmatches. done. }
    assert (Hold_none :
      filter
        (λ '(policy_id0, _),
          policy_matches_resource policies resource' policy_id0 = true)
        policy_ids !! policy_id = None).
    { apply map_lookup_filter_None_2.
      destruct (policy_ids !! policy_id) as [[]|] eqn:Hlookup; [right|left; done].
      intros [] Hlookup' Hmatches.
      inversion Hlookup'. subst.
      rewrite Hmatch in Hmatches. done. }
    rewrite Hnew_none Hold_none. done.
  - rewrite !map_lookup_filter.
    rewrite lookup_insert_ne; done.
Qed.

Local Lemma resources_for_identity_counts_entries_nodup policies policy_ids :
  NoDup (((λ resource,
    (resource, size (attached_policies_for_resource policies policy_ids resource))) <$>
    elements (policy_resources policies)).*1).
Proof.
  rewrite -list_fmap_compose /=.
  rewrite list_fmap_id.
  apply NoDup_elements.
Qed.

Local Lemma resources_for_identity_counts_insert_other
    policies policy_ids policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  resources_for_identity_counts policies (<[policy_id := tt]> policy_ids) !! resource' =
  resources_for_identity_counts policies policy_ids !! resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold resources_for_identity_counts.
  destruct (list_to_map
    ((λ resource0,
      (resource0,
       size (attached_policies_for_resource policies (<[policy_id:=tt]> policy_ids) resource0)))
      <$> elements (policy_resources policies)) !! resource') as [n|] eqn:Hnew.
  - apply elem_of_list_to_map_2 in Hnew as Hin.
    apply list_elem_of_fmap in Hin as (resource0 & Hpair & Hin).
    inversion Hpair. subst resource0 n.
    symmetry.
    apply elem_of_list_to_map_1.
    + apply resources_for_identity_counts_entries_nodup.
    + apply list_elem_of_fmap.
      exists resource'. split; [|done].
      simpl. f_equal.
      pose proof (attached_policies_for_resource_insert_other
        policies policy_ids policy_id policy resource resource'
        Hpolicy Hresource Hneq) as Hattached.
      rewrite Hattached.
      done.
  - destruct (list_to_map
      ((λ resource0,
        (resource0, size (attached_policies_for_resource policies policy_ids resource0)))
        <$> elements (policy_resources policies)) !! resource') as [n|] eqn:Hold; [|done].
    exfalso.
    apply elem_of_list_to_map_2 in Hold as Hin.
    apply list_elem_of_fmap in Hin as (resource0 & Hpair & Hin).
    inversion Hpair. subst resource0 n.
    assert (Hnew_some :
      (list_to_map
        ((λ resource0,
          (resource0,
           size (attached_policies_for_resource policies
             (<[policy_id:=tt]> policy_ids) resource0)))
          <$> elements (policy_resources policies)) : gmap iammodel.ResourceName.t nat) !! resource' =
      Some (size (attached_policies_for_resource policies
        (<[policy_id:=tt]> policy_ids) resource'))).
    { apply elem_of_list_to_map_1.
      - apply resources_for_identity_counts_entries_nodup.
      - apply list_elem_of_fmap.
        exists resource'. split; [done|done]. }
    rewrite Hnew in Hnew_some. discriminate.
Qed.

Local Lemma policy_resource_elem policies policy_id policy :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') ∈ policy_resources policies.
Proof.
  intros Hpolicy.
  unfold policy_resources.
  apply elem_of_list_to_set, list_elem_of_fmap.
  exists policy. split; [done|].
  apply list_elem_of_fmap.
  exists (policy_id, policy). split; [done|].
  rewrite elem_of_map_to_list. exact Hpolicy.
Qed.

Local Lemma resources_for_identity_counts_lookup policies policy_ids resource :
  resource ∈ policy_resources policies →
  resources_for_identity_counts policies policy_ids !! resource =
  Some (size (attached_policies_for_resource policies policy_ids resource)).
Proof.
  intros Hresource.
  unfold resources_for_identity_counts.
  apply elem_of_list_to_map_1.
  - apply resources_for_identity_counts_entries_nodup.
  - apply list_elem_of_fmap.
    exists resource. split; [done|].
    apply elem_of_elements. exact Hresource.
Qed.

Local Lemma attached_policies_for_resource_not_policy_resource
    policies policy_ids resource :
  resource ∉ policy_resources policies →
  attached_policies_for_resource policies policy_ids resource = ∅.
Proof.
  intros Hresource.
  apply elem_of_equiv_empty_L. intros policy_id Hin.
  unfold attached_policies_for_resource in Hin.
  apply elem_of_dom in Hin as [[] Hlookup].
  apply map_lookup_filter_Some in Hlookup as [Hpolicy_id Hmatches].
  unfold policy_matches_resource in Hmatches.
  destruct (policies !! policy_id) as [policy|] eqn:Hpolicy; [|done].
  apply bool_decide_eq_true in Hmatches.
  apply Hresource.
  rewrite -Hmatches.
  apply policy_resource_elem with policy_id. exact Hpolicy.
Qed.

Local Lemma resources_for_identity_counts_lookup_default
    policies policy_ids resource :
  default 0%nat (resources_for_identity_counts policies policy_ids !! resource) =
  size (attached_policies_for_resource policies policy_ids resource).
Proof.
  destruct (decide (resource ∈ policy_resources policies)) as [Hresource|Hresource].
  - rewrite resources_for_identity_counts_lookup; done.
  - assert (Hlookup_none :
      resources_for_identity_counts policies policy_ids !! resource = None).
    { unfold resources_for_identity_counts.
      destruct (list_to_map
        ((λ resource0,
          (resource0,
           size (attached_policies_for_resource policies policy_ids resource0)))
          <$> elements (policy_resources policies)) !! resource) as [n|] eqn:Hlookup;
        [|done].
      exfalso.
      apply Hresource.
      apply elem_of_list_to_map_2 in Hlookup as Hin.
      apply list_elem_of_fmap in Hin as (resource0 & Hpair & Hin).
      inversion Hpair. subst resource0.
      apply elem_of_elements. done. }
    rewrite Hlookup_none /=.
    rewrite (attached_policies_for_resource_not_policy_resource
      policies policy_ids resource Hresource).
    rewrite size_empty. done.
Qed.

Local Lemma attached_policies_for_resource_not_elem
    policies policy_ids resource policy_id :
  policy_ids !! policy_id = None →
  policy_id ∉ attached_policies_for_resource policies policy_ids resource.
Proof.
  intros Hlookup Hin.
  unfold attached_policies_for_resource in Hin.
  apply elem_of_dom in Hin as [[] Hfilter].
  apply map_lookup_filter_Some in Hfilter as [Hlookup' _].
  rewrite Hlookup in Hlookup'. done.
Qed.

Local Lemma attached_policies_for_resource_insert_policy_unattached
    policies policy_ids policy_id policy resource :
  policy_ids !! policy_id = None →
  attached_policies_for_resource (<[policy_id := policy]> policies) policy_ids resource =
  attached_policies_for_resource policies policy_ids resource.
Proof.
  intros Hfresh.
  unfold attached_policies_for_resource.
  f_equal.
  apply map_eq. intros policy_id'.
  rewrite !map_lookup_filter.
  destruct (policy_ids !! policy_id') as [[]|] eqn:Hpolicy_id'; simpl; [|done].
  destruct (decide (policy_id' = policy_id)) as [->|Hne].
  - rewrite Hfresh in Hpolicy_id'. done.
  - unfold policy_matches_resource.
    rewrite lookup_insert_ne; done.
Qed.

Local Lemma resources_for_identity_counts_insert_policy_reference_count
    policies policy_ids policy_id policy ref :
  policy_ids !! policy_id = None →
  @counted_reversed_reference.reference_count
    IamRef.t _ _ (gmap iammodel.ResourceName.t nat) resource_count_refs
    (resources_for_identity_counts (<[policy_id := policy]> policies) policy_ids) ref =
  @counted_reversed_reference.reference_count
    IamRef.t _ _ (gmap iammodel.ResourceName.t nat) resource_count_refs
    (resources_for_identity_counts policies policy_ids) ref.
Proof.
  intros Hfresh.
  destruct ref as [identity|resource].
  - unfold counted_reversed_reference.reference_count.
    assert (Hnew_none :
      resource_count_refs
        (resources_for_identity_counts (<[policy_id:=policy]> policies) policy_ids)
        !! IamRef.IdentityRef identity = None).
    { unfold resource_count_refs. apply lookup_kmap_None.
      - apply _.
      - intros resource Href. discriminate Href. }
    assert (Hold_none :
      resource_count_refs
        (resources_for_identity_counts policies policy_ids)
        !! IamRef.IdentityRef identity = None).
    { unfold resource_count_refs. apply lookup_kmap_None.
      - apply _.
      - intros resource Href. discriminate Href. }
    rewrite Hnew_none Hold_none. done.
  - unfold counted_reversed_reference.reference_count, resource_count_refs.
    rewrite !lookup_kmap.
    rewrite !resources_for_identity_counts_lookup_default.
    rewrite attached_policies_for_resource_insert_policy_unattached; done.
Qed.

Local Lemma attachment_ref_counts_insert_policy_unattached
    identities policies policy_id policy ref :
  (∀ identity policy_ids,
    identities !! identity = Some policy_ids →
    policy_ids !! policy_id = None) →
  attachment_ref_counts identities (<[policy_id := policy]> policies) ref =
  attachment_ref_counts identities policies ref.
Proof.
  intros Hunattached.
  apply map_eq. intros identity.
  unfold attachment_ref_counts, counted_reversed_reference.reverse_index,
    attachment_state.
  rewrite !map_lookup_imap.
  destruct (identities !! identity) as [policy_ids|] eqn:Hidentity.
  2:{ done. }
  simpl.
  rewrite !(resources_for_identity_counts_insert_policy_reference_count
    policies policy_ids policy_id policy ref).
  - apply Hunattached with identity. done.
  - done.
Qed.

Local Lemma attached_policies_for_resource_insert_same
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource =
  attached_policies_for_resource policies policy_ids resource ∪ {[policy_id]}.
Proof.
  intros Hpolicy Hresource.
  unfold attached_policies_for_resource.
  rewrite map_filter_insert_True.
  - simpl. unfold policy_matches_resource.
    rewrite Hpolicy Hresource.
    apply bool_decide_eq_true_2. done.
  - rewrite dom_insert_L. Timeout 10 set_solver.
Qed.

Local Lemma attached_policies_for_resource_insert_same_size
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = None →
  size (attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource) =
  S (size (attached_policies_for_resource policies policy_ids resource)).
Proof.
  intros Hpolicy Hresource Hlookup.
  rewrite (attached_policies_for_resource_insert_same
    policies policy_ids policy_id policy resource Hpolicy Hresource).
  rewrite size_union.
  - rewrite disjoint_singleton_r.
    apply attached_policies_for_resource_not_elem. exact Hlookup.
  - rewrite size_singleton. lia.
Qed.

Local Lemma resources_for_identity_counts_insert_same_lookup
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = None →
  resources_for_identity_counts policies (<[policy_id := tt]> policy_ids) !! resource =
  Some (S (size (attached_policies_for_resource policies policy_ids resource))).
Proof.
  intros Hpolicy Hresource Hlookup.
  rewrite resources_for_identity_counts_lookup.
  - rewrite -Hresource. apply policy_resource_elem with policy_id. exact Hpolicy.
  - rewrite (attached_policies_for_resource_insert_same_size
      policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup).
    done.
Qed.

Local Lemma resource_count_refs_identity_ref_none resources identity :
  resource_count_refs resources !! IamRef.IdentityRef identity = None.
Proof.
  unfold resource_count_refs.
  apply lookup_kmap_None.
  - apply _.
  - intros resource Heq.
    discriminate Heq.
Qed.

Local Lemma resource_count_refs_insert_policy_other
    policies policy_ids policy_id policy resource ref :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  resource_count_refs
    (resources_for_identity_counts policies (<[policy_id := tt]> policy_ids)) !! ref =
  resource_count_refs
    (resources_for_identity_counts policies policy_ids) !! ref.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct ref as [identity|resource'].
  - rewrite !resource_count_refs_identity_ref_none. done.
  - rewrite /resource_count_refs !lookup_kmap.
    apply (resources_for_identity_counts_insert_other
      policies policy_ids policy_id policy resource resource'); [done|done|].
    intros Heq. apply Hneq. subst resource'. done.
Qed.

Local Lemma attach_identity_policy_other_refs
    identities policies identity policy_ids policy_id policy resource ref :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  attachment_ref_counts
    (<[identity := <[policy_id := tt]> policy_ids]> identities) policies ref =
  attachment_ref_counts identities policies ref.
Proof.
  intros Hidentity Hpolicy Hresource Hneq.
  apply map_eq. intros identity'.
  unfold attachment_ref_counts,
    counted_reversed_reference.reverse_index,
    attachment_state.
  rewrite !map_lookup_imap.
  destruct (decide (identity' = identity)) as [->|Hne_identity].
  - rewrite lookup_insert_eq Hidentity /=.
    unfold counted_reversed_reference.reference_count.
    pose proof (resource_count_refs_insert_policy_other
      policies policy_ids policy_id policy resource ref
      Hpolicy Hresource Hneq) as Hrefs.
    rewrite Hrefs.
    done.
  - rewrite lookup_insert_ne; [|done].
    destruct (identities !! identity'); done.
Qed.

Local Lemma attach_identity_policy_counts_lookup_same
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = None →
  attachment_counts
    (<[identity := <[policy_id := tt]> policy_ids]> identities) policies resource
    !! identity =
  Some (S (default 0%nat
    (attachment_counts identities policies resource !! identity))).
Proof.
  intros Hidentity Hpolicy Hresource Hlookup.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hresource_elem.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap lookup_insert_eq /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap.
  rewrite (resources_for_identity_counts_insert_same_lookup
    policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup).
  rewrite Hidentity /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap.
  rewrite resources_for_identity_counts_lookup.
  - rewrite -Hresource. exact Hresource_elem.
  - destruct (decide (0 <
      S (size (attached_policies_for_resource policies policy_ids resource)))%nat)
      as [_|Hnew]; [|lia].
    destruct (decide (0 <
      size (attached_policies_for_resource policies policy_ids resource))%nat)
      as [Hold|Hold]; simpl.
    + destruct (decide (0 <
        size (attached_policies_for_resource policies policy_ids resource))%nat)
        as [_|Hcontra]; [done|contradiction].
    + destruct (decide (0 <
        size (attached_policies_for_resource policies policy_ids resource))%nat)
        as [Hcontra|_]; [contradiction|simpl; f_equal; lia].
Qed.

Local Lemma attach_identity_policy_counts_lookup_other
    identities policies identity policy_ids policy_id resource identity' :
  identity' ≠ identity →
  attachment_counts
    (<[identity := <[policy_id := tt]> policy_ids]> identities) policies resource
    !! identity' =
  attachment_counts identities policies resource !! identity'.
Proof.
  intros Hne.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap.
  rewrite lookup_insert_ne; [|done].
  destruct (identities !! identity'); done.
Qed.

Local Lemma attached_policies_for_resource_insert_elem
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_id ∈
    attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource.
Proof.
  intros Hpolicy Hresource.
  unfold attached_policies_for_resource.
  apply elem_of_dom. exists tt.
  apply map_lookup_filter_Some. split.
  - rewrite lookup_insert_eq. done.
  - simpl. unfold policy_matches_resource.
    rewrite Hpolicy Hresource.
    apply bool_decide_eq_true_2. done.
Qed.

Local Lemma attached_policies_for_resource_insert_size_pos
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (0 < size
    (attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource))%nat.
Proof.
  intros Hpolicy Hresource.
  pose proof (attached_policies_for_resource_insert_elem
    policies policy_ids policy_id policy resource Hpolicy Hresource) as Hin.
  destruct (decide (size
    (attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource)
    = 0%nat)) as [Hempty|Hnonempty].
  - apply size_empty_inv in Hempty.
    rewrite Hempty in Hin. set_solver.
  - lia.
Qed.

Local Lemma resources_for_identity_counts_insert_lookup_positive
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ∃ n,
    resources_for_identity_counts policies (<[policy_id := tt]> policy_ids) !! resource =
      Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hpolicy Hresource.
  exists (size
    (attached_policies_for_resource policies (<[policy_id := tt]> policy_ids) resource)).
  split.
  - apply resources_for_identity_counts_lookup.
    rewrite -Hresource. apply policy_resource_elem with policy_id. exact Hpolicy.
  - pose proof (attached_policies_for_resource_insert_size_pos
      policies policy_ids policy_id policy resource Hpolicy Hresource).
    lia.
Qed.

Local Lemma attach_identity_policy_counts_lookup_positive
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ∃ n,
    attachment_counts
      (<[identity := <[policy_id := tt]> policy_ids]> identities) policies resource
      !! identity = Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hidentity Hpolicy Hresource.
  destruct (resources_for_identity_counts_insert_lookup_positive
    policies policy_ids policy_id policy resource Hpolicy Hresource)
    as (n & Hlookup & Hpositive).
  exists n. split; [|done].
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap lookup_insert_eq /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap Hlookup /=.
  destruct (decide (0 < n)%nat) as [_|Hnot_positive]; [done|lia].
Qed.

Local Lemma attach_identity_policy_counts_insert
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = None →
  attachment_counts
    (<[identity := <[policy_id := tt]> policy_ids]> identities) policies resource =
  <[identity := S (default 0%nat
    (attachment_counts identities policies resource !! identity))]>
    (attachment_counts identities policies resource).
Proof.
  intros Hidentity Hpolicy Hresource Hlookup.
  apply map_eq. intros identity'.
  destruct (decide (identity' = identity)) as [->|Hne].
  - rewrite lookup_insert_eq.
    apply (attach_identity_policy_counts_lookup_same
      identities policies identity policy_ids policy_id policy resource); done.
  - rewrite (attach_identity_policy_counts_lookup_other
      identities policies identity policy_ids policy_id resource identity' Hne).
    symmetry. apply lookup_insert_ne.
    intros Heq. apply Hne. symmetry. exact Heq.
Qed.

Local Lemma attached_policies_for_resource_delete_other
    policies policy_ids policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  attached_policies_for_resource policies (delete policy_id policy_ids) resource' =
  attached_policies_for_resource policies policy_ids resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold attached_policies_for_resource.
  f_equal.
  apply map_eq. intros policy_id'.
  destruct (decide (policy_id' = policy_id)) as [->|Hne_policy].
  - pose proof (policy_matches_resource_other
      policies policy_id policy resource resource' Hpolicy Hresource Hneq) as Hmatch.
    assert (Hdelete_none :
      filter
        (λ '(policy_id0, _),
          policy_matches_resource policies resource' policy_id0 = true)
        (delete policy_id policy_ids) !! policy_id = None).
    { apply map_lookup_filter_None_2. left. rewrite lookup_delete_eq. done. }
    assert (Hold_none :
      filter
        (λ '(policy_id0, _),
          policy_matches_resource policies resource' policy_id0 = true)
        policy_ids !! policy_id = None).
    { apply map_lookup_filter_None_2.
      destruct (policy_ids !! policy_id) as [[]|] eqn:Hlookup; [right|left; done].
      intros [] Hlookup' Hmatches.
      inversion Hlookup'. subst.
      rewrite Hmatch in Hmatches. done. }
    rewrite Hdelete_none Hold_none. done.
  - rewrite !map_lookup_filter.
    rewrite lookup_delete_ne; done.
Qed.

Local Lemma resources_for_identity_counts_delete_other
    policies policy_ids policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  resources_for_identity_counts policies (delete policy_id policy_ids) !! resource' =
  resources_for_identity_counts policies policy_ids !! resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold resources_for_identity_counts.
  destruct (list_to_map
    ((λ resource0,
      (resource0,
       size (attached_policies_for_resource policies (delete policy_id policy_ids) resource0)))
      <$> elements (policy_resources policies)) !! resource') as [n|] eqn:Hnew.
  - apply elem_of_list_to_map_2 in Hnew as Hin.
    apply list_elem_of_fmap in Hin as (resource0 & Hpair & Hin).
    inversion Hpair. subst resource0 n.
    symmetry.
    apply elem_of_list_to_map_1.
    + apply resources_for_identity_counts_entries_nodup.
    + apply list_elem_of_fmap.
      exists resource'. split; [|done].
      simpl. f_equal.
      pose proof (attached_policies_for_resource_delete_other
        policies policy_ids policy_id policy resource resource'
        Hpolicy Hresource Hneq) as Hattached.
      rewrite Hattached. done.
  - destruct (list_to_map
      ((λ resource0,
        (resource0, size (attached_policies_for_resource policies policy_ids resource0)))
        <$> elements (policy_resources policies)) !! resource') as [n|] eqn:Hold; [|done].
    exfalso.
    apply elem_of_list_to_map_2 in Hold as Hin.
    apply list_elem_of_fmap in Hin as (resource0 & Hpair & Hin).
    inversion Hpair. subst resource0 n.
    assert (Hnew_some :
      (list_to_map
        ((λ resource0,
          (resource0,
           size (attached_policies_for_resource policies
             (delete policy_id policy_ids) resource0)))
          <$> elements (policy_resources policies)) : gmap iammodel.ResourceName.t nat) !! resource' =
      Some (size (attached_policies_for_resource policies
        (delete policy_id policy_ids) resource'))).
    { apply elem_of_list_to_map_1.
      - apply resources_for_identity_counts_entries_nodup.
      - apply list_elem_of_fmap.
        exists resource'. split; [done|done]. }
    rewrite Hnew in Hnew_some. discriminate.
Qed.

Local Lemma resource_count_refs_delete_policy_other
    policies policy_ids policy_id policy resource ref :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  resource_count_refs
    (resources_for_identity_counts policies (delete policy_id policy_ids)) !! ref =
  resource_count_refs
    (resources_for_identity_counts policies policy_ids) !! ref.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct ref as [identity|resource'].
  - rewrite !resource_count_refs_identity_ref_none. done.
  - rewrite /resource_count_refs !lookup_kmap.
    apply (resources_for_identity_counts_delete_other
      policies policy_ids policy_id policy resource resource'); [done|done|].
    intros Heq. apply Hneq. subst resource'. done.
Qed.

Local Lemma detach_identity_policy_other_refs
    identities policies identity policy_ids policy_id policy resource ref :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  attachment_ref_counts
    (<[identity := delete policy_id policy_ids]> identities) policies ref =
  attachment_ref_counts identities policies ref.
Proof.
  intros Hidentity Hpolicy Hresource Hneq.
  apply map_eq. intros identity'.
  unfold attachment_ref_counts,
    counted_reversed_reference.reverse_index,
    attachment_state.
  rewrite !map_lookup_imap.
  destruct (decide (identity' = identity)) as [->|Hne_identity].
  - rewrite lookup_insert_eq Hidentity /=.
    unfold counted_reversed_reference.reference_count.
    pose proof (resource_count_refs_delete_policy_other
      policies policy_ids policy_id policy resource ref
      Hpolicy Hresource Hneq) as Hrefs.
    rewrite Hrefs.
    done.
  - rewrite lookup_insert_ne; [|done].
    destruct (identities !! identity'); done.
Qed.

Local Lemma detach_identity_policy_counts_lookup_other
    identities policies identity policy_ids policy_id resource identity' :
  identity' ≠ identity →
  attachment_counts
    (<[identity := delete policy_id policy_ids]> identities) policies resource
    !! identity' =
  attachment_counts identities policies resource !! identity'.
Proof.
  intros Hne.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap.
  rewrite lookup_insert_ne; [|done].
  destruct (identities !! identity'); done.
Qed.

Local Lemma attached_policies_for_resource_elem
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  policy_id ∈ attached_policies_for_resource policies policy_ids resource.
Proof.
  intros Hpolicy Hresource Hlookup.
  unfold attached_policies_for_resource.
  apply elem_of_dom. exists tt.
  apply map_lookup_filter_Some. split; [done|].
  unfold policy_matches_resource.
  rewrite Hpolicy Hresource.
  apply bool_decide_eq_true_2. done.
Qed.

Local Lemma attached_policies_for_resource_size_pos
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  (0 < size (attached_policies_for_resource policies policy_ids resource))%nat.
Proof.
  intros Hpolicy Hresource Hlookup.
  pose proof (attached_policies_for_resource_elem
    policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup) as Hin.
  destruct (decide (size
    (attached_policies_for_resource policies policy_ids resource) = 0%nat))
    as [Hempty|Hnonempty].
  - apply size_empty_inv in Hempty.
    rewrite Hempty in Hin. set_solver.
  - lia.
Qed.

Local Lemma resources_for_identity_counts_attached_lookup_positive
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  ∃ n,
    resources_for_identity_counts policies policy_ids !! resource = Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hpolicy Hresource Hlookup.
  exists (size (attached_policies_for_resource policies policy_ids resource)).
  split.
  - apply resources_for_identity_counts_lookup.
    rewrite -Hresource. apply policy_resource_elem with policy_id. exact Hpolicy.
  - pose proof (attached_policies_for_resource_size_pos
      policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup).
    lia.
Qed.

Local Lemma detach_identity_policy_counts_lookup_positive
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  ∃ n,
    attachment_counts identities policies resource !! identity = Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hidentity Hpolicy Hresource Hlookup.
  destruct (resources_for_identity_counts_attached_lookup_positive
    policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup)
    as (n & Hcount & Hpositive).
  exists n. split; [|done].
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap Hidentity /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap Hcount /=.
  destruct (decide (0 < n)%nat) as [_|Hnot_positive]; [done|lia].
Qed.

Local Lemma attached_policies_for_resource_delete_same
    policies policy_ids policy_id resource :
  attached_policies_for_resource policies (delete policy_id policy_ids) resource =
  attached_policies_for_resource policies policy_ids resource ∖ {[policy_id]}.
Proof.
  unfold attached_policies_for_resource.
  rewrite map_filter_delete.
  rewrite dom_delete_L. done.
Qed.

Local Lemma attached_policies_for_resource_delete_same_size
    policies policy_ids policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  size (attached_policies_for_resource policies (delete policy_id policy_ids) resource) =
  (size (attached_policies_for_resource policies policy_ids resource) - 1)%nat.
Proof.
  intros Hpolicy Hresource Hlookup.
  rewrite attached_policies_for_resource_delete_same.
  rewrite size_difference.
  - pose proof (attached_policies_for_resource_elem
      policies policy_ids policy_id policy resource Hpolicy Hresource Hlookup).
    Timeout 10 set_solver.
  - rewrite size_singleton. lia.
Qed.

Local Lemma detach_identity_policy_counts_lookup_same_decrement
    identities policies identity policy_ids policy_id policy resource n :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  attachment_counts identities policies resource !! identity = Some n →
  (2 ≤ n)%nat →
  attachment_counts
    (<[identity := delete policy_id policy_ids]> identities) policies resource
    !! identity = Some (n - 1)%nat.
Proof.
  intros Hidentity Hpolicy Hresource Hpolicy_id Hcount Hn.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hresource_elem.
  assert (Hold_lookup :
    resources_for_identity_counts policies policy_ids !! resource =
    Some (size (attached_policies_for_resource policies policy_ids resource))).
  { apply resources_for_identity_counts_lookup.
    rewrite -Hresource. exact Hresource_elem. }
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state in Hcount.
  rewrite !map_lookup_imap Hidentity /= in Hcount.
  unfold counted_reversed_reference.reference_count in Hcount.
  rewrite /resource_count_refs lookup_kmap Hold_lookup /= in Hcount.
  destruct (decide (0 <
    size (attached_policies_for_resource policies policy_ids resource))%nat)
    as [Hold_positive|Hold_not_positive]; [|discriminate].
  inversion Hcount. subst n.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap lookup_insert_eq /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap.
  rewrite resources_for_identity_counts_lookup.
  - rewrite -Hresource. exact Hresource_elem.
  - rewrite (attached_policies_for_resource_delete_same_size
      policies policy_ids policy_id policy resource Hpolicy Hresource Hpolicy_id).
    destruct (decide
      (0 <
       (size (attached_policies_for_resource policies policy_ids resource) - 1)%nat)%nat)
      as [Hnew_positive|Hnew_not_positive].
    + rewrite decide_True.
      * exact Hnew_positive.
      * done.
    + lia.
Qed.

Local Lemma detach_identity_policy_counts_lookup_same_delete
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  attachment_counts identities policies resource !! identity = Some 1%nat →
  attachment_counts
    (<[identity := delete policy_id policy_ids]> identities) policies resource
    !! identity = None.
Proof.
  intros Hidentity Hpolicy Hresource Hpolicy_id Hcount.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hresource_elem.
  assert (Hold_lookup :
    resources_for_identity_counts policies policy_ids !! resource =
    Some (size (attached_policies_for_resource policies policy_ids resource))).
  { apply resources_for_identity_counts_lookup.
    rewrite -Hresource. exact Hresource_elem. }
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state in Hcount.
  rewrite !map_lookup_imap Hidentity /= in Hcount.
  unfold counted_reversed_reference.reference_count in Hcount.
  rewrite /resource_count_refs lookup_kmap Hold_lookup /= in Hcount.
  destruct (decide (0 <
    size (attached_policies_for_resource policies policy_ids resource))%nat)
    as [Hold_positive|Hold_not_positive]; [|discriminate].
  inversion Hcount as [Hsize]. clear Hcount.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap lookup_insert_eq /=.
  unfold counted_reversed_reference.reference_count.
  rewrite /resource_count_refs lookup_kmap.
  rewrite resources_for_identity_counts_lookup.
  - rewrite -Hresource. exact Hresource_elem.
  - rewrite (attached_policies_for_resource_delete_same_size
      policies policy_ids policy_id policy resource Hpolicy Hresource Hpolicy_id).
    rewrite Hsize.
    simpl.
    destruct (decide (0 < 0)%nat) as [Hfalse|_]; [lia|done].
Qed.

Local Lemma detach_identity_policy_counts_decrement
    identities policies identity policy_ids policy_id policy resource n :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  attachment_counts identities policies resource !! identity = Some n →
  (2 ≤ n)%nat →
  attachment_counts
    (<[identity := delete policy_id policy_ids]> identities) policies resource =
  <[identity := (n - 1)%nat]>
    (attachment_counts identities policies resource).
Proof.
  intros Hidentity Hpolicy Hresource Hpolicy_id Hcount Hn.
  apply map_eq. intros identity'.
  destruct (decide (identity' = identity)) as [->|Hne].
  - rewrite lookup_insert_eq.
    apply (detach_identity_policy_counts_lookup_same_decrement
      identities policies identity policy_ids policy_id policy resource n); done.
  - rewrite (detach_identity_policy_counts_lookup_other
      identities policies identity policy_ids policy_id resource identity' Hne).
    symmetry. apply lookup_insert_ne.
    intros Heq. apply Hne. symmetry. exact Heq.
Qed.

Local Lemma detach_identity_policy_counts_delete
    identities policies identity policy_ids policy_id policy resource :
  identities !! identity = Some policy_ids →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_ids !! policy_id = Some tt →
  attachment_counts identities policies resource !! identity = Some 1%nat →
  attachment_counts
    (<[identity := delete policy_id policy_ids]> identities) policies resource =
  delete identity (attachment_counts identities policies resource).
Proof.
  intros Hidentity Hpolicy Hresource Hpolicy_id Hcount.
  apply map_eq. intros identity'.
  destruct (decide (identity' = identity)) as [->|Hne].
  - rewrite lookup_delete_eq.
    apply (detach_identity_policy_counts_lookup_same_delete
      identities policies identity policy_ids policy_id policy resource); done.
  - rewrite (detach_identity_policy_counts_lookup_other
      identities policies identity policy_ids policy_id resource identity' Hne).
    symmetry. apply lookup_delete_ne.
    intros Heq. apply Hne. symmetry. exact Heq.
Qed.

Local Lemma attachment_state_identity_refs identities policies observed_resources :
  map_Forall (λ identity resources,
    identity_ref identity resources ∈
      attachment_used_reference_set identities policies observed_resources)
    (attachment_state identities policies).
Proof.
  rewrite map_Forall_lookup.
  intros identity resources Hlookup.
  unfold attachment_state in Hlookup.
  rewrite map_lookup_imap in Hlookup.
  destruct (identities !! identity) as [policy_ids|] eqn:Hidentity.
  2:{ simpl in Hlookup. inversion Hlookup. }
  simpl in Hlookup.
  inversion Hlookup. subst resources.
  unfold identity_ref, attachment_used_reference_set.
  apply elem_of_union_l.
  apply elem_of_map.
  exists identity. split; [done|].
  apply elem_of_dom. eexists. exact Hidentity.
Qed.

Local Lemma attachment_resource_ref_used identities policies observed_resources resource :
  resource ∈ observed_resources →
  IamRef.ResourceRef resource ∈
    attachment_used_reference_set identities policies observed_resources.
Proof.
  intros Hresource.
  unfold attachment_used_reference_set.
  apply elem_of_union_r.
  apply elem_of_map.
  exists resource. split; done.
Qed.

Local Lemma attachment_resource_ref_observed
    identities policies observed_resources resource :
  IamRef.ResourceRef resource ∈
    attachment_used_reference_set identities policies observed_resources →
  resource ∈ observed_resources.
Proof.
  unfold attachment_used_reference_set.
  intros Hused.
  apply elem_of_union in Hused as [Hidentity|Hresource].
  - apply elem_of_map in Hidentity as (identity & Heq & _).
    inversion Heq.
  - apply elem_of_map in Hresource as (resource' & Heq & Hin).
    inversion Heq. subst. done.
Qed.

Class iamResourceAccessG Σ :=
  { #[global] iam_attachment_counted_reversed_referenceG ::
      @counted_reversed_reference.counted_reversed_referenceG
        iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
        resource_count_refs identity_ref Σ; }.

Definition iamResourceAccessΣ :=
  @counted_reversed_reference.counted_reversed_referenceΣ
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref.

#[global]
Instance subG_iamResourceAccessG Σ :
  subG iamResourceAccessΣ Σ → iamResourceAccessG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (@counted_reversed_reference.subG_counted_reversed_referenceG
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref Σ Hsub).
Qed.

Section attachment.
Context `{!iamResourceAccessG Σ}.

Definition own_attachments_auth
    γ (identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t)
    (observed_resources : gset iammodel.ResourceName.t) : iProp Σ :=
  @counted_reversed_reference.own_auth
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _ γ
    (attachment_state identities policies,
     attachment_used_reference_set identities policies observed_resources).

Definition own_attachments_frag
    γ (resource : iammodel.ResourceName.t) dq (identities : gmap iammodel.IdentityID.t nat) : iProp Σ :=
  @counted_reversed_reference.own_frag
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (IamRef.ResourceRef resource) dq identities.

Global Instance own_attachments_auth_timeless
    γ identities policies observed_resources :
  Timeless (own_attachments_auth γ identities policies observed_resources).
Proof. unfold own_attachments_auth. apply _. Qed.

Global Instance own_attachments_frag_timeless γ resource dq identities :
  Timeless (own_attachments_frag γ resource dq identities).
Proof. unfold own_attachments_frag. apply _. Qed.

Lemma own_attachments_frag_valid
    {γ identities policies observed_resources resource dq attachments} :
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource dq attachments -∗
  ⌜ attachments =
      attachment_counts identities policies resource ⌝ ∗
  ⌜ IamRef.ResourceRef resource ∈
      attachment_used_reference_set identities policies observed_resources ⌝.
Proof.
  unfold own_attachments_auth, own_attachments_frag, attachment_counts.
  iIntros "Hauth Hfrag".
  iDestruct (@counted_reversed_reference.own_auth_frag_valid
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (attachment_state identities policies,
       attachment_used_reference_set identities policies observed_resources)
    (IamRef.ResourceRef resource) dq attachments
    with "Hauth Hfrag") as "[%Hidentities %Hused]".
  iPureIntro. split; done.
Qed.

Lemma own_attachments_frag_valid_pure
    {γ identities policies observed_resources resource dq attachments} :
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource dq attachments -∗
  ⌜ attachments =
      attachment_counts identities policies resource ∧
    IamRef.ResourceRef resource ∈
      attachment_used_reference_set identities policies observed_resources ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_attachments_frag_valid with "Hauth Hfrag")
    as "[%Hidentities %Hused]".
  iPureIntro. split; done.
Qed.

Lemma own_attachments_frag_observed
    {γ identities policies observed_resources resource dq attachments} :
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource dq attachments -∗
  ⌜ resource ∈ observed_resources ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_attachments_frag_valid with "Hauth Hfrag")
    as "[_ %Hused]".
  iPureIntro.
  eapply attachment_resource_ref_observed. exact Hused.
Qed.

Lemma own_attachments_frag_lookup_positive {γ resource dq attachments identity n} :
  own_attachments_frag γ resource dq attachments -∗
  ⌜ attachments !! identity = Some n → (1 ≤ n)%nat ⌝.
Proof.
  unfold own_attachments_frag.
  iIntros "Hfrag".
  iDestruct (counted_reversed_reference.own_frag_lookup_positive with "Hfrag")
    as "%Hpositive".
  iPureIntro. intros Hlookup.
  specialize (Hpositive Hlookup). lia.
Qed.

Lemma insert_unattached_policy_vs
    {γ identities policies observed_resources policy_id policy} :
  (∀ identity policy_ids,
    identities !! identity = Some policy_ids →
    policy_ids !! policy_id = None) →
  own_attachments_auth γ identities policies observed_resources ==∗
    own_attachments_auth γ identities
      (<[policy_id := policy]> policies) observed_resources.
Proof.
  iIntros (Hunattached) "Hauth".
  unfold own_attachments_auth.
  iMod (@counted_reversed_reference.generic_update_vs
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (attachment_state identities policies,
       attachment_used_reference_set identities policies observed_resources)
    (attachment_state identities (<[policy_id := policy]> policies),
       attachment_used_reference_set identities
         (<[policy_id := policy]> policies) observed_resources)
    with "Hauth") as "Hauth".
  - apply attachment_state_identity_refs.
  - intros ref Href. exact Href.
  - intros ref _.
    apply attachment_ref_counts_insert_policy_unattached.
    exact Hunattached.
  - iModIntro. iExact "Hauth".
Qed.

Local Lemma update_identity_policy_vs
    {γ identities policies observed_resources identity policy_ids policy_ids'
      resource attachments attachments'} :
  identities !! identity = Some policy_ids →
  attachments' =
    attachment_counts
      (<[identity := policy_ids']> identities) policies resource →
  (∀ ref,
    ref ≠ IamRef.ResourceRef resource →
    attachment_ref_counts
      (<[identity := policy_ids']> identities) policies ref =
      attachment_ref_counts identities policies ref) →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    own_attachments_auth γ
      (<[identity := policy_ids']> identities) policies observed_resources ∗
    own_attachments_frag γ resource 1 attachments'.
Proof.
  iIntros (Hidentity Hidentities Hother_refs) "Hauth Hfrag".
  iPoseProof (own_attachments_frag_observed with "Hauth Hfrag")
    as "%Hresource".
  unfold own_attachments_auth, own_attachments_frag.
  iMod (@counted_reversed_reference.generic_reference_update_vs
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (attachment_state identities policies,
       attachment_used_reference_set identities policies observed_resources)
    (attachment_state (<[identity := policy_ids']> identities) policies,
       attachment_used_reference_set
         (<[identity := policy_ids']> identities) policies observed_resources)
    (IamRef.ResourceRef resource) attachments attachments'
    with "Hauth Hfrag") as "[Hauth Hfrag]".
  - apply attachment_state_identity_refs.
  - apply attachment_resource_ref_used. exact Hresource.
  - symmetry. exact Hidentities.
  - intros ref _ Href.
    assert (Hidentity_dom : identity ∈ dom identities).
    { apply elem_of_dom. eexists. exact Hidentity. }
    assert (Hdom :
      dom (<[identity:=policy_ids']> identities) = dom identities).
    { rewrite dom_insert_L. Timeout 10 set_solver. }
    unfold attachment_used_reference_set in *.
    rewrite Hdom. exact Href.
  - intros ref Hneq _.
    apply Hother_refs. exact Hneq.
  - iModIntro. iFrame.
Qed.

Lemma attach_new_identity_policy_vs
    {γ identities identities' policies observed_resources identity policy_ids policy_id policy
      resource attachments} :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  identities !! identity = Some policy_ids →
  policy_ids !! policy_id = None →
  identities' = <[identity := <[policy_id := tt]> policy_ids]> identities →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    own_attachments_auth γ identities' policies observed_resources ∗
    own_attachments_frag γ resource 1
      (<[identity := S (default 0%nat (attachments !! identity))]>
        attachments).
Proof.
  iIntros (Hpolicy Hpolicy_resource Hidentity Hfresh Hidentity_update)
    "Hauth Hfrag".
  iPoseProof (own_attachments_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hattachments _].
  subst identities'.
  assert (Hidentities :
    <[identity := S (default 0%nat (attachments !! identity))]>
      attachments =
    attachment_counts
      (<[identity := <[policy_id := tt]> policy_ids]> identities)
      policies resource).
  { rewrite Hattachments.
    symmetry.
    apply (attach_identity_policy_counts_insert
      identities policies identity policy_ids policy_id policy resource); done. }
  iMod (update_identity_policy_vs with "Hauth Hfrag")
    as "[Hauth Hfrag]".
  - exact Hidentity.
  - exact Hidentities.
  - intros ref Hneq.
    apply (attach_identity_policy_other_refs
      identities policies identity policy_ids policy_id policy resource ref); done.
  - iModIntro.
    iFrame.
Qed.

Lemma attach_identity_policy_vs
    {γ identities identities' policies observed_resources identity policy_ids policy_id policy
      resource attachments} :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  identities !! identity = Some policy_ids →
  identities' = <[identity := <[policy_id := tt]> policy_ids]> identities →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    ∃ n,
    own_attachments_auth γ identities' policies observed_resources ∗
    own_attachments_frag γ resource 1 (<[identity := n]> attachments) ∗
    ⌜ (1 ≤ n)%nat ⌝.
Proof.
  iIntros (Hpolicy Hpolicy_resource Hidentity Hidentity_update)
    "Hauth Hfrag".
  iPoseProof (own_attachments_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hattachments _].
  subst identities'.
  destruct (attach_identity_policy_counts_lookup_positive
    identities policies identity policy_ids policy_id policy resource
    Hidentity Hpolicy Hpolicy_resource) as (n & Hlookup & Hpositive).
  assert (Hidentities :
    <[identity := n]> attachments =
    attachment_counts
      (<[identity := <[policy_id := tt]> policy_ids]> identities)
      policies resource).
  { rewrite Hattachments.
    apply map_eq. intros identity'.
    destruct (decide (identity' = identity)) as [->|Hne].
    - rewrite lookup_insert_eq. done.
    - assert ((<[identity:=n]> (attachment_counts identities policies resource)) !! identity' =
        attachment_counts identities policies resource !! identity') as Hinsert_lookup.
      { apply lookup_insert_ne. intros Heq. apply Hne. symmetry. exact Heq. }
      rewrite Hinsert_lookup.
      rewrite (attach_identity_policy_counts_lookup_other
        identities policies identity policy_ids policy_id resource identity' Hne).
      done. }
  iMod (update_identity_policy_vs with "Hauth Hfrag")
    as "[Hauth Hfrag]".
  - exact Hidentity.
  - exact Hidentities.
  - intros ref Hneq.
    apply (attach_identity_policy_other_refs
      identities policies identity policy_ids policy_id policy resource ref); done.
  - iModIntro.
    iExists n. iFrame. done.
Qed.

Lemma detach_identity_policy_decrement_vs
    {γ identities identities' policies observed_resources identity policy_ids policy_id policy
      resource attachments n} :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  identities !! identity = Some policy_ids →
  policy_ids !! policy_id = Some tt →
  attachments !! identity = Some n →
  (2 ≤ n)%nat →
  identities' = <[identity := delete policy_id policy_ids]> identities →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    own_attachments_auth γ identities' policies observed_resources ∗
    own_attachments_frag γ resource 1
      (<[identity := (n - 1)%nat]> attachments).
Proof.
  iIntros (Hpolicy Hpolicy_resource Hidentity Hpolicy_id Hcount Hn Hidentity_update)
    "Hauth Hfrag".
  iPoseProof (own_attachments_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hattachments _].
  subst identities'.
  assert (Hidentities :
    <[identity := (n - 1)%nat]> attachments =
    attachment_counts
      (<[identity := delete policy_id policy_ids]> identities)
      policies resource).
  { rewrite Hattachments.
    symmetry.
    apply (detach_identity_policy_counts_decrement
      identities policies identity policy_ids policy_id policy resource n).
    - exact Hidentity.
    - exact Hpolicy.
    - exact Hpolicy_resource.
    - exact Hpolicy_id.
    - rewrite -Hattachments. exact Hcount.
    - exact Hn. }
  iMod (update_identity_policy_vs with "Hauth Hfrag")
    as "[Hauth Hfrag]".
  - exact Hidentity.
  - exact Hidentities.
  - intros ref Hneq.
    apply (detach_identity_policy_other_refs
      identities policies identity policy_ids policy_id policy resource ref); done.
  - iModIntro.
    iFrame.
Qed.

Lemma detach_last_identity_policy_vs
    {γ identities identities' policies observed_resources identity policy_ids policy_id policy
      resource attachments} :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  identities !! identity = Some policy_ids →
  policy_ids !! policy_id = Some tt →
  attachments !! identity = Some 1%nat →
  identities' = <[identity := delete policy_id policy_ids]> identities →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    own_attachments_auth γ identities' policies observed_resources ∗
    own_attachments_frag γ resource 1 (delete identity attachments).
Proof.
  iIntros (Hpolicy Hpolicy_resource Hidentity Hpolicy_id Hcount Hidentity_update)
    "Hauth Hfrag".
  iPoseProof (own_attachments_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hattachments _].
  subst identities'.
  assert (Hidentities :
    delete identity attachments =
    attachment_counts
      (<[identity := delete policy_id policy_ids]> identities)
      policies resource).
  { rewrite Hattachments.
    symmetry.
    apply (detach_identity_policy_counts_delete
      identities policies identity policy_ids policy_id policy resource); [done..|].
    rewrite -Hattachments. exact Hcount. }
  iMod (update_identity_policy_vs with "Hauth Hfrag")
    as "[Hauth Hfrag]".
  - exact Hidentity.
  - exact Hidentities.
  - intros ref Hneq.
    apply (detach_identity_policy_other_refs
      identities policies identity policy_ids policy_id policy resource ref); done.
  - iModIntro.
    iFrame.
Qed.

Lemma detach_identity_policy_vs
    {γ identities identities' policies observed_resources identity policy_ids policy_id policy
      resource attachments} :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  identities !! identity = Some policy_ids →
  policy_ids !! policy_id = Some tt →
  identities' = <[identity := delete policy_id policy_ids]> identities →
  own_attachments_auth γ identities policies observed_resources -∗
  own_attachments_frag γ resource 1 attachments ==∗
    ∃ attachments',
    own_attachments_auth γ identities' policies observed_resources ∗
    own_attachments_frag γ resource 1 attachments' ∗
    ⌜ (attachments !! identity = Some 1%nat ∧
        attachments' = delete identity attachments) ∨
      ∃ n, attachments !! identity = Some n ∧
        (2 ≤ n)%nat ∧
        attachments' = <[identity := (n - 1)%nat]> attachments ⌝.
Proof.
  iIntros (Hpolicy Hpolicy_resource Hidentity Hpolicy_id Hidentity_update)
    "Hauth Hfrag".
  iPoseProof (own_attachments_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hattachments _].
  destruct (detach_identity_policy_counts_lookup_positive
    identities policies identity policy_ids policy_id policy resource
    Hidentity Hpolicy Hpolicy_resource Hpolicy_id)
    as (n & Hcount & Hpositive).
  rewrite -Hattachments in Hcount.
  destruct n as [|n']; [lia|].
  destruct n' as [|n''].
  - iMod (detach_last_identity_policy_vs with "Hauth Hfrag")
      as "[Hauth Hfrag]"; [done..|exact Hcount|exact Hidentity_update|].
    iModIntro. iExists (delete identity attachments). iFrame.
    iPureIntro. left. done.
  - assert ((2 ≤ S (S n''))%nat) as Hn by lia.
    iMod (detach_identity_policy_decrement_vs with "Hauth Hfrag")
      as "[Hauth Hfrag]"; [done..|exact Hcount|exact Hn|exact Hidentity_update|].
    iModIntro. iExists (<[identity := (S (S n'') - 1)%nat]> attachments). iFrame.
    iPureIntro. right. eexists. done.
Qed.

End attachment.

End attachment_defs.
