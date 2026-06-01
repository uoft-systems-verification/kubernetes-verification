From New.proof Require Import prelude.
From iris.algebra Require Import gmap gset.
From New.proof.iam_model Require Export aliases.
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

Section reversed_identity_policy_defs.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition identity_ref
    (identity : iammodel.IdentityID.t) (_ : gmap iammodel.ResourceName.t nat) : IamRef.t :=
  IamRef.IdentityRef identity.

Definition policy_matches_resource
    (policies : policy_map) (resource : iammodel.ResourceName.t)
    (policy_id : iammodel.PolicyID.t) : bool :=
  match policies !! policy_id with
  | Some policy => bool_decide (policy.(iammodel.IdentityPolicy.Resource') = resource)
  | None => false
  end.

Definition attachment_matches_resource
    (policies : policy_map) (identity : iammodel.IdentityID.t)
    (resource : iammodel.ResourceName.t) (a : attachment) : bool :=
  bool_decide (fst a = identity) &&
  policy_matches_resource policies resource (snd a).

Definition attached_policies_for_resource
    (policies : policy_map) (attachments : attachment_set)
    (identity : iammodel.IdentityID.t) (resource : iammodel.ResourceName.t)
    : gset iammodel.PolicyID.t :=
  set_map snd (filter (λ a,
    attachment_matches_resource policies identity resource a = true) attachments).

Definition policy_resources (policies : policy_map) : gset iammodel.ResourceName.t :=
  list_to_set (C:=gset iammodel.ResourceName.t)
    ((λ policy, policy.(iammodel.IdentityPolicy.Resource')) <$> (map_to_list policies).*2).

Definition resources_for_identity_counts
    (policies : policy_map) (attachments : attachment_set)
    (identity : iammodel.IdentityID.t) : gmap iammodel.ResourceName.t nat :=
  list_to_map ((λ resource,
    (resource, size (attached_policies_for_resource policies attachments identity resource))) <$>
    elements (policy_resources policies)).

Definition reversed_identity_policy_state
    (identities : identity_set) (attachments : attachment_set)
    (policies : policy_map) :
    gmap iammodel.IdentityID.t (gmap iammodel.ResourceName.t nat) :=
  map_imap (λ identity _, Some (resources_for_identity_counts policies attachments identity))
    (gset_to_gmap tt identities).

Definition reversed_identity_policy_used_reference_set
    (identities : identity_set) (observed_resources : gset iammodel.ResourceName.t)
    : gset IamRef.t :=
  set_map IamRef.IdentityRef identities ∪
  set_map IamRef.ResourceRef observed_resources.

Definition resource_count_refs
    (resources : gmap iammodel.ResourceName.t nat) : gmap IamRef.t nat :=
  kmap (M1:=gmap iammodel.ResourceName.t) (M2:=gmap IamRef.t)
    IamRef.ResourceRef resources.

Definition reversed_identity_policy_ref_counts
    (identities : identity_set) (attachments : attachment_set)
    (policies : policy_map) (ref : IamRef.t) : gmap iammodel.IdentityID.t nat :=
  @counted_reversed_reference.reverse_index
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs
    (reversed_identity_policy_state identities attachments policies) ref.

Definition reversed_identity_policy_counts
    (identities : identity_set) (attachments : attachment_set)
    (policies : policy_map) (resource : iammodel.ResourceName.t)
    : gmap iammodel.IdentityID.t nat :=
  reversed_identity_policy_ref_counts identities attachments policies
    (IamRef.ResourceRef resource).

Local Lemma policy_matches_resource_other policies policy_id policy resource resource' :
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

Local Lemma attachment_matches_resource_other
    policies identity identity' policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  attachment_matches_resource policies identity' resource' (identity, policy_id) = false.
Proof.
  intros Hpolicy Hresource Hneq.
  unfold attachment_matches_resource. simpl.
  destruct (bool_decide (identity = identity')); simpl; [|done].
  apply (policy_matches_resource_other policies policy_id policy resource resource');
    done.
Qed.

Local Lemma attachment_matches_resource_identity_other
    policies identity identity' policy_id resource :
  identity' ≠ identity →
  attachment_matches_resource policies identity' resource (identity, policy_id) = false.
Proof.
  intros Hneq.
  unfold attachment_matches_resource. simpl.
  destruct (bool_decide (identity = identity')) eqn:Heq; simpl; [|done].
  apply bool_decide_eq_true_1 in Heq.
  exfalso. apply Hneq. symmetry. done.
Qed.

Local Lemma attached_policies_for_resource_attach_other
    policies attachments identity identity' policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  attached_policies_for_resource policies
    (attachments ∪ {[(identity, policy_id)]}) identity' resource' =
  attached_policies_for_resource policies attachments identity' resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  apply set_eq. intros policy_id'.
  unfold attached_policies_for_resource.
  rewrite !elem_of_map. split.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    apply elem_of_union in Ha as [Ha|Ha].
    + exists a. split; [done|].
      apply elem_of_filter. split; done.
    + apply elem_of_singleton in Ha. subst a.
      rewrite (attachment_matches_resource_other
        policies identity identity' policy_id policy resource resource')
        in Hmatch; done.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    exists a. split; [done|].
    apply elem_of_filter. split; [done|].
    apply elem_of_union_l. done.
Qed.

Local Lemma attached_policies_for_resource_attach_identity_other
    policies attachments identity identity' policy_id resource :
  identity' ≠ identity →
  attached_policies_for_resource policies
    (attachments ∪ {[(identity, policy_id)]}) identity' resource =
  attached_policies_for_resource policies attachments identity' resource.
Proof.
  intros Hneq.
  apply set_eq. intros policy_id'.
  unfold attached_policies_for_resource.
  rewrite !elem_of_map. split.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    apply elem_of_union in Ha as [Ha|Ha].
    + exists a. split; [done|].
      apply elem_of_filter. split; done.
    + apply elem_of_singleton in Ha. subst a.
      rewrite (attachment_matches_resource_identity_other
        policies identity identity' policy_id resource) in Hmatch; done.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    exists a. split; [done|].
    apply elem_of_filter. split; [done|].
    apply elem_of_union_l. done.
Qed.

Local Lemma attached_policies_for_resource_detach_other
    policies attachments identity identity' policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  attached_policies_for_resource policies
    (attachments ∖ {[(identity, policy_id)]}) identity' resource' =
  attached_policies_for_resource policies attachments identity' resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  apply set_eq. intros policy_id'.
  unfold attached_policies_for_resource.
  rewrite !elem_of_map. split.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    apply elem_of_difference in Ha as [Ha _].
    exists a. split; [done|].
    apply elem_of_filter. split; done.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    exists a. split; [done|].
    apply elem_of_filter. split; [done|].
    apply elem_of_difference. split; [done|].
    intros Hsingle.
    apply elem_of_singleton in Hsingle. subst a.
    rewrite (attachment_matches_resource_other
      policies identity identity' policy_id policy resource resource')
      in Hmatch; done.
Qed.

Local Lemma attached_policies_for_resource_detach_identity_other
    policies attachments identity identity' policy_id resource :
  identity' ≠ identity →
  attached_policies_for_resource policies
    (attachments ∖ {[(identity, policy_id)]}) identity' resource =
  attached_policies_for_resource policies attachments identity' resource.
Proof.
  intros Hneq.
  apply set_eq. intros policy_id'.
  unfold attached_policies_for_resource.
  rewrite !elem_of_map. split.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    apply elem_of_difference in Ha as [Ha _].
    exists a. split; [done|].
    apply elem_of_filter. split; done.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    exists a. split; [done|].
    apply elem_of_filter. split; [done|].
    apply elem_of_difference. split; [done|].
    intros Hsingle.
    apply elem_of_singleton in Hsingle. subst a.
    rewrite (attachment_matches_resource_identity_other
      policies identity identity' policy_id resource) in Hmatch; done.
Qed.

Local Lemma attached_policies_for_resource_contains
    policies attachments identity policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  policy_id ∈ attached_policies_for_resource policies attachments identity resource.
Proof.
  intros Hpolicy Hresource Hattachment.
  unfold attached_policies_for_resource.
  apply elem_of_map.
  exists (identity, policy_id). split; [done|].
  apply elem_of_filter. split.
  - unfold attachment_matches_resource, policy_matches_resource. simpl.
    replace (bool_decide (identity = identity)) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    rewrite Hpolicy Hresource.
    replace (bool_decide (resource = resource)) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    done.
  - done.
Qed.

Local Lemma attached_policies_for_resource_detach_same
    policies attachments identity policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  attached_policies_for_resource policies
    (attachments ∖ {[(identity, policy_id)]}) identity resource =
  attached_policies_for_resource policies attachments identity resource ∖ {[policy_id]}.
Proof.
  intros Hpolicy Hresource Hattachment.
  apply set_eq. intros policy_id'.
  unfold attached_policies_for_resource.
  rewrite elem_of_difference elem_of_singleton !elem_of_map. split.
  - intros (a & -> & Ha).
    apply elem_of_filter in Ha as [Hmatch Ha].
    apply elem_of_difference in Ha as [Ha Hnot_single].
    split.
    + exists a. split; [done|].
      apply elem_of_filter. split; done.
    + intros Hsnd.
      apply Hnot_single.
      apply elem_of_singleton.
      destruct a as [attached_identity attached_policy]; simpl in *.
      subst attached_policy.
      unfold attachment_matches_resource in Hmatch. simpl in Hmatch.
      destruct (bool_decide (attached_identity = identity)) eqn:Hattached_identity;
        simpl in Hmatch; [|done].
      apply bool_decide_eq_true_1 in Hattached_identity.
      subst attached_identity. done.
  - intros [(a & -> & Ha) Hpolicy_id_ne].
    apply elem_of_filter in Ha as [Hmatch Ha].
    exists a. split; [done|].
    apply elem_of_filter. split; [done|].
    apply elem_of_difference. split; [done|].
    intros Hsingle.
    apply elem_of_singleton in Hsingle.
    subst a. simpl in Hpolicy_id_ne. done.
Qed.

Local Lemma attached_policies_for_resource_attach_same_contains
    policies attachments identity policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  policy_id ∈ attached_policies_for_resource policies
    (attachments ∪ {[(identity, policy_id)]}) identity resource.
Proof.
  intros Hpolicy Hresource.
  unfold attached_policies_for_resource.
  apply elem_of_map.
  exists (identity, policy_id). split; [done|].
  apply elem_of_filter. split.
  - unfold attachment_matches_resource, policy_matches_resource. simpl.
    replace (bool_decide (identity = identity)) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    rewrite Hpolicy Hresource.
    replace (bool_decide (resource = resource)) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    done.
  - apply elem_of_union_r.
    apply elem_of_singleton. done.
Qed.

Local Lemma policy_resource_elem policies policy_id policy :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') ∈ policy_resources policies.
Proof.
  intros Hpolicy.
  unfold policy_resources.
  apply elem_of_list_to_set.
  apply list_elem_of_fmap.
  exists policy. split; [done|].
  apply list_elem_of_fmap.
  exists (policy_id, policy). split; [done|].
  rewrite elem_of_map_to_list. done.
Qed.

Local Lemma resources_for_identity_counts_entries_nodup policies attachments identity :
  NoDup (((λ resource,
    (resource, size (attached_policies_for_resource policies attachments identity resource))) <$>
    elements (policy_resources policies)).*1).
Proof.
  rewrite -list_fmap_compose /=.
  rewrite list_fmap_id.
  apply NoDup_elements.
Qed.

Local Lemma resources_for_identity_counts_lookup policies attachments identity resource :
  resource ∈ policy_resources policies →
  resources_for_identity_counts policies attachments identity !! resource =
  Some (size (attached_policies_for_resource policies attachments identity resource)).
Proof.
  intros Hresource.
  unfold resources_for_identity_counts.
  apply elem_of_list_to_map_1.
  - apply resources_for_identity_counts_entries_nodup.
  - apply list_elem_of_fmap.
    exists resource. split; [done|].
    apply elem_of_elements. done.
Qed.

Local Lemma resources_for_identity_counts_lookup_None policies attachments identity resource :
  resource ∉ policy_resources policies →
  resources_for_identity_counts policies attachments identity !! resource = None.
Proof.
  intros Hresource.
  unfold resources_for_identity_counts.
  apply not_elem_of_list_to_map_1.
  rewrite -list_fmap_compose /=.
  rewrite list_fmap_id.
  rewrite elem_of_elements. done.
Qed.

Local Lemma resources_for_identity_counts_attach_other
    policies attachments identity identity' policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  resources_for_identity_counts policies
    (attachments ∪ {[(identity, policy_id)]}) identity' !! resource' =
  resources_for_identity_counts policies attachments identity' !! resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct (decide (resource' ∈ policy_resources policies)) as [Hin|Hnotin].
  - rewrite (resources_for_identity_counts_lookup
      policies (attachments ∪ {[(identity, policy_id)]}) identity' resource' Hin).
    rewrite (resources_for_identity_counts_lookup
      policies attachments identity' resource' Hin).
    rewrite (attached_policies_for_resource_attach_other
      policies attachments identity identity' policy_id policy resource resource');
      done.
  - rewrite !resources_for_identity_counts_lookup_None; done.
Qed.

Local Lemma resources_for_identity_counts_detach_other
    policies attachments identity identity' policy_id policy resource resource' :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  resource' ≠ resource →
  resources_for_identity_counts policies
    (attachments ∖ {[(identity, policy_id)]}) identity' !! resource' =
  resources_for_identity_counts policies attachments identity' !! resource'.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct (decide (resource' ∈ policy_resources policies)) as [Hin|Hnotin].
  - rewrite (resources_for_identity_counts_lookup
      policies (attachments ∖ {[(identity, policy_id)]}) identity' resource' Hin).
    rewrite (resources_for_identity_counts_lookup
      policies attachments identity' resource' Hin).
    rewrite (attached_policies_for_resource_detach_other
      policies attachments identity identity' policy_id policy resource resource');
      done.
  - rewrite !resources_for_identity_counts_lookup_None; done.
Qed.

Local Lemma resources_for_identity_counts_detach_identity_other
    policies attachments identity identity' policy_id resource :
  identity' ≠ identity →
  resources_for_identity_counts policies
    (attachments ∖ {[(identity, policy_id)]}) identity' !! resource =
  resources_for_identity_counts policies attachments identity' !! resource.
Proof.
  intros Hneq.
  destruct (decide (resource ∈ policy_resources policies)) as [Hin|Hnotin].
  - rewrite (resources_for_identity_counts_lookup
      policies (attachments ∖ {[(identity, policy_id)]}) identity' resource Hin).
    rewrite (resources_for_identity_counts_lookup
      policies attachments identity' resource Hin).
    rewrite (attached_policies_for_resource_detach_identity_other
      policies attachments identity identity' policy_id resource); done.
  - rewrite !resources_for_identity_counts_lookup_None; done.
Qed.

Local Lemma resources_for_identity_counts_attach_identity_other
    policies attachments identity identity' policy_id resource :
  identity' ≠ identity →
  resources_for_identity_counts policies
    (attachments ∪ {[(identity, policy_id)]}) identity' !! resource =
  resources_for_identity_counts policies attachments identity' !! resource.
Proof.
  intros Hneq.
  destruct (decide (resource ∈ policy_resources policies)) as [Hin|Hnotin].
  - rewrite (resources_for_identity_counts_lookup
      policies (attachments ∪ {[(identity, policy_id)]}) identity' resource Hin).
    rewrite (resources_for_identity_counts_lookup
      policies attachments identity' resource Hin).
    rewrite (attached_policies_for_resource_attach_identity_other
      policies attachments identity identity' policy_id resource); done.
  - rewrite !resources_for_identity_counts_lookup_None; done.
Qed.

Local Lemma resources_for_identity_counts_attach_same_positive
    policies attachments identity policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ∃ n,
    resources_for_identity_counts policies
      (attachments ∪ {[(identity, policy_id)]}) identity !! resource = Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hpolicy Hresource.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hpolicy_resource.
  rewrite Hresource in Hpolicy_resource.
  rewrite (resources_for_identity_counts_lookup
    policies (attachments ∪ {[(identity, policy_id)]}) identity resource Hpolicy_resource).
  exists (size (attached_policies_for_resource policies
    (attachments ∪ {[(identity, policy_id)]}) identity resource)).
  split; [done|].
  pose proof (attached_policies_for_resource_attach_same_contains
    policies attachments identity policy_id policy resource Hpolicy Hresource) as Hin.
  assert (attached_policies_for_resource policies
    (attachments ∪ {[(identity, policy_id)]}) identity resource ≢ ∅) as Hnonempty.
  { intros Hempty.
    rewrite Hempty in Hin.
    apply elem_of_empty in Hin. done. }
  apply size_non_empty_iff in Hnonempty.
  lia.
Qed.

Local Lemma resources_for_identity_counts_detach_same
    policies attachments identity policy_id policy resource :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  resources_for_identity_counts policies
    (attachments ∖ {[(identity, policy_id)]}) identity !! resource =
  Some (size (attached_policies_for_resource policies attachments identity resource) - 1)%nat.
Proof.
  intros Hpolicy Hresource Hattachment.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hpolicy_resource.
  rewrite Hresource in Hpolicy_resource.
  rewrite (resources_for_identity_counts_lookup
    policies (attachments ∖ {[(identity, policy_id)]}) identity resource Hpolicy_resource).
  rewrite (attached_policies_for_resource_detach_same
    policies attachments identity policy_id policy resource Hpolicy Hresource Hattachment).
  rewrite size_difference.
  - intros detached_policy Hdetached_policy.
    apply elem_of_singleton in Hdetached_policy. subst detached_policy.
    apply (attached_policies_for_resource_contains
      policies attachments identity policy_id policy resource); done.
  - rewrite size_singleton. done.
Qed.

Local Lemma resource_count_refs_identity_ref_none resources identity :
  resource_count_refs resources !! IamRef.IdentityRef identity = None.
Proof.
  unfold resource_count_refs.
  apply eq_None_not_Some.
  intros [n Hlookup].
  destruct (lookup_kmap_Some
    (M1:=gmap iammodel.ResourceName.t) (M2:=gmap IamRef.t)
    IamRef.ResourceRef resources (IamRef.IdentityRef identity) n) as [Hsome _].
  specialize (Hsome Hlookup) as (resource & Heq & _).
  inversion Heq.
Qed.

Local Lemma reversed_identity_policy_identity_ref_counts
    identities attachments policies identity_ref' :
  reversed_identity_policy_ref_counts identities attachments policies
    (IamRef.IdentityRef identity_ref') = ∅.
Proof.
  apply map_eq. intros identity.
  unfold reversed_identity_policy_ref_counts,
    counted_reversed_reference.reverse_index,
    reversed_identity_policy_state.
  rewrite map_lookup_imap.
  destruct (gset_to_gmap tt identities !! identity) as [[]|] eqn:Hidentity.
  - rewrite map_lookup_imap Hidentity /=.
    replace (@counted_reversed_reference.reference_count
      IamRef.t _ _ (gmap iammodel.ResourceName.t nat) resource_count_refs
      (resources_for_identity_counts policies attachments identity)
      (IamRef.IdentityRef identity_ref')) with 0%nat.
    2:{ unfold counted_reversed_reference.reference_count.
        rewrite resource_count_refs_identity_ref_none. done. }
    destruct (decide (0 < 0)%nat); [lia|done].
  - rewrite map_lookup_imap Hidentity /=.
    rewrite lookup_empty. done.
Qed.

Local Lemma reversed_identity_policy_attach_counts_lookup_other_identity
    identities attachments policies identity identity' policy_id resource :
  identity' ≠ identity →
  reversed_identity_policy_counts identities
    (attachments ∪ {[(identity, policy_id)]}) policies resource !! identity' =
  reversed_identity_policy_counts identities attachments policies resource !! identity'.
Proof.
  intros Hneq.
  unfold reversed_identity_policy_counts, reversed_identity_policy_ref_counts,
    counted_reversed_reference.reverse_index, reversed_identity_policy_state.
  rewrite !map_lookup_imap.
  destruct (gset_to_gmap tt identities !! identity') as [[]|] eqn:Hidentity';
    simpl; [|done].
  unfold counted_reversed_reference.reference_count, resource_count_refs.
  rewrite !lookup_kmap.
  rewrite (resources_for_identity_counts_attach_identity_other
    policies attachments identity identity' policy_id resource Hneq).
  done.
Qed.

Local Lemma reversed_identity_policy_counts_lookup
    identities attachments policies identity resource :
  identity ∈ identities →
  resource ∈ policy_resources policies →
  reversed_identity_policy_counts identities attachments policies resource !! identity =
    if decide (0 <
      size (attached_policies_for_resource policies attachments identity resource))%nat
    then Some (size (attached_policies_for_resource policies attachments identity resource))
    else None.
Proof.
  intros Hidentity Hresource.
  unfold reversed_identity_policy_counts, reversed_identity_policy_ref_counts,
    counted_reversed_reference.reverse_index, reversed_identity_policy_state.
  rewrite !map_lookup_imap lookup_gset_to_gmap.
  destruct (decide (identity ∈ identities)) as [_|Hnot_identity]; [|done].
  simpl.
  unfold counted_reversed_reference.reference_count, resource_count_refs.
  rewrite (@option_guard_True unit (identity ∈ identities) _ (Some ()%V)
    Hidentity).
  simpl.
  rewrite (lookup_kmap
    (M1:=gmap iammodel.ResourceName.t) (M2:=gmap IamRef.t)
    IamRef.ResourceRef
    (resources_for_identity_counts policies attachments identity)
    resource).
  rewrite (resources_for_identity_counts_lookup
    policies attachments identity resource Hresource).
  done.
Qed.

Local Lemma reversed_identity_policy_attach_counts_lookup_positive
    identities attachments policies identity policy_id policy resource :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ∃ n,
    reversed_identity_policy_counts identities
      (attachments ∪ {[(identity, policy_id)]}) policies resource !! identity = Some n ∧
    (1 ≤ n)%nat.
Proof.
  intros Hidentity Hpolicy Hresource.
  unfold reversed_identity_policy_counts, reversed_identity_policy_ref_counts,
    counted_reversed_reference.reverse_index, reversed_identity_policy_state.
  rewrite !map_lookup_imap lookup_gset_to_gmap.
  destruct (decide (identity ∈ identities)) as [_|Hnot_identity]; [|done].
  simpl.
  unfold counted_reversed_reference.reference_count, resource_count_refs.
  rewrite (@option_guard_True unit (identity ∈ identities) _ (Some ()%V)
    Hidentity).
  simpl.
  rewrite (lookup_kmap
    (M1:=gmap iammodel.ResourceName.t) (M2:=gmap IamRef.t)
    IamRef.ResourceRef
    (resources_for_identity_counts policies
      (attachments ∪ {[(identity, policy_id)]}) identity)
    resource).
  destruct (resources_for_identity_counts_attach_same_positive
    policies attachments identity policy_id policy resource Hpolicy Hresource)
    as (n & Hlookup & Hn).
  rewrite Hlookup /=.
  destruct (decide (0 < n)%nat); [|lia].
  exists n. split; done.
Qed.

Local Lemma reversed_identity_policy_detach_counts_lookup_positive
    identities attachments policies identity policy_id policy resource :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  ∃ n,
    reversed_identity_policy_counts identities attachments policies resource !! identity =
      Some n ∧
    (0 < n)%nat.
Proof.
  intros Hidentity Hpolicy Hresource Hattachment.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hpolicy_resource.
  rewrite Hresource in Hpolicy_resource.
  rewrite (reversed_identity_policy_counts_lookup
    identities attachments policies identity resource Hidentity Hpolicy_resource).
  pose proof (attached_policies_for_resource_contains
    policies attachments identity policy_id policy resource Hpolicy Hresource Hattachment)
    as Hcontains.
  assert (attached_policies_for_resource policies attachments identity resource ≢ ∅)
    as Hnonempty.
  { intros Hempty.
    rewrite Hempty in Hcontains.
    apply elem_of_empty in Hcontains. done. }
  apply size_non_empty_iff in Hnonempty.
  destruct (decide (0 <
    size (attached_policies_for_resource policies attachments identity resource))%nat)
    as [Hpositive|Hnot_positive]; [|lia].
  exists (size (attached_policies_for_resource policies attachments identity resource)).
  split; done.
Qed.

Local Lemma reversed_identity_policy_detach_counts_lookup_other_identity
    identities attachments policies identity identity' policy_id resource :
  identity' ≠ identity →
  reversed_identity_policy_counts identities
    (attachments ∖ {[(identity, policy_id)]}) policies resource !! identity' =
  reversed_identity_policy_counts identities attachments policies resource !! identity'.
Proof.
  intros Hneq.
  unfold reversed_identity_policy_counts, reversed_identity_policy_ref_counts,
    counted_reversed_reference.reverse_index, reversed_identity_policy_state.
  rewrite !map_lookup_imap.
  destruct (gset_to_gmap tt identities !! identity') as [[]|] eqn:Hidentity';
    simpl; [|done].
  unfold counted_reversed_reference.reference_count, resource_count_refs.
  rewrite !lookup_kmap.
  rewrite (resources_for_identity_counts_detach_identity_other
    policies attachments identity identity' policy_id resource Hneq).
  done.
Qed.

Local Lemma reversed_identity_policy_detach_counts_lookup_decrease
    identities attachments policies identity policy_id policy resource n :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  reversed_identity_policy_counts identities attachments policies resource !! identity =
    Some n →
  (1 < n)%nat →
  reversed_identity_policy_counts identities
    (attachments ∖ {[(identity, policy_id)]}) policies resource !! identity =
    Some (n - 1)%nat.
Proof.
  intros Hidentity Hpolicy Hresource Hattachment Hold_lookup Hn.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hpolicy_resource.
  rewrite Hresource in Hpolicy_resource.
  rewrite (reversed_identity_policy_counts_lookup
    identities attachments policies identity resource Hidentity Hpolicy_resource)
    in Hold_lookup.
  destruct (decide (0 <
    size (attached_policies_for_resource policies attachments identity resource))%nat)
    as [Hold_positive|Hold_zero]; [|done].
  inversion Hold_lookup. subst n. clear Hold_lookup.
  rewrite (reversed_identity_policy_counts_lookup
    identities (attachments ∖ {[(identity, policy_id)]}) policies identity resource
    Hidentity Hpolicy_resource).
  rewrite (attached_policies_for_resource_detach_same
    policies attachments identity policy_id policy resource Hpolicy Hresource Hattachment).
  rewrite size_difference.
  - intros detached_policy Hdetached_policy.
    apply elem_of_singleton in Hdetached_policy. subst detached_policy.
    apply (attached_policies_for_resource_contains
      policies attachments identity policy_id policy resource); done.
  - rewrite size_singleton.
    destruct (decide (0 <
      size (attached_policies_for_resource policies attachments identity resource) - 1)%nat)
      as [Hnew_positive|Hnew_zero]; [done|lia].
Qed.

Local Lemma reversed_identity_policy_detach_counts_lookup_remove
    identities attachments policies identity policy_id policy resource :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  reversed_identity_policy_counts identities attachments policies resource !! identity =
    Some 1%nat →
  reversed_identity_policy_counts identities
    (attachments ∖ {[(identity, policy_id)]}) policies resource !! identity = None.
Proof.
  intros Hidentity Hpolicy Hresource Hattachment Hold_lookup.
  pose proof (policy_resource_elem policies policy_id policy Hpolicy) as Hpolicy_resource.
  rewrite Hresource in Hpolicy_resource.
  rewrite (reversed_identity_policy_counts_lookup
    identities attachments policies identity resource Hidentity Hpolicy_resource)
    in Hold_lookup.
  destruct (decide (0 <
    size (attached_policies_for_resource policies attachments identity resource))%nat)
    as [Hold_positive|Hold_zero]; [|done].
  inversion Hold_lookup as [Hsize]. clear Hold_lookup.
  rewrite (reversed_identity_policy_counts_lookup
    identities (attachments ∖ {[(identity, policy_id)]}) policies identity resource
    Hidentity Hpolicy_resource).
  rewrite (attached_policies_for_resource_detach_same
    policies attachments identity policy_id policy resource Hpolicy Hresource Hattachment).
  rewrite size_difference.
  - intros detached_policy Hdetached_policy.
    apply elem_of_singleton in Hdetached_policy. subst detached_policy.
    apply (attached_policies_for_resource_contains
      policies attachments identity policy_id policy resource); done.
  - rewrite size_singleton Hsize.
    destruct (decide (0 < 1 - 1)%nat); [lia|done].
Qed.

Local Lemma reversed_identity_policy_attach_other_refs
    identities attachments policies identity policy_id policy resource ref :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  reversed_identity_policy_ref_counts identities
    (attachments ∪ {[(identity, policy_id)]}) policies ref =
  reversed_identity_policy_ref_counts identities attachments policies ref.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct ref as [identity_ref'|resource'].
  - rewrite !reversed_identity_policy_identity_ref_counts. done.
  - apply map_eq. intros identity'.
    unfold reversed_identity_policy_ref_counts,
      counted_reversed_reference.reverse_index,
      reversed_identity_policy_state.
    rewrite !map_lookup_imap.
    destruct (gset_to_gmap tt identities !! identity') as [[]|] eqn:Hidentity;
      simpl; [|done].
    unfold counted_reversed_reference.reference_count, resource_count_refs.
    rewrite !lookup_kmap.
    assert (Hresource_ne : resource' ≠ resource).
    { intros Heq. apply Hneq. subst. done. }
    rewrite (resources_for_identity_counts_attach_other
      policies attachments identity identity' policy_id policy resource resource');
      done.
Qed.

Local Lemma reversed_identity_policy_detach_other_refs
    identities attachments policies identity policy_id policy resource ref :
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  ref ≠ IamRef.ResourceRef resource →
  reversed_identity_policy_ref_counts identities
    (attachments ∖ {[(identity, policy_id)]}) policies ref =
  reversed_identity_policy_ref_counts identities attachments policies ref.
Proof.
  intros Hpolicy Hresource Hneq.
  destruct ref as [identity_ref'|resource'].
  - rewrite !reversed_identity_policy_identity_ref_counts. done.
  - apply map_eq. intros identity'.
    unfold reversed_identity_policy_ref_counts,
      counted_reversed_reference.reverse_index,
      reversed_identity_policy_state.
    rewrite !map_lookup_imap.
    destruct (gset_to_gmap tt identities !! identity') as [[]|] eqn:Hidentity;
      simpl; [|done].
    unfold counted_reversed_reference.reference_count, resource_count_refs.
    rewrite !lookup_kmap.
    assert (Hresource_ne : resource' ≠ resource).
    { intros Heq. apply Hneq. subst. done. }
    rewrite (resources_for_identity_counts_detach_other
      policies attachments identity identity' policy_id policy resource resource');
      done.
Qed.

Local Lemma reversed_identity_policy_state_identity_refs
    identities attachments policies observed_resources :
  map_Forall (λ identity resources,
    identity_ref identity resources ∈
      reversed_identity_policy_used_reference_set identities observed_resources)
    (reversed_identity_policy_state identities attachments policies).
Proof.
  rewrite map_Forall_lookup.
  intros identity resources Hlookup.
  unfold reversed_identity_policy_state in Hlookup.
  rewrite map_lookup_imap in Hlookup.
  destruct (gset_to_gmap tt identities !! identity) as [[]|] eqn:Hidentity_lookup.
  - simpl in Hlookup. inversion Hlookup. subst resources.
    apply lookup_gset_to_gmap_Some in Hidentity_lookup as [Hidentity _].
    unfold identity_ref, reversed_identity_policy_used_reference_set.
    apply elem_of_union_l.
    apply elem_of_map.
    exists identity. split; done.
  - simpl in Hlookup. inversion Hlookup.
Qed.

Local Lemma reversed_identity_policy_resource_ref_used identities observed_resources resource :
  resource ∈ observed_resources →
  IamRef.ResourceRef resource ∈
    reversed_identity_policy_used_reference_set identities observed_resources.
Proof.
  intros Hresource.
  unfold reversed_identity_policy_used_reference_set.
  apply elem_of_union_r.
  apply elem_of_map.
  exists resource. split; done.
Qed.

Local Lemma reversed_identity_policy_resource_ref_observed
    identities observed_resources resource :
  IamRef.ResourceRef resource ∈
    reversed_identity_policy_used_reference_set identities observed_resources →
  resource ∈ observed_resources.
Proof.
  unfold reversed_identity_policy_used_reference_set.
  intros Hused.
  apply elem_of_union in Hused as [Hidentity|Hresource].
  - apply elem_of_map in Hidentity as (identity & Heq & _).
    inversion Heq.
  - apply elem_of_map in Hresource as (resource' & Heq & Hin).
    inversion Heq. subst. done.
Qed.

Class iamResourceAccessG Σ :=
  { #[global] iam_reversed_identity_policy_counted_reversed_referenceG ::
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

Section reversed_identity_policy.
Context `{!iamResourceAccessG Σ}.

Definition own_reversed_identity_policy_auth
    γ (identities : identity_set) (attachments : attachment_set)
    (policies : policy_map) (observed_resources : gset iammodel.ResourceName.t)
    : iProp Σ :=
  @counted_reversed_reference.own_auth
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _ γ
    (reversed_identity_policy_state identities attachments policies,
     reversed_identity_policy_used_reference_set identities observed_resources).

Definition own_reversed_identity_policy_frag
    γ (resource : iammodel.ResourceName.t) dq
    (identities : gmap iammodel.IdentityID.t nat) : iProp Σ :=
  @counted_reversed_reference.own_frag
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (IamRef.ResourceRef resource) dq identities.

Global Instance own_reversed_identity_policy_auth_timeless
    γ identities attachments policies observed_resources :
  Timeless (own_reversed_identity_policy_auth γ identities attachments policies observed_resources).
Proof. unfold own_reversed_identity_policy_auth. apply _. Qed.

Global Instance own_reversed_identity_policy_frag_timeless γ resource dq identities :
  Timeless (own_reversed_identity_policy_frag γ resource dq identities).
Proof. unfold own_reversed_identity_policy_frag. apply _. Qed.

Lemma own_reversed_identity_policy_frag_valid
    {γ identities attachments policies observed_resources resource dq resource_identities} :
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource dq resource_identities -∗
  ⌜ resource_identities =
      reversed_identity_policy_counts identities attachments policies resource ⌝ ∗
  ⌜ IamRef.ResourceRef resource ∈
      reversed_identity_policy_used_reference_set identities observed_resources ⌝.
Proof.
  unfold own_reversed_identity_policy_auth, own_reversed_identity_policy_frag,
    reversed_identity_policy_counts.
  iIntros "Hauth Hfrag".
  iDestruct (@counted_reversed_reference.own_auth_frag_valid
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (reversed_identity_policy_state identities attachments policies,
       reversed_identity_policy_used_reference_set identities observed_resources)
    (IamRef.ResourceRef resource) dq resource_identities
    with "Hauth Hfrag") as "[%Hidentities %Hused]".
  iPureIntro. split; done.
Qed.

Lemma own_reversed_identity_policy_frag_valid_pure
    {γ identities attachments policies observed_resources resource dq resource_identities} :
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource dq resource_identities -∗
  ⌜ resource_identities =
      reversed_identity_policy_counts identities attachments policies resource ∧
    IamRef.ResourceRef resource ∈
      reversed_identity_policy_used_reference_set identities observed_resources ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_reversed_identity_policy_frag_valid with "Hauth Hfrag")
    as "[%Hidentities %Hused]".
  iPureIntro. split; done.
Qed.

Lemma own_reversed_identity_policy_frag_observed
    {γ identities attachments policies observed_resources resource dq resource_identities} :
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource dq resource_identities -∗
  ⌜ resource ∈ observed_resources ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_reversed_identity_policy_frag_valid with "Hauth Hfrag")
    as "[_ %Hused]".
  iPureIntro.
  eapply reversed_identity_policy_resource_ref_observed. exact Hused.
Qed.

Lemma own_reversed_identity_policy_frag_lookup_positive
    {γ identities attachments policies observed_resources resource dq
      resource_identities identity policy_id policy} :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource dq resource_identities -∗
  ⌜ ∃ n, resource_identities !! identity = Some n ∧ (0 < n)%nat ⌝.
Proof.
  iIntros (Hidentity Hpolicy Hpolicy_resource Hattachment) "Hauth Hfrag".
  iPoseProof (own_reversed_identity_policy_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hresource_identities _].
  destruct (reversed_identity_policy_detach_counts_lookup_positive
    identities attachments policies identity policy_id policy resource
    Hidentity Hpolicy Hpolicy_resource Hattachment) as (n & Hlookup & Hpositive).
  iPureIntro.
  exists n. split; [|done].
  rewrite Hresource_identities. done.
Qed.

Local Lemma reversed_identity_policy_update_vs
    {γ identities attachments policies identities' attachments' policies'
      observed_resources resource resource_identities resource_identities'} :
  resource_identities' =
    reversed_identity_policy_counts identities' attachments' policies' resource →
  (∀ ref,
    ref ≠ IamRef.ResourceRef resource →
    ref ∈ reversed_identity_policy_used_reference_set identities observed_resources →
    ref ∈ reversed_identity_policy_used_reference_set identities' observed_resources) →
  (∀ ref,
    ref ≠ IamRef.ResourceRef resource →
    ref ∈ reversed_identity_policy_used_reference_set identities observed_resources →
    reversed_identity_policy_ref_counts identities' attachments' policies' ref =
      reversed_identity_policy_ref_counts identities attachments policies ref) →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource 1 resource_identities ==∗
    own_reversed_identity_policy_auth γ identities' attachments' policies' observed_resources ∗
    own_reversed_identity_policy_frag γ resource 1 resource_identities'.
Proof.
  iIntros (Hresource_identities Hused_preserve Hindex_preserve) "Hauth Hfrag".
  iPoseProof (own_reversed_identity_policy_frag_observed with "Hauth Hfrag")
    as "%Hresource".
  unfold own_reversed_identity_policy_auth, own_reversed_identity_policy_frag.
  iMod (@counted_reversed_reference.generic_reference_update_vs
    iammodel.IdentityID.t _ _ IamRef.t _ _ (gmap iammodel.ResourceName.t nat)
    resource_count_refs identity_ref
    Σ _
    γ (reversed_identity_policy_state identities attachments policies,
       reversed_identity_policy_used_reference_set identities observed_resources)
    (reversed_identity_policy_state identities' attachments' policies',
       reversed_identity_policy_used_reference_set identities' observed_resources)
    (IamRef.ResourceRef resource) resource_identities resource_identities'
    with "Hauth Hfrag") as "[Hauth Hfrag]".
  - apply reversed_identity_policy_state_identity_refs.
  - apply reversed_identity_policy_resource_ref_used. exact Hresource.
  - symmetry. exact Hresource_identities.
  - exact Hused_preserve.
  - exact Hindex_preserve.
  - iModIntro. iFrame.
Qed.

Lemma attach_identity_policy_vs
    {γ identities attachments attachments' policies observed_resources
      identity policy_id policy resource resource_identities} :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  attachments' = attachments ∪ {[(identity, policy_id)]} →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource 1 resource_identities ==∗
    ∃ resource_identities',
    own_reversed_identity_policy_auth γ identities attachments' policies observed_resources ∗
    own_reversed_identity_policy_frag γ resource 1 resource_identities' ∗
    ⌜ (∀ identity',
        identity' ≠ identity →
        resource_identities' !! identity' = resource_identities !! identity') ∧
      ∃ n, resource_identities' !! identity = Some n ∧ (1 ≤ n)%nat ⌝.
Proof.
  iIntros (Hidentity Hpolicy Hpolicy_resource Hattachments) "Hauth Hfrag".
  iPoseProof (own_reversed_identity_policy_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hresource_identities _].
  subst attachments'.
  set (resource_identities' :=
    reversed_identity_policy_counts identities
      (attachments ∪ {[(identity, policy_id)]}) policies resource).
  iMod (reversed_identity_policy_update_vs with "Hauth Hfrag")
    as "[Hauth Hfrag]".
  - reflexivity.
  - intros ref _ Href. exact Href.
  - intros ref Hneq _.
    apply (reversed_identity_policy_attach_other_refs
      identities attachments policies identity policy_id policy resource ref);
      done.
  - iModIntro.
    iExists resource_identities'.
    iFrame.
    iPureIntro.
    split.
    + intros identity' Hne.
      unfold resource_identities'.
      rewrite (reversed_identity_policy_attach_counts_lookup_other_identity
        identities attachments policies identity identity' policy_id resource Hne).
      rewrite Hresource_identities. done.
    + unfold resource_identities'.
      apply (reversed_identity_policy_attach_counts_lookup_positive
        identities attachments policies identity policy_id policy resource);
        done.
Qed.

Lemma detach_identity_policy_vs
    {γ identities attachments attachments' policies observed_resources
      identity policy_id policy resource resource_identities} :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  attachments' = attachments ∖ {[(identity, policy_id)]} →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource 1 resource_identities ==∗
    ∃ n,
    ⌜ resource_identities !! identity = Some n ∧ (0 < n)%nat ⌝ ∗
    own_reversed_identity_policy_auth γ identities attachments' policies observed_resources ∗
    own_reversed_identity_policy_frag γ resource 1
      (if decide (1 < n)%nat
       then <[identity := (n - 1)%nat]> resource_identities
       else delete identity resource_identities).
Proof.
  iIntros (Hidentity Hpolicy Hpolicy_resource Hattachment Hattachments) "Hauth Hfrag".
  iPoseProof (own_reversed_identity_policy_frag_valid_pure with "Hauth Hfrag")
    as "%Hvalid".
  destruct Hvalid as [Hresource_identities _].
  iPoseProof (own_reversed_identity_policy_frag_lookup_positive
    (identity:=identity) (policy_id:=policy_id) (policy:=policy)
    with "Hauth Hfrag") as "%Hlookup_positive"; [done|done|done|done|].
  destruct Hlookup_positive as (n & Hfrag_lookup & Hpositive).
  subst attachments'.
  destruct (decide (1 < n)%nat) as [Hgt|Hle].
  - iMod (reversed_identity_policy_update_vs
      (resource_identities':= if decide (1 < n)%nat
        then <[identity := (n - 1)%nat]> resource_identities
        else delete identity resource_identities)
      with "Hauth Hfrag")
      as "[Hauth Hfrag]".
    + apply map_eq. intros identity'.
      destruct (decide (1 < n)%nat) as [Hgt'|Hle']; [|lia].
      destruct (decide (identity' = identity)) as [->|Hne].
      * rewrite lookup_insert_eq.
        symmetry.
        eapply reversed_identity_policy_detach_counts_lookup_decrease; try done.
        rewrite -Hresource_identities. done.
      * rewrite lookup_insert.
        destruct (decide (identity = identity')) as [Heq|_].
        { exfalso. apply Hne. symmetry. done. }
        symmetry.
        rewrite (reversed_identity_policy_detach_counts_lookup_other_identity
          identities attachments policies identity identity' policy_id resource Hne).
        rewrite Hresource_identities. done.
    + intros ref _ Href. exact Href.
    + intros ref Hneq _.
      apply (reversed_identity_policy_detach_other_refs
        identities attachments policies identity policy_id policy resource ref);
        done.
    + iModIntro.
      iExists n. iFrame.
      iPureIntro. split; done.
  - assert (Hn_eq : n = 1%nat) by lia. subst n.
    iMod (reversed_identity_policy_update_vs
      (resource_identities':= if decide (1 < 1)%nat
        then <[identity := (1 - 1)%nat]> resource_identities
        else delete identity resource_identities)
      with "Hauth Hfrag")
      as "[Hauth Hfrag]".
    + apply map_eq. intros identity'.
      destruct (decide (1 < 1)%nat) as [Hgt'|Hle']; [lia|].
      destruct (decide (identity' = identity)) as [->|Hne].
      * rewrite lookup_delete_eq.
        symmetry.
        eapply reversed_identity_policy_detach_counts_lookup_remove; try done.
        rewrite -Hresource_identities. done.
      * rewrite lookup_delete.
        destruct (decide (identity = identity')) as [Heq|_].
        { exfalso. apply Hne. symmetry. done. }
        symmetry.
        rewrite (reversed_identity_policy_detach_counts_lookup_other_identity
          identities attachments policies identity identity' policy_id resource Hne).
        rewrite Hresource_identities. done.
    + intros ref _ Href. exact Href.
    + intros ref Hneq _.
      apply (reversed_identity_policy_detach_other_refs
        identities attachments policies identity policy_id policy resource ref);
        done.
    + iModIntro.
      iExists 1%nat. iFrame.
      iPureIntro. split; done.
Qed.

Lemma detach_identity_policy_gt_1_vs
    {γ identities attachments attachments' policies observed_resources
      identity policy_id policy resource resource_identities n} :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  attachments' = attachments ∖ {[(identity, policy_id)]} →
  resource_identities !! identity = Some n →
  (1 < n)%nat →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource 1 resource_identities ==∗
    own_reversed_identity_policy_auth γ identities attachments' policies observed_resources ∗
    own_reversed_identity_policy_frag γ resource 1
      (<[identity := (n - 1)%nat]> resource_identities).
Proof.
  iIntros (Hidentity Hpolicy Hpolicy_resource Hattachment Hattachments Hlookup Hn)
    "Hauth Hfrag".
  iMod (detach_identity_policy_vs with "Hauth Hfrag") as (n') "(%Hn' & Hauth & Hfrag)";
    [done|done|done|done|done|].
  destruct Hn' as [Hlookup' Hpositive].
  assert (n' = n) as -> by congruence.
  destruct (decide (1 < n)%nat); [iModIntro; iFrame|lia].
Qed.

Lemma detach_identity_policy_eq_1_vs
    {γ identities attachments attachments' policies observed_resources
      identity policy_id policy resource resource_identities} :
  identity ∈ identities →
  policies !! policy_id = Some policy →
  policy.(iammodel.IdentityPolicy.Resource') = resource →
  (identity, policy_id) ∈ attachments →
  attachments' = attachments ∖ {[(identity, policy_id)]} →
  resource_identities !! identity = Some 1%nat →
  own_reversed_identity_policy_auth γ identities attachments policies observed_resources -∗
  own_reversed_identity_policy_frag γ resource 1 resource_identities ==∗
    own_reversed_identity_policy_auth γ identities attachments' policies observed_resources ∗
    own_reversed_identity_policy_frag γ resource 1
      (delete identity resource_identities).
Proof.
  iIntros (Hidentity Hpolicy Hpolicy_resource Hattachment Hattachments Hlookup)
    "Hauth Hfrag".
  iMod (detach_identity_policy_vs with "Hauth Hfrag") as (n') "(%Hn' & Hauth & Hfrag)";
    [done|done|done|done|done|].
  destruct Hn' as [Hlookup' Hpositive].
  assert (n' = 1%nat) as -> by congruence.
  destruct (decide (1 < 1)%nat); [lia|iModIntro; iFrame].
Qed.

End reversed_identity_policy.

End reversed_identity_policy_defs.
