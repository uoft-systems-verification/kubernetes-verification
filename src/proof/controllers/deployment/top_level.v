From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common.

Section specs.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  code.controllers.deployment.deployment.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance intstr_sem : intstr.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_intstr_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".
Context `{!KObjectV.ObjectInterfaceAssumptions}.

(* ---------------------------------------------------------------- *)
(* Shared ownership bundle for the two top-level triples.            *)
(*                                                                   *)
(* The reduction to Hoare triples needs two of them, H1 and H2.     *)
(* H1 is [progress_spec] below, discharged by [wp_syncDeployment] in *)
(* sync_deployment.v; H2 is [stability_spec], discharged by          *)
(* [wp_syncDeployment_stability] in stability.v.                     *)
(*                                                                   *)
(* There is no preservation triple yet, and there should be -- see  *)
(* the TODO on [owned_resources] below. The triples here assume a    *)
(* good environment rather than naming it.                           *)
(* ---------------------------------------------------------------- *)

(* Field names are prefixed because [replicaset/top_level.v] already exports
   [rs_dq] and [children_dq] as global record projections. *)
Record all_fractions := {
  dep_dq : dfrac;
  dep_rs_dq : dfrac;
  dep_children_dq : dfrac;
}.

(* The progress triple writes through the ReplicaSet fragments, so those are
   full, and so is the children fraction.

   That last point was left open when this bundle was written. Proving
   [wp_syncDeployment] settles it: the sync may create a ReplicaSet, which adds
   a key to the children set and consumes the name's reservation, and neither
   is possible at a partial fraction. So the children fraction is 1, not a
   parameter -- the same choice replicaset/top_level.v makes, and for the same
   reason. *)
Definition mutating_fractions (dq : dfrac) : all_fractions :=
  {| dep_dq := dq; dep_rs_dq := 1; dep_children_dq := 1 |}.

(* Stability holds everything at the *same* fraction. That is the entire
   mechanism of H2: a write needs the full fraction, so if the proof goes
   through at all, no write happened. *)
Definition stability_fractions (dq : dfrac) : all_fractions :=
  {| dep_dq := dq; dep_rs_dq := dq; dep_children_dq := dq |}.

(* Everything the controller owns going in. The reserved fragment travels with
   the children fragment (both are 1 under [mutating_fractions], both [dq]
   under [stability_fractions]), so it shares [dep_children_dq].

   This is the precondition bundle for both triples, and the *post*condition
   bundle for stability. The progress postcondition cannot use it: its branches
   differ in the children set and in whether the reserved key is available or
   occupied, so it spells those out. *)
(* THE GOOD-ENVIRONMENT ASSUMPTION, and what is still missing.

   [owned_resources] takes a [ready : bool], mirroring
   replicaset/top_level.v. [progress_spec] below is stated at [true]: the
   controller makes progress *provided nothing in the environment forces it to
   wait for a deletion*. Two things can, and [ready] covers both.

   AXIS 1 -- the name reservation. [getNewReplicaSet] creates under the
   deterministic name <deployment>-<template-hash>. The model gives every name
   a reservation with three states (kubernetes_model/inv.v:46-56):

       Available | Occupied uid | Deleting uid

   [Deleting uid] is reachable: this controller never deletes ReplicaSets, so
   an external actor -- a user, garbage collection, or the revision-history
   cleanup this simplified controller drops -- can delete the object sitting at
   that name. Until deletion completes the name is not free, the create returns
   AlreadyExists, and the controller can only wait.

   AXIS 2 -- terminating children. A child ReplicaSet carrying a deletion
   timestamp is one the controller must wait out before the rollout can be
   realized. This is NOT implied by holding fragments for [rss], contrary to
   what an earlier version of this comment claimed. The argument given there
   was that [kview.own_meta_valid] yields [DeletionTimestamp = None] from any
   metadata fragment, and [Hdom_eq] forces [rss] to be exactly the
   ReplicaSet-kinded children. The first half is true and the second is not:
   [own_children_frag] records the keys of the *living* children only
   (algebra/cview.v:124), so a terminating child is missing from
   [children_keys] altogether rather than present and visibly terminating.
   Fragments for [rss] therefore say every object in [rss] is living, and say
   nothing about children outside it.

   That gap is load-bearing downstream: [filterReplicaSetsByOwner] reads
   through the replicaSetController index, which filters by [obj_parent_ref]
   and is blind to deletion timestamps, so it returns terminating children the
   caller holds no fragment for. See the note on
   [wp_State__ByIndex_replicaSetController] in
   kubernetes_model/index_replicaset.v.

   Not part of [ready], because ownership really does imply it:
     - No competing writer. Discharged structurally by [dep_rs_dq := 1].

   TODO (separate PR): the [ready = false] half, in dependency order.
   Item 1 is the blocker, and is the other half of the TODO at
   kubernetes_model/create_named.v:701.

     1. [wp_State__ReplicaSetCreate_named] -- the Deleting variant of the named
        create, which does not exist yet. Mirror [wp_State__PodCreate_named]
        (kubernetes_model/create_named.v:610); the note at :704 there records
        that only the Available variant was written.
     2. A second branch in [wp_getNewReplicaSet] for the AlreadyExists return.
        Note the Go then calls [ReplicaSetGet] and hands the result to
        [rollout], which would scale a terminating object -- that path is
        currently assumed away, not verified.
     3. [preservation_spec] at [ready = false], concluding
        [match_distance d rss' <= match_distance d rss].

   So the premise is now written down rather than baked silently into the
   ownership bundle; what remains is the [false] half. *)
Definition owned_resources γ (d : DeploymentV.t)
    (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    uid kmeta (fractions : all_fractions) (ready : bool) : iProp Σ :=
  "Hown_d_meta" ∷ own_meta_frag γ (DeploymentV.key d) uid
    fractions.(dep_dq) kmeta ∗
  "Hown_d_spec" ∷ own_spec_frag γ (DeploymentV.key d) uid fractions.(dep_dq)
    (ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')) ∗
  (* Good environment, axis 1: the name the create targets is free, not
     mid-deletion. *)
  "Hreserved" ∷ (if ready then
      own_available_reserved_frag γ fractions.(dep_children_dq) (new_rs_key d)
    else
      ∃ status, own_reserved_frag γ (new_rs_key d)
        fractions.(dep_children_dq) status)%I ∗
  "Hown_children" ∷ own_children_frag γ (DeploymentV.key d) uid
    fractions.(dep_children_dq) children_keys ∗
  (* Good environment, axis 2: no child ReplicaSet is mid-deletion. Not
     implied by the fragments above, contrary to what an earlier draft of
     this file claimed: [own_children_frag] records only the *living*
     children (algebra/cview.v:124), so a terminating child is absent from
     [children_keys] rather than present-and-visible, and [Hdom_eq] cannot
     see it either. The index the controller reads through filters by
     [obj_parent_ref], which is blind to deletion timestamps, so it returns
     terminating children the caller holds no fragment for. *)
  "Hown_terminating_children" ∷ (if ready then
      own_terminating_children_frag γ (DeploymentV.key d) uid Quiescent
    else
      ∃ control_phase,
        own_terminating_children_frag γ (DeploymentV.key d) uid control_phase)%I ∗
  "Hown_frags" ∷ ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(dep_rs_dq)
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(dep_rs_dq)
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
  "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝.

(* The hypotheses both triples carry. [unique_new_replica_set] is the
   no-collision assumption: findNewReplicaSet returns the *first* template
   match, so with two matches a sync could pick either and stability would be
   false as stated. *)
Definition input_requirement (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) (namespace name : go_string) : Prop :=
  DeploymentV.key d = {|
    KKey.Kind' := DeploymentV.kind;
    KKey.Namespace' := namespace;
    KKey.Name' := name
  |} ∧
  DeploymentV.valid d ∧
  valid_namespace namespace ∧
  valid_dns1123_subdomain (new_rs_name d) ∧
  (* The selector must leave the pod-template-hash label alone and stay inside
     the model's size bound once it is stamped -- see
     [deployment_selector_admissible]. Without it getNewReplicaSet can build a
     ReplicaSet the API server rejects. *)
  deployment_selector_admissible d ∧
  Forall ReplicaSetV.valid rss ∧
  list_to_set (ReplicaSetV.key <$> rss) =
    filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ∧
  unique_new_replica_set d rss.

(* ---------------------------------------------------------------- *)
(* (M) -- the progress metric                                       *)
(* ---------------------------------------------------------------- *)

(* Two-valued, and that is the accurate metric for this controller rather than
   a degenerate one. The rule is that a metric's granularity has to match how
   many reconcile runs convergence takes: replicaset/top_level.v uses
   |actual - desired| because SlowStartBatch creates a bounded batch per sync,
   and statefulset charges 2 for a live outdated pod so that the run which
   deletes it is a strict decrease rather than a plateau.

   This controller has no surge pacing, so one sync scales the new ReplicaSet
   to replicasOf(d) and every old one to 0, and every lemma in the rollout
   chain returns without an error -- full fragment ownership rules out the
   update conflict that would otherwise leave a sync half-done. Convergence
   takes one run, so the metric needs exactly two values. *)
Definition match_distance (d : DeploymentV.t) (rss : list ReplicaSetV.t) : nat :=
  if decide (deployment_realized d rss) then 0%nat else 1%nat.

Lemma match_distance_zero_matches d rss :
  match_distance d rss = 0%nat ↔ deployment_realized d rss.
Proof.
  rewrite /match_distance.
  destruct (decide (deployment_realized d rss)) as [Hr|Hr].
  - split; [intros _; exact Hr|done].
  - split; [discriminate|intros Hc; contradiction].
Qed.

(* The collapse, which is why stating [progress_spec] in the reduction's shape
   costs no strength here. [match_distance] is two-valued, so a strict decrease
   can only be 1 -> 0, and that is [deployment_realized] again: the progress
   disjunct says nothing the match disjunct does not already say. *)
Lemma progress_disjunct_realized d rss rss' :
  deployment_realized d rss' ∨
    (rss_progress_observed rss rss' ∧
     match_distance d rss' < match_distance d rss) →
  deployment_realized d rss'.
Proof.
  intros [Hrealized|[_ Hlt]]; first exact Hrealized.
  apply match_distance_zero_matches.
  unfold match_distance in Hlt |- *.
  destruct (decide (deployment_realized d rss')),
           (decide (deployment_realized d rss)); lia.
Qed.

(* H1 -- progress. Stated in the reduction's shape, matching
   replicaset/top_level.v's [progress_spec]: either the desired state is
   reached, or the sync made an observable change that strictly decreased the
   metric.

   This controller always establishes the *first* disjunct, and
   [progress_disjunct_realized] shows the second cannot say anything more here
   -- with a two-valued metric a strict decrease *is* being realized. The shape
   is what earns its keep: the meta-theorem instantiates uniformly across
   controllers, and a reader does not have to re-derive the collapse.

   This triple assumes a good environment rather than stating one; the
   [preservation_spec] that would cover the bad case does not exist yet. See
   the TODO on [owned_resources] above.

   [rss_post] is existential because the new ReplicaSet may have been created
   during the sync, in which case it is not among the framed [rss]. *)
Definition progress_spec γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq_d : iProp Σ :=
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      (* Progress is claimed only in a good environment: [true]. The
         [preservation_spec] that covers [false] is still to be written. *)
      "Hresources" ∷ owned_resources γ d rss children_keys uid kmeta
        (mutating_fractions dq_d) true ∗
      "%Hinput" ∷ ⌜ input_requirement d rss children_keys namespace name ⌝
  }}}
    @! deployment.syncDeployment #namespace #name
  {{{ (rss_post : list ReplicaSetV.t), RET #interface.nil;
      "Hown_d_meta" ∷ own_meta_frag γ (DeploymentV.key d) uid dq_d kmeta ∗
      "Hown_d_spec" ∷ own_spec_frag γ (DeploymentV.key d) uid dq_d
        (ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')) ∗
      (* Handed back without a phase claim, as replicaset/top_level.v's
         [progress_spec] hands back [owned_resources ... false]: the sync may
         itself have moved the parent out of [Quiescent]. *)
      "Hown_terminating_children" ∷ (∃ control_phase,
        own_terminating_children_frag γ (DeploymentV.key d) uid control_phase) ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss_post,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
      (* The deletion branch is gone: holding the metadata fragment gives
         [kview.own_meta_valid], so the deployment has no deletion timestamp
         under this precondition and [syncDeployment]'s early return is
         unreachable. It used to appear as a vacuous first disjunct. *)
      "%Hnot_deleting" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hprogress" ∷ ⌜ deployment_realized d rss_post ∨
          (rss_progress_observed rss rss_post ∧
           match_distance d rss_post < match_distance d rss) ⌝ ∗
      "%Hunique_new'" ∷ ⌜ unique_new_replica_set d rss_post ⌝ ∗
      (* Either the new ReplicaSet was adopted from [rss], or it was created
         and [rss_post] carries one extra object at [new_rs_key d].

         Stated over the key lists, not the objects: a sync rewrites replica
         counts, and the objects reach the controller through the index in an
         arbitrary order, so [rss_post] is never literally [rss]. What the
         caller needs is which *objects* exist, and that is the keys. *)
      ( ( "%Hadopted" ∷ ⌜ ReplicaSetV.key <$> rss_post ≡ₚ
              ReplicaSetV.key <$> rss ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            uid 1 children_keys)
        ∨
        (* The created ReplicaSet is named because the reservation it fills is
           stamped with *its* UID, not the deployment's — the store records
           which object occupies the reserved key. *)
        ( ∃ new_rs,
          "%Hcreated" ∷ ⌜ ReplicaSetV.key <$> rss_post ≡ₚ
              (ReplicaSetV.key <$> rss) ++ [new_rs_key d] ∧
              new_rs ∈ rss_post ∧
              ReplicaSetV.key new_rs = new_rs_key d ⌝ ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            uid 1 ({[ new_rs_key d ]} ∪ children_keys)))
  }}}.

(* H2 -- stability. Nothing moves, so the postcondition is the precondition.

   No hypothesis on the deletion timestamp: if it is set the controller returns
   before rollout, and if it is not the state is already realized. Both paths
   leave every fragment untouched, unlike [progress_spec] whose branches differ. *)
Definition stability_spec γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq : iProp Σ :=
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hresources" ∷ owned_resources γ d rss children_keys uid kmeta
        (stability_fractions dq) true ∗
      "%Hinput" ∷ ⌜ input_requirement d rss children_keys namespace name ⌝ ∗
      "%Hmatch" ∷ ⌜ deployment_realized d rss ⌝
  }}}
    @! deployment.syncDeployment #namespace #name
  {{{ (err : interface.t), RET #err;
      owned_resources γ d rss children_keys uid kmeta (stability_fractions dq)
        true
  }}}.

End specs.
