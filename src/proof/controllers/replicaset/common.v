(* Helper lemmas shared by the ReplicaSet controller's progress, preservation and
   stability proofs. These are specific to this controller, so they stay out of
   controllers/common.v, which the other controllers import too. Everything here
   is pure, hence no [Section] and no ghost-state context. *)
From New.proof.controllers.replicaset Require Export top_level.
From New.proof Require Export util.

(* Replica arithmetic of one sync under the burst cap: the controller moves the
   live replica count toward the desired count by at most [burst]. *)
Definition replica_distance (actual desired : nat) : nat :=
  ((actual - desired) + (desired - actual))%nat.

Definition capped_replica_count (actual desired burst : nat) : nat :=
  if decide (actual < desired)%nat then (actual + Nat.min (desired - actual) burst)%nat
  else (actual - Nat.min (actual - desired) burst)%nat.

Lemma capped_replica_count_distance actual desired burst :
  (replica_distance (capped_replica_count actual desired burst) desired +
    Nat.min (replica_distance actual desired) burst = replica_distance actual desired)%nat.
Proof. unfold capped_replica_count, replica_distance. destruct (decide _); lia. Qed.

Lemma match_distance_replica_distance rs pods n :
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n →
  match_distance rs pods = replica_distance (length (filter is_pod_alive pods)) (sint.nat n).
Proof. intros Hreplicas. unfold match_distance. rewrite Hreplicas. done. Qed.

Lemma active_pod_count_erased_meta_perm pods1 pods2 :
  ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2) →
  length (filter is_pod_alive pods1) = length (filter is_pod_alive pods2).
Proof.
  intros Hperm.
  assert (Hcount : ∀ pods,
    length (filter is_pod_alive pods) =
    length (filter (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
      (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods)))).
  { intros pods. induction pods as [|pod pods IH]; simpl; first done.
    destruct (decide (is_pod_alive pod)) as [Halive|Hnot_alive].
    - destruct (decide ((ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta')).(ObjectMetaV.DeletionTimestamp') = None))
        as [Herased_alive|Hnot_erased_alive].
      + rewrite (filter_cons_True is_pod_alive pod pods Halive).
        rewrite (filter_cons_True
          (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
          (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))
          (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))
          Herased_alive).
        simpl. f_equal. exact IH.
      + exfalso. apply Hnot_erased_alive.
        unfold is_pod_alive, ObjectMetaV.without_resource_version in *.
        destruct pod as [? [] ? ?]. exact Halive.
    - destruct (decide ((ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta')).(ObjectMetaV.DeletionTimestamp') = None))
        as [Herased_alive|Hnot_erased_alive].
      + exfalso. apply Hnot_alive.
        unfold is_pod_alive, ObjectMetaV.without_resource_version in *.
        destruct pod as [? [] ? ?]. exact Herased_alive.
      + rewrite (filter_cons_False is_pod_alive pod pods Hnot_alive).
        rewrite (filter_cons_False
          (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
          (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))
          (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))
          Hnot_erased_alive).
        exact IH. }
  rewrite !Hcount.
  apply Permutation_length.
  apply perm_filter.
  exact Hperm.
Qed.
