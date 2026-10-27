# StatefulSet proof status

The active proofs cover the revision-label getter, setter, and matcher, and the
retained ordinal, Pod/PVC construction, identity, storage, release, and deletion
helpers. The pure legacy desired-state and distance predicates remain available
for migration; their lemmas do not establish correctness of the new rollout
decisions.

The obsolete PodSpec-comparison program proofs were removed because they referred
to deleted functions and no longer matched the Go controller. Their top-level
contracts remain commented in `top_level.v` as migration references. This also
removes the old `wp_podSpecMatches` admission. Previous proof versions remain
available in Git history.

## TODO Replace the controller contracts and proofs

- TODO: extend the resource account in `top_level.v` with ControllerRevision
  metadata/spec fragments, mixed Pod/revision child sets, StatefulSet status
  resources, revision allocation/deletion permissions, and Pod-status observations.
- TODO: replace the old full-PodSpec desired-state predicates with separate
  revision membership, provenance, structural correctness, and policy completion
  predicates. Preserve OnDelete and rolling-partition behavior.
- TODO: prove revision creation, collision handling, semantic reuse, rollback,
  restoration, selection, status persistence, and history cleanup.
- TODO: replace `outdated.v` with revision-based selection and ordering proofs
  for the current `largestOutdatedPod`, including availability and termination.
- TODO: replace the `reconcile_*` proofs for the current function signatures,
  versioned Pod construction, and partial success/error behavior.
- TODO: restore top-level preservation, progress, and stability proofs against
  revision-aware contracts. Account for history/status writes and explicit
  readiness, availability, deletion, and retry outcomes.

Needed replacement lemmas may temporarily use `Admitted.` with a nearby TODO
describing the remaining obligation. State their contracts against the current
implementation first. Keep temporary admissions visible and distinguish those
lemmas from completed proofs. Do not reinstate the obsolete comparison contracts.
