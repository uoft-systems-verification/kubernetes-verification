The local controller persists apps/v1 ControllerRevisions and uses
`controller-revision-hash` Pod labels to decide rolling replacements. The label
value is the ControllerRevision name. Live PodSpec defaulting, admission changes,
and scheduling do not change this rollout decision. Ordinary identity repair
preserves the revision label; it does not repair immutable hostname, subdomain,
or storage fields of existing Pods.

The behavior reference is the vendored Kubernetes commit
`17044946fab00c49e29adee01319809ef17d9283`. History captures only the Pod template,
including its labels and annotations. It reuses equivalent latest revisions,
increments an older equivalent revision's counter on rollback, compares restored
and defaulted templates semantically, and retries name collisions after comparing
payloads. A same-name StatefulSet with a different UID cannot reuse that history.
History cleanup preserves current/update and all Pod-referenced revisions,
including references from terminating Pods.

Supported policy scope is OrderedReady, zero start ordinal, OnDelete or
RollingUpdate with an optional partition, minReadySeconds, and one destructive
update per reconciliation. Parallel policy and nonzero start ordinals return
explicit errors. The optional semantic-equality LRU cache is omitted. Non-default
feature gates, adoption, concurrent reconciliation, and PVC retention owner
reference management remain unsupported. Reconciliation releases owned Pods with
bad names as before. A deleting StatefulSet is left untouched, including its
status. API-valid inputs must also produce admissible Pod/PVC
requests, including revision names valid as Pod label values.

History updates and status writes use optimistic resource versions. A conflict
returns an error for retry from a fresh observation. No hash-injectivity
assumption is made. ControllerRevision Data uses encoded Raw bytes with
Object=nil; applying a revision with a non-nil Object returns an explicit error.
The API model continues to run the upstream strategy validation rather than
silently discarding alternate runtime representations.

An editable Pod revision label is a rollout signal, not evidence of the Pod's
body or construction history. Structural guarantees require a creation invariant
and assumptions restricting interference. Readiness, availability, deletion,
and API retries can cause calls without progress. Convergence additionally
requires a stable desired template, successful retries, readiness progress, and
completion of pending deletions. OnDelete requires manual removal of old Pods;
partitioned updates intentionally retain existing Pods below the partition.

Formal migration is in progress. The new object/view representation and revision
predicates distinguish membership from historical provenance and model explicit
waiting/retry outcomes. The metadata-only revision-label getter, setter, and
matcher program proofs have been checked. The previous StatefulSet distance and
top-level program proofs described the old comparison-based controller. The
obsolete program proofs and top-level contracts have been removed; their
[replacement obligations](../../src/proof/controllers/statefulset/README.md) are
marked TODO. CI checks the retained helper proofs, but does not establish
top-level correctness of this implementation until the migration is complete.
The obsolete `wp_podSpecMatches` admission has been removed as well.

Selected generic/API Create, Get, List, Update, Delete, and status proof targets
have also been checked with ControllerRevision included. Its ordinary-update
contract is a sufficient precondition requiring current create validity of the
input, as in the existing generic resource contracts; it does not characterize
all updates of legacy metadata accepted by Kubernetes.
