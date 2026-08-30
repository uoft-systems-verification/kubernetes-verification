# Views (`V`) of Kubernetes types

The `V` types in this directory are the abstract representations of the Go
objects used by the model. The generated Goose types describe how those
objects are laid out in Go memory; the `V` types describe their pure,
value-level meaning in Rocq.

## Why do we need `V` types?

One important reason for this distinction is that pointers such as `loc`
should not appear in the abstract representation of the Kubernetes cluster
state in `kubernetes_model`. The abstract store should record the values of
Kubernetes objects, not the Go memory addresses at which a particular
execution happens to allocate them. Otherwise, two identical objects stored
at different addresses would produce different abstract cluster states and
expose an irrelevant implementation detail to controller correctness proofs.
The physical Go store and its addresses are instead related to this
address-free abstract state through `deepown` and the API-model invariant.

A corresponding `V.t` is a pure projection of the fields that the current
verification needs. It replaces heap representation with ordinary Rocq data:

| Go representation | Typical pure view |
| --- | --- |
| `*T` | `option T` or `option T_V` |
| `[]T` | `option (list T_V)` |
| `map[K]V` | `option (gmap K V)` |

## `deepown`: connecting a pure value to Go memory

The pure view is useful only if a proof can connect it to the program's
actual object. That connection is the separation-logic assertion

```coq
deepown (c : generated_go_type) (v : V.t) (dq : dfrac) : iProp Σ
```

It says that the shallow Goose value `c` represents the pure value `v`, and
provides ownership (with permission `dq`) of the modeled heap reachable from
`c`. For example, `ReplicaSetSpecV.deepown` says that the Go `Replicas`
pointer is null exactly when the pure `Replicas'` field is `None`. If it is
`Some n`, the assertion owns the pointed-to cell and says that the cell
contains `n`.

## Validation follows the real API lifecycle

We need several validity predicates because whether a Kubernetes object is
valid depends on both the operation being performed and the object's stage in
the API lifecycle. A create request may omit fields that the API server later
defaults, while a stored object must satisfy stronger invariants. An update
must additionally be compared with the existing object to enforce rules such
as field immutability, and the resulting object may differ from the submitted
one after preparation and canonicalization.

| Proof definition | Meaning in Kubernetes |
| --- | --- |
| `SpecV.valid_create input` | The modeled spec is admissible as request input. It may omit fields that Kubernetes defaults before storage. |
| `ObjectMetaV.valid_create kind ns meta` | Validates common create metadata and branches on whether `metadata.name` is empty; nameless requests require a valid, short enough `generateName`, while named requests require a valid name. |
| `KObjectV.valid_create` | The full request-level condition for either name mode: create-compatible TypeMeta and metadata, and a create-valid spec. The `KObjectV` constructor determines the resource kind. Specialized operations state `metadata.name` emptiness separately when needed. |
| `V.valid_update old input` | Top-level validation of submitted update input against the stored old value. It includes ordinary validation and accounts directly for preparation affecting represented fields. |
| `KObjectV.created namespace input stored` | Relates the submitted create request to the object stored after a successful create. |
| `KObjectV.updated old input stored` | Relates the existing object, submitted update, and object stored after a successful update. |
| `KObjectV.valid_update old input` | Top-level update-validation contract over the existing stored object and submitted input; intermediate prepared objects are not exposed. |
| `KObjectV.status_updated old input stored` | Relates the existing object and submitted status update to the object stored after a successful status update. |
| `KObjectV.valid_status_update old input` | Top-level status-update validation over the existing stored object and submitted input. |
| `KObjectV.valid stored` | The invariant guaranteed of the modeled part of an object stored by the API server. |
| `V.extra_valid stored` | A condition not enforced by the API server but required by verified controllers. It is expected to hold for realistic objects; violating it would generally require impractically large values. |
| `SpecV.created input stored` / `SpecV.updated old input stored` | Relations between the submitted component and the corresponding component of the stored object. |
| `StatusV.created input stored` / `StatusV.updated input stored` | Relations between the submitted status and the corresponding status of the stored object. |

These are Rocq propositions used in specifications. The `created`, `updated`,
and `status_updated` relations describe the complete operation from submitted
input to stored output. They are relations because the pure views omit fields
that can influence the exact stored value.

### Controller requirements are separate from API validity

`KObjectV.valid` contains properties attributed to API validation and storage
normalization. `KObjectV.extra_valid` separately records assumptions required
by verified controller implementations that Kubernetes admission does not
enforce. The authoritative `kview` invariant requires both for every stored
object, so the modeled state is the supported subset on which the verified
controllers execute safely; `extra_valid` must not be cited as an admission
guarantee about arbitrary real clusters.

The ReplicaSet branch currently requires every present selector to satisfy
`LabelSelectorV.extra_valid`, the Go-size bound needed by
`LabelSelectorAsSelector`. Structural selector validity remains in ordinary API
validity. Other object kinds currently reduce to `True`. Adding a nontrivial
branch requires proving it at every model transition that can store that kind
and exposing it from the relevant read specifications.

### Create validity is intentionally weaker than stored validity

A legal create request is not generally a legal stored object. In the modeled
Kubernetes API:

- a request may omit TypeMeta because the endpoint and decoder determine it;
- a request may leave its namespace empty because the request URL supplies it;
- a request may use `generateName` instead of `name`;
- UID, resource version, creation timestamp, and sometimes generation are
  assigned or controlled by the server;
- resource schemas can default omitted fields; and
- the Pod, ReplicaSet, StatefulSet, and PVC create strategies reset status, so
  their request predicates do not require the submitted status to be valid.

By contrast, `KObjectV.valid` is the invariant used for an object in the API
model's store. It requires TypeMeta to be omitted or compatible with the
concrete type, a valid resource version, complete stored metadata, a
stored-valid spec, and a stored-valid status.

`created`, `updated`, and `status_updated` relate submitted requests directly
to newly stored objects. They leave server-assigned values unspecified where
the model does not need to determine those values exactly.

`ObjectMetaV.valid` also includes storage normalization represented by this
model, such as `selfLink = ""`. It deliberately does not include the resource
version predicate because some metadata-only ghost fragments do not carry the
resource version; `KObjectV.valid` adds that condition at the whole-object
level.

## Extending a value model

When adding a resource or field:

1. Add the pure field to the appropriate `V.t`. Preserve nil separately for
   pointer, slice, and map fields. In particular, use an `option` for a slice
   or map even if a particular Kubernetes operation treats nil and empty
   alike. Add a helper that collapses the distinction for that operation when
   needed.
2. Extend `deepown` to relate the field to its Go representation and own every
   newly modeled reachable allocation.
3. Put request-admission facts in `valid_create` and persistent
   post-defaulting/normalization facts in `valid`.
4. Add the old/new constraints enforced by Kubernetes to `valid_update`.
5. Extend `created`, `updated`, and `status_updated` as end-to-end relations. Keep intermediate
   preparation inside the top-level validation predicates, and leave omitted
   view fields unconstrained.
6. Add `Decision` instances where the proposition is concrete. If a component
   must remain axiomatic, document the upstream guarantee represented by the
   axiom.
7. Update the `ObjectSpecV`, `ObjectStatusV`, and `KObjectV` validation and
   normalization dispatchers when a new resource kind is introduced.

The central rule is to keep three questions separate: **what pure value does
this Go heap represent, which values may Kubernetes accept at this stage, and
how may Kubernetes transform the value before returning or storing it?**
`deepown`, the validity predicates, and the create/update normalization APIs
answer those questions respectively.
