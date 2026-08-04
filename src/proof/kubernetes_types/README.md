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
| `ObjectMetaV.valid_named_create kind ns meta` | A create request supplies `metadata.name`; its namespace is empty or agrees with the request URL, and its user-controlled metadata passes validation. |
| `ObjectMetaV.valid_nameless_create kind ns meta` | A create request omits `metadata.name` and supplies a valid, short enough `generateName` from which the API server can choose a name. |
| `KObjectV.valid_named_create` / `valid_nameless_create` | The full request-level condition: correct resource kind, create-compatible TypeMeta and metadata, and a create-valid spec. |
| `V.valid_update old new` | The cross-object rules for an update, especially immutable fields. This is used together with validity of the individual objects. |
| `V.valid stored` | The stronger invariant guaranteed of the modeled part of an object after it has been prepared, defaulted/normalized, and stored by the API server. |
| `V.created input stored` | The relation between a create request projection and the projection that the server stores. |
| `V.updated input stored` | The corresponding relation after update preparation/defaulting. |

These are Rocq propositions used in specifications. Some are executable
definitions with `Decision` instances; others are axiomatized where the
corresponding Go fields have not yet been translated.

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
model's store. It requires valid TypeMeta and resource version, complete
stored metadata, a stored-valid spec, and a stored-valid status.

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
5. Describe server changes in `created` and `updated`; do not silently assume
   request and stored values are equal across a defaulting boundary.
6. Add `Decision` instances where the proposition is concrete. If a component
   must remain axiomatic, document the upstream guarantee represented by the
   axiom.
7. Update the `ObjectSpecV`, `ObjectStatusV`, and `KObjectV` dispatchers when a
   new resource kind is introduced.

The central rule is to keep three questions separate: **what pure value does
this Go heap represent, which values may Kubernetes accept at this stage, and
how may Kubernetes transform the value before returning or storing it?**
`deepown`, the validity predicates, and the create/update relations answer
those questions respectively.

## TODO

- Generalize `valid_update` so that `old` does not have to be a `valid`
  object, and refactor `updated` accordingly.
