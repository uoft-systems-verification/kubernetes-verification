# Object view generator

[`scripts/generate_views.py`](../scripts/generate_views.py) generates pure views
and ownership predicates from the checked-out Kubernetes Go structs. The resource
views cover Pod, PersistentVolumeClaim, ReplicaSet, StatefulSet, Deployment,
ControllerRevision, DaemonSet, and Node, including nested spec and status fields.

The generator runs [`scripts/extract_schema.go`](../scripts/extract_schema.go)
from the Kubernetes module to reflect the configured root types and their nested
fields. Python creates a temporary Go entry point containing the selected imports
and roots; the helper itself contains no Kubernetes type selections. Temporary
sources are removed when reflection finishes, including on failure.
It selects the Go version declared in the root `go.mod`, matching
`scripts/goose.sh`. Python needs `tomllib`, available in Python 3.11 and later.

## Generated definitions and specifications

[`src/generatedviews`](../src/generatedviews) contains the generated field views,
ownership predicates, and supporting lemmas.

Let `V(T)` denote the view type of a Go type `T`. The generator uses these mappings:

| Go type | Rocq view type | Notes |
| --- | --- | --- |
| `string` | `go_string` | Named string types use the same representation. |
| `bool` | `bool` | Named boolean types use the same representation. |
| `int`, `int64`, `uint`, `uint64` | `w64` | Signed and unsigned types share the word representation. |
| `int32`, `uint32`, `rune` | `w32` | `rune` is an alias for `int32`. |
| `int16`, `uint16` | `w16` | Signed and unsigned types share the word representation. |
| `int8`, `uint8`, `byte` | `w8` | `byte` is an alias for `uint8`. |
| Struct `T` | Generated view module's `t`, such as `PodView.PodV.t` | Included fields are represented recursively. A struct aliases its Goose record type only if it contains scalar fields (including nested structs) and has no exclusions anywhere inside it. |
| `*T` | `option (V(T))` | `None` represents nil; `Some v` represents an allocated pointee. |
| `[]T` | `option (list (V(T)))` | `None` represents nil; `Some []` represents an allocated empty slice. Ownership includes backing capacity. |
| `map[string]T` | `option (gmap go_string (V(T)))` | `None` represents nil; `Some ∅` represents an allocated empty map. Keys must have underlying kind `string`. |
| Internal `math/big.nat` word buffer | `list w64` | Nil and allocated empty buffers both map to `[]`; ownership still includes backing storage and capacity. |
| Field listed in `exclude_fields` | Omitted | The field is absent from the view record, `of_go`, zero value, and `deepown`. The generated module includes a comment explaining the exclusion. |

Named integer types follow the mapping for their underlying Go kind. Structs
whose represented fields require no heap ownership have pure ownership predicates
and an `of_go` projection.

## Generate and check views

Run these commands from the repository root. To update Goose translation
configuration, regenerate Go translations, and regenerate views together:

```sh
scripts/goose.sh
```

When the Go translations are already current, regenerate only the views with:

```sh
python3 scripts/generate_views.py
```

To check whether the views match the current Kubernetes types and ownership
configuration without writing files:

```sh
python3 scripts/generate_views.py --check
```

The check exits with an error if a generated view is missing or stale.

| Option | Behavior |
| --- | --- |
| `--config` | Update Goose `.v.toml` translation configuration under `src/code` and exit without generating views. This runs automatically through `scripts/goose.sh`. |
| `--check` | Check the generated views without writing files. Cannot be combined with `--config`. |
| `--view-config PATH` | Read roots, output groups, Rocq contexts, and ownership choices from this TOML file. Defaults to `scripts/generate_views.toml`. |
| `--output-dir DIR` | Write or check views in this directory. Defaults to `src/generatedviews`. |
| `--schema FILE` | Reuse a saved JSON reflection schema for development, skipping Go reflection. Omit this option when checking against the current Go types. |

## Configuring the generated views

[`scripts/generate_views.toml`](../scripts/generate_views.toml) defines which
types to reflect, where their views go, and how ownership is presented.
The `PACKAGES` mapping stays in Python: it describes supported Go packages and
their Goose module paths and local Rocq aliases.

| Setting | Meaning |
| --- | --- |
| `[groups.NAME]` | Write `NAME.v`. Groups are processed in declaration order; the first group reaching a nested type owns its view, and later groups reuse it. |
| `module` | Outer Rocq module in the output file. |
| `roots` | Named Go struct type IDs, written as `package/path/TypeName`. The package must be in `PACKAGES`; root names must be exported. Nested fields are reflected automatically. |
| `context` | Select a shared `[contexts.NAME]` table for the group's imports and semantic assumptions. |
| `exports` | Optional table of module aliases emitted after the outer module, such as `{ TimeV = "MetaTimeView.TimeV" }`. |
| `[contexts.NAME]` | Reusable Rocq setup: `imports` lists qualified modules to export, `aliases` selects local aliases from `PACKAGES`, and `assumptions` maps binder names to those aliases. Their configured order is preserved. |
| `named_collections` | Top-level list of Go struct type IDs whose collection fields retain named nilness, contents, and capacity components used by existing proofs. Other structs use the general ownership helpers. This changes predicate presentation, not which fields are represented or owned. |
| `[exclude_fields."TYPE"]` | Fields omitted from both the view and ownership, with explanations as described below. |

For example, adding another root and output group using the existing core context
requires only a table in the configuration:

```toml
[groups.service]
module = "ServiceView"
roots = ["k8s.io/api/core/v1/Service"]
context = "core"
```

Put this group after groups whose shared views it should reuse, then run
`scripts/goose.sh` to update translations and generate its views. Adding a new Go
package also requires extending `PACKAGES` and providing the appropriate Rocq
context. Imports and assumptions must cover the represented types and their
generated proofs.

When using `--schema`, the saved schema's root groups must match the configuration.
Changing roots or group names requires reflecting again without `--schema`.

## Field exclusions

Field exclusions are configured in
[`scripts/generate_views.toml`](../scripts/generate_views.toml), or an alternative
file supplied with `--view-config`. An excluded field is omitted from both the
view and its ownership predicate. The same filtered field list drives the record,
`of_go`, zero value, and `deepown`. Every entry includes a reason, emitted as a
comment in the generated module. Included fields follow the normal type mapping.

Tables use fully qualified Go type IDs, followed by exact Go field names:

```toml
[exclude_fields."time/Time"]
loc = "The timezone location is shared runtime state and may be lazily initialized."
```

For example, `time/Time.loc` is excluded because timestamps share runtime-managed
timezone memory that Go may initialize lazily. The timestamp view contains only
`wall` and `ext`, which are sufficient for instant comparisons. View equality
ignores timezone pointer identity. Proofs that inspect an omitted field need
additional facts about the concrete Go value; dereferencing its pointer also
requires ownership or an invariant for the referenced memory.

The generator rejects unknown types or fields, empty explanations, and
explanations containing Rocq comment delimiters. Fields without an exclusion
retain their usual representation and ownership.

## Using large predicates in proofs

Generated ownership predicates for structs with heap ownership and at least
10 included fields are opaque by default. Use the generated `deepown_unfold` lemma, or
enable `Local Transparent` for the relevant predicate when a proof needs its
fields. For example:

```coq
Local Transparent PodView.PodSpecV.deepown.
```

A repeated Pod getter experiment reduced total checking time from about 14.3 s
to 6.8 s (tactic time from 10.6 s to 3.1 s) with large predicates opaque; the
ObjectMeta getter showed a smaller improvement, from about 6.0 s to 5.2 s. These
are focused local experiments, not whole-project build speedups.

ControllerRevision is also a root, with an explicit `runtime.RawExtension`
representation. Interface fields are retained in views and ownership restricts
both the physical and view interface values to nil. Thus the supported revision
path uses `Raw` bytes with `Object=nil`; non-nil runtime objects are not silently
ignored or claimed to be owned. Supporting them would require a dynamic,
implementation-specific ownership relation. Data and the mutable Revision
counter belong to the ordinary-update body; the formal status projection is
empty and has no status-update operation.
