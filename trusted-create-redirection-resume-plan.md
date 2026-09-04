# Trusted Create Redirection Resume Plan

Last updated: 2026-09-04, after the Perennial dependency bump, regeneration with
the local patched Goose checkout, and a successful ReplicaSet progress proof.

## Goal

The simple controllers under `controllers/` should call the real Kubernetes Go
API, in the same shape as upstream controllers. Proofs should cross a small
trusted Goose boundary that redirects the real client-go operation to the
corresponding Kubernetes model operation.

The first completed path is ReplicaSet Pod creation:

```go
kubeClient.CoreV1().Pods(namespace).Create(ctx, pod, createOptions)
```

Its proof-facing path is:

```text
Clientset.CoreV1
  -> CoreV1Client.Pods(namespace)
  -> PodInterface.Create(ctx, pod, createOptions)
  -> gentype.Client[*Pod].Create(ctx, pod, createOptions)
  -> apimodel.ModelState.PodCreate(namespace, pod)
```

The controller remains ordinary client-go code. Only the client construction
and final model redirection are trusted.

## Perennial Version Policy

`go.mod` remains pinned to the repository's bumped Perennial version:

```text
github.com/mit-pdos/perennial
  => github.com/uoft-systems-verification/perennial
     v0.0.0-20260818000745-1723ea2029e6
```

Do not add a local `replace` or otherwise edit `go.mod` for this work. Local
Goose experiments use the CLI's `--local` option. Once the required fixes and
features are published, update the pinned Perennial version through the normal
dependency workflow.

## Implemented Controller Change

`controllers/replicaset/replica_set.go` now receives a real
`*clientset.Clientset` and `context.Context`, passes them through
`syncReplicaSet`, and creates Pods through client-go.

The source uses a zero-valued `metav1.CreateOptions` variable. This has the same
Go value as `metav1.CreateOptions{}`, but avoids requiring the proof to reduce a
composite literal for an intentionally opaque imported type.

The controller signature changes have been propagated through the generated
controller semantics and the ReplicaSet preservation, stability, top-level,
and progress proof statements.

## Implemented Trusted Path

### `Clientset.CoreV1`

`src/trusted_code/k8s_io/client_go/kubernetes.v` returns an interface whose
dynamic type is the real generated `*typed/core/v1.CoreV1Client`. Its value is a
typed nil pointer because the next trusted method does not inspect REST client
state.

### `CoreV1Client.Pods`

`src/code/k8s_io/client_go/kubernetes/typed/core/v1.v.toml` now:

- translates `CoreV1Interface`, `PodInterface`, and `pods` type semantics;
- trusts `CoreV1Client.Pods` itself rather than `newPods`;
- imports the real core API, apply-configuration, gentype, and REST packages.

`src/trusted_code/k8s_io/client_go/kubernetes/typed/core/v1.v` implements
`CoreV1Client.Pods` by allocating the exact imported
`gentype.Client[*corev1.Pod]`, recording `namespace`, and returning it through
the real `PodInterface` result. Trusting this public method avoids constructing
the package-private `pods` wrapper, whose same-package type token is not
available to the trusted file under Goose's current generation order.

### `gentype.Client.Create`

`src/code/k8s_io/client_go/gentype.v.toml` translates the generic client types
and trusts `Client.Create`.

`src/trusted_code/k8s_io/client_go/gentype.v`:

- reads the namespace stored in the real generated generic client;
- type-asserts the generic object as `*corev1.Pod`;
- calls `apimodel.ModelState.PodCreate`;
- converts the created Pod back to the generic result type and returns the
  model error.

The context and `CreateOptions` remain in the real method signature but are
ignored by the model shim. The trusted body does not allocate these unused
values; in particular, allocating the opaque `context.Context` interface would
add a proof obligation with no semantic benefit.

The older model wrapper remains generated under
`kubernetes_model/apimodel/wrapper`, but the active Pod path does not use it.
Importing a wrapper only from a trusted Rocq file would not install that Go
package's semantics in the generated assumptions and initialization graph.

## Regeneration and Proofgen Status

The Perennial bump fixed the original generic-parameter capture failure. Local
fixes in `/Users/xudongsun/workspace/perennial` additionally address the later
proofgen failures exposed by this client-go package:

1. representation instances for imported axiomatized field types no longer
   acquire unusable package-semantics dependencies;
2. `trust_proofgen = true` admits the complete generated representation
   instance instead of first elaborating a structural body that is known to be
   unsupported.

Using that checkout through `perennial-cli goose --local` now regenerates the
client-go path and compiles its generated code/proof layers. These fixes are
not yet supplied by the version pinned in `go.mod`, so clean regeneration from
only the pinned dependency remains an integration task.

The historical failures and minimal generic-shadow reproduction are retained
under `goose-repros/` and in the external Perennial checkout for regression
testing.

## Required New Goose Feature

The remaining architectural limitation is exact named-type identity between a
trusted implementation and the Go package containing the replaced declaration.
The current proof uses:

```coq
Transparent client_gentype.Client.
```

and explicitly normalizes `Pod` constants reached through different imported
module aliases. This is a local workaround, not the desired trusted-code API.

The required Goose feature, design alternatives, acceptance fixture, and
Kubernetes acceptance test are documented in
[Goose support needed for trusted same-package named types](goose-trusted-same-package-type-support.md).
The preferred solution gives trusted bodies a generated shared type token; a
minimal solution permits narrowly configured named types to remain transparent.

## Proof Status

The ReplicaSet progress proof now unfolds all three real API calls and reaches
`wp_State__PodCreate_nameless`. It handles:

- the namespace carried by the trusted `Pods` client;
- the generic client's input and output Pod type assertions;
- the real `Create` result shape `(*Pod, error)`;
- the existing Pod ownership and controller-children ghost state.

The required focused target passes without admits:

```sh
make -j10 src/proof/controllers/replicaset/progress.vo
```

The successful incremental run took 337.50 seconds.

The remaining local verification also passes:

```text
make -j10 src/proof/controllers/replicaset/top_level.vo   PASS (up to date, 0.69 s)
GOCACHE=/tmp/go-build scripts/test_model.sh 5             PASS (5/5, 172.92 s)
(cd controllers && go test ./...)                         PASS (5.24 s)
git diff --check                                           PASS
git diff -- go.mod controllers/go.mod                      empty
```

## Remaining Work

1. Upstream and publish the proofgen fixes, implement the trusted same-package
   named-type feature, and bump the pinned Perennial version normally.

2. Regenerate without `--local`, remove the proof-local `Transparent` and
   alias-normalization workaround where the new feature makes them unnecessary,
   and re-run the same proof targets.

3. Apply the same pattern to other simple controller operations: keep the Go
   controller on the real Kubernetes API, trust the smallest client-go shim,
   and redirect that shim to the corresponding model operation.

## Regeneration and Consistency Checks

Regenerate only from source/config inputs; never hand-edit `src/code` or
`src/generatedproof`.

```sh
/usr/bin/time -p go tool perennial-cli goose \
  --config goose-kubernetes.toml \
  --local /Users/xudongsun/workspace/perennial/goose

python3 scripts/optimize_generated_proofs.py \
  --optimize-into-val-typed PodSpec,VolumeSource \
  --optimize-access PodSpec,VolumeSource \
  src/generatedproof/k8s_io/api/core/v1.v
```

Check that the trusted hooks remain present:

```sh
rg -n 'Client__Createⁱᵐᵖˡ|Client.*Create_unfold' \
  src/code/k8s_io/client_go/gentype.v \
  src/trusted_code/k8s_io/client_go/gentype.v

rg -n 'CoreV1Client__Podsⁱᵐᵖˡ|CoreV1Client.*Pods_unfold' \
  src/code/k8s_io/client_go/kubernetes/typed/core/v1.v \
  src/trusted_code/k8s_io/client_go/kubernetes/typed/core/v1.v

git diff -- go.mod
```

The final command must remain empty.

## Constraints

- Do not edit `go.mod` to select a local Perennial checkout.
- Do not hand-edit generated files under `src/code` or `src/generatedproof`.
- Keep trusted code limited to API-to-model translation; do not trust the
  controller.
- Keep all named types opaque by default when implementing the Goose feature.
- The first supported operation is Pod create; additional resources and verbs
  should be added incrementally with corresponding model specifications.
