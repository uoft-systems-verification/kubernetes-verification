# Trusted Create Redirection Resume Plan

## Goal

Redirect translated client-go `gentype.Client.Create` away from the REST API and
into the Kubernetes model API, using Goose trusted code in the same style as
Perennial's `trusted_code/sync.v`.

Target proof-facing call path:

```go
r.KubeClient.CoreV1().Pods(namespace).Create(ctx, pod, metav1.CreateOptions{})
```

should reason about:

```coq
gentype.Client__Createⁱᵐᵖˡ
  -> kubernetes_model.apimodel.wrapper.Client__Createⁱᵐᵖˡ
  -> apimodel.ModelState.PodCreate
```

## Current Implementation State

The trusted-code wiring has already been implemented.

Relevant source/config inputs:

- `goose-kubernetes.toml`
  - added `./staging/src/k8s.io/client-go/gentype`
  - added `./staging/src/k8s.io/client-go/applyconfigurations/core/v1`
- `src/code/k8s_io/client_go/gentype.v.toml`
  - translates the real `Client`, `ClientWithList*`, `alsoLister`,
    `alsoApplier`, `Option`, and constructor definitions needed by the pod
    client path
  - trusts `Client.Create`
  - keeps `namedObject` axiomatized to avoid unsupported `go.comparable`
- `src/code/k8s_io/client_go/kubernetes/typed/core/v1.v.toml`
  - translates `CoreV1Client.Pods` and `pods`
  - imports `k8s.io/api/core/v1`,
    `k8s.io/client-go/applyconfigurations/core/v1`, and
    `k8s.io/client-go/gentype`
  - trusts `newPods`
- `src/trusted_code/k8s_io/client_go/gentype.v`
  - defines trusted `Client__Createⁱᵐᵖˡ`
  - reads the real generated `gentype.Client` namespace field
  - constructs `kubernetes_model/apimodel/wrapper.Client`
  - delegates to wrapper `Create`
- `src/trusted_code/k8s_io/client_go/kubernetes/typed/core/v1.v`
  - defines trusted `newPodsⁱᵐᵖˡ`
  - constructs a generated `pods` value with an embedded gentype client
  - preserves the selected namespace and ignores REST/codec fields
- `src/manualproof/k8s_io/client_go/gentype.v`
  - empty manualproof stub required because generated code imports trusted code
- `src/manualproof/k8s_io/client_go/kubernetes/typed/core/v1.v`
  - empty manualproof stub for typed core/v1

The model-facing wrapper is in:

- `kubernetes_model/apimodel/wrapper/wrapper.go`
- generated Rocq: `src/code/kubernetes_model/apimodel/wrapper.v`

## Current Blocker

Generated executable Rocq code compiles, but generatedproof for `gentype` is
blocked by a Goose proofgen hygiene bug.

Failure:

```sh
make -j10 src/generatedproof/k8s_io/client_go/kubernetes/typed/core/v1.vo
```

fails while compiling:

```text
src/generatedproof/k8s_io/client_go/gentype.v
```

with a type-parameter collision around `C`:

```text
The term "C" has type "iProp ?Σ0" while it is expected to have type "go.type".
```

Details and a minimal reproduction are documented in:

```text
goose-proofgen-typeparam-collision.md
```

After fixing Goose proofgen, regenerate before continuing.

## Resume Steps After Fixing Goose

1. Point this repo at the local fixed Perennial checkout.

   Example `go.mod` entry:

   ```go
   replace github.com/mit-pdos/perennial => /path/to/local/perennial
   ```

2. Confirm Go uses the local Perennial checkout.

   ```sh
   go list -m -f '{{.Path}} => {{with .Replace}}{{.Path}} {{.Version}} {{.Dir}}{{else}}{{.Version}} {{.Dir}}{{end}}' github.com/mit-pdos/perennial
   ```

3. Regenerate all Goose outputs.

   ```sh
   /usr/bin/time -p scripts/goose.sh
   ```

4. Re-check the trusted-code generated code targets.

   ```sh
   /usr/bin/time -p make -j10 src/code/k8s_io/client_go/gentype.vo
   /usr/bin/time -p make -j10 src/code/k8s_io/client_go/kubernetes/typed/core/v1.vo
   ```

5. Re-check generatedproof for the new client-go path.

   ```sh
   /usr/bin/time -p make -j10 src/generatedproof/k8s_io/client_go/gentype.vo
   /usr/bin/time -p make -j10 src/generatedproof/k8s_io/client_go/kubernetes/typed/core/v1.vo
   ```

6. Re-run the Kubernetes model test.

   ```sh
   /usr/bin/time -p zsh -lc 'GOCACHE=/tmp/go-build scripts/test_model.sh 5'
   ```

7. Re-run the existing controller proof surface.

   ```sh
   /usr/bin/time -p make -j10 src/proof/controllers/replicaset.vo
   ```

8. If a proof is added for the real Kubernetes controller call path in
   `kubernetes/pkg/controller/controller_utils.go`, first update
   `src/code/k8s_io/kubernetes/pkg/controller.v.toml` to translate the relevant
   method containing `RealPodControl.createPods`, regenerate, and prove that
   the translated call unfolds through:

   ```coq
   CoreV1Client__Podsⁱᵐᵖˡ
   newPodsⁱᵐᵖˡ
   gentype.Client__Createⁱᵐᵖˡ
   wrapper.Client__Createⁱᵐᵖˡ
   apimodel.State__PodCreateⁱᵐᵖˡ
   ```

## Expected Checks

After regeneration, verify the generated files still show the intended trusted
hooks:

```sh
rg -n 'trusted_code.k8s_io.client_go.gentype|Client__Createⁱᵐᵖˡ|Client.*Create_unfold' \
  src/code/k8s_io/client_go/gentype.v \
  src/trusted_code/k8s_io/client_go/gentype.v

rg -n 'trusted_code.k8s_io.client_go.kubernetes.typed.core.v1|newPodsⁱᵐᵖˡ|newPods_unfold' \
  src/code/k8s_io/client_go/kubernetes/typed/core/v1.v \
  src/trusted_code/k8s_io/client_go/kubernetes/typed/core/v1.v

rg -n 'PodCreate|ReplicaSetCreate' src/code/kubernetes_model/apimodel/wrapper.v
```

`src/code/k8s_io/client_go/gentype.v` should import:

```coq
Require Export New.trusted_code.k8s_io.client_go.gentype.
```

and should not contain the original REST-chain implementation of
`Client.Create`.

## Notes

- Do not manually edit generated files under `src/code` or
  `src/generatedproof`; update source/config/trusted files and regenerate.
- The trusted `newPods` intentionally ignores REST client and codec values,
  because trusted `Client.Create` only needs namespace and the object.
- The current implementation targets the Pod create path first. ReplicaSet
  create is already handled inside the model wrapper type switch, but the
  apps/v1 client construction path may need analogous trusted/translated wiring
  before proofs can reach it through client-go.
