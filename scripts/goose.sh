#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."

# Goose emits standard-library declarations, which can change between Go patch
# releases. Use the exact version from go.mod even if a newer Go is installed.
export GOTOOLCHAIN="go$(awk '$1 == "go" { print $2; exit }' go.mod)"

python3 scripts/generate_views.py --config

go tool perennial-cli goose --config goose-kubernetes.toml
go tool perennial-cli goose --config goose-kubernetes-model.toml
go tool perennial-cli goose --config goose-controllers.toml
go tool perennial-cli goose --config goose-iam.toml
go tool perennial-cli goose --config goose-benchmark.toml

# Limit post-processing to these generated proof files. The value may contain
# multiple whitespace-separated paths; core/v1.v is the default target.
GOOSE_PROOF_OPTIMIZER_TARGETS="${GOOSE_PROOF_OPTIMIZER_TARGETS:-src/generatedproof/k8s_io/api/core/v1.v}"

# Optimize Pod records with at least ten fields.
# Lists are comma-separated.
# Set an explicit empty value to disable either optimization independently.
POD_LARGE_STRUCTS="PodSpec,VolumeSource,Container,ContainerStatus,EphemeralContainerCommon,PodStatus"
POD_LARGE_STRUCTS+=",PodSecurityContext,SecurityContext,ISCSIVolumeSource,ScaleIOVolumeSource"
GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED="${GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED-$POD_LARGE_STRUCTS}"
GOOSE_PROOF_OPTIMIZER_ACCESS="${GOOSE_PROOF_OPTIMIZER_ACCESS-$POD_LARGE_STRUCTS}"

# Add each optional flag only when at least one struct is selected.
OPTIMIZER_ARGS=()
if [[ -n "$GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED" ]]; then
  OPTIMIZER_ARGS+=(
    --optimize-into-val-typed "$GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED"
  )
fi
if [[ -n "$GOOSE_PROOF_OPTIMIZER_ACCESS" ]]; then
  OPTIMIZER_ARGS+=(
    --optimize-access "$GOOSE_PROOF_OPTIMIZER_ACCESS"
  )
fi

# Run after Goose so regenerated one-line proofs are replaced deterministically.
python3 scripts/optimize_generated_proofs.py \
  "${OPTIMIZER_ARGS[@]}" \
  $GOOSE_PROOF_OPTIMIZER_TARGETS

# Apply the same optimization to apps records with at least ten fields.
python3 scripts/optimize_generated_proofs.py \
  --optimize-into-val-typed StatefulSetSpec,StatefulSetStatus \
  --optimize-access StatefulSetSpec,StatefulSetStatus \
  src/generatedproof/k8s_io/api/apps/v1.v

python3 scripts/generate_views.py
