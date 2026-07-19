#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."

go tool perennial-cli goose --config goose-kubernetes.toml
go tool perennial-cli goose --config goose-kubernetes-model.toml
go tool perennial-cli goose --config goose-controllers.toml
go tool perennial-cli goose --config goose-iam.toml
go tool perennial-cli goose --config goose-benchmark.toml

# Limit post-processing to these generated proof files. The value may contain
# multiple whitespace-separated paths; core/v1.v is the default target.
GOOSE_PROOF_OPTIMIZER_TARGETS="${GOOSE_PROOF_OPTIMIZER_TARGETS:-src/generatedproof/k8s_io/api/core/v1.v}"

# Select PodSpec and VolumeSource for both optimizations by default. Each variable accepts a
# comma-separated struct list and can be set to an explicit empty value to
# disable that optimization independently.
GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED="${GOOSE_PROOF_OPTIMIZER_INTO_VAL_TYPED-PodSpec,VolumeSource}"
GOOSE_PROOF_OPTIMIZER_ACCESS="${GOOSE_PROOF_OPTIMIZER_ACCESS-PodSpec,VolumeSource}"

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
