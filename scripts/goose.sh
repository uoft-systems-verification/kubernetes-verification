#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."

go tool perennial-cli goose --config goose-kubernetes.toml
go tool perennial-cli goose --config goose-kubernetes-model.toml
go tool perennial-cli goose --config goose-controllers.toml
go tool perennial-cli goose --config goose-iam.toml
go tool perennial-cli goose --config goose-benchmark.toml

GOOSE_PROOF_OPTIMIZER_TARGETS="${GOOSE_PROOF_OPTIMIZER_TARGETS:-src/generatedproof/k8s_io/api/core/v1.v}"
python3 scripts/optimize_generated_proofs.py $GOOSE_PROOF_OPTIMIZER_TARGETS
