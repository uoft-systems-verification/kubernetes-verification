#!/bin/bash

set -euo pipefail

usage() {
  echo "Usage: $0 <n>"
  echo
  echo "n    Number of times to run TestPBT."
}

if [[ $# -ne 1 ]]; then
  usage
  exit 1
fi

N="$1"

if ! [[ "$N" =~ ^[1-9][0-9]*$ ]]; then
  echo "Error: n must be a positive integer, got '$N'"
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"
MODEL_DIR="$REPO_ROOT/kubernetes_model"

if [[ ! -d "$MODEL_DIR" ]]; then
  echo "Error: expected directory not found: $MODEL_DIR"
  exit 1
fi

cd "$MODEL_DIR"

for ((i = 1; i <= N; i++)); do
  echo "=== Run $i/$N ==="
  KUBEBUILDER_ASSETS="$(setup-envtest use 1.34.0 -p path)" \
    go test -v ./apimodel -run TestPBT -rapid.checks=1 -timeout=10m
done
