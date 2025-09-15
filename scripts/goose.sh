#!/bin/bash

set -e

usage() {
  echo "Usage: $0 <K8SPATH>"
  echo
  echo "Runs goose on code in K8SPATH and outputs to src/code."
}

# Variable to hold the controller name
K8SPATH=""

while [[ $# -gt 0 ]]; do
  case "$1" in
  -h | -help | --help)
    usage
    exit 0
    ;;
  -*)
    echo "Error: Unknown argument '$1'."
    usage
    exit 1
    ;;
  *)
    if [[ -z "$K8SPATH" ]]; then
      K8SPATH="$1"
    else
      echo "Error: Too many arguments provided."
      usage
      exit 1
    fi
    ;;
  esac
  shift
done

# Check if K8SPATH is provided
if [[ -z "$K8SPATH" ]]; then
  echo "Error: No K8SPATH provided."
  usage
  exit 1
fi

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# run from repository root
cd "$DIR/.."

GOOSE_OUTPUT=src/code
GOOSE_CONFIG_DIR=src/code
PROOFGEN_OUTPUT=src/generatedproof

if which goose 1>/dev/null 2>&1; then
  # NOTE: requires new goose
  GOOSE=("goose")
else
  GOOSE=("go" "run" "github.com/goose-lang/goose/cmd/goose@new")
fi
if which proofgen 1>/dev/null 2>&1; then
  PROOFGEN=("proofgen")
else
  PROOFGEN=("go" "run" "github.com/goose-lang/goose/cmd/proofgen@new")
fi

# Construct the go_path variable
code_path="$K8SPATH"

# Run goose on the specified path
# Ignore errors as goose cannot handle some code snippet
"${GOOSE[@]}" -ignore-errors -out "$GOOSE_OUTPUT" -dir "$code_path" ./...
"${PROOFGEN[@]}" -out "$PROOFGEN_OUTPUT" -configdir "$GOOSE_CONFIG_DIR" -dir "$code_path" ./...
