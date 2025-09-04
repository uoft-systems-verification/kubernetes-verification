#!/bin/bash

set -e

usage() {
  echo "Usage: $0 <CONTROLLER>"
  echo
  echo "Runs goose on code in kubernetes/pkg/controller/CONTROLLER and outputs to src/code."
}

# Variable to hold the controller name
CONTROLLER=""

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
    if [[ -z "$CONTROLLER" ]]; then
      CONTROLLER="$1"
    else
      echo "Error: Too many arguments provided."
      usage
      exit 1
    fi
    ;;
  esac
  shift
done

# Check if CONTROLLER is provided
if [[ -z "$CONTROLLER" ]]; then
  echo "Error: No CONTROLLER provided."
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
controller_path="kubernetes/pkg/controller/$CONTROLLER"

# Run goose on the specified path
# Ignore errors as goose cannot handle some code snippet
"${GOOSE[@]}" -ignore-errors -out "$GOOSE_OUTPUT" -dir "$controller_path" ./...
"${PROOFGEN[@]}" -out "$PROOFGEN_OUTPUT" -configdir "$GOOSE_CONFIG_DIR" -dir "$controller_path" ./...
