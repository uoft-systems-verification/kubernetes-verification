#!/bin/bash

set -e

usage() {
  echo "Usage: $0 [-dir GO_DIR] <PKG_PATTERN>"
  echo
  echo "-dir GO_DIR     Optional; passed to goose/proofgen as -dir GO_DIR (module root)."
  echo "PKG_PATTERN     Package pattern to process (e.g., './...' or './k8s.io/kubernetes/pkg/controller/replicaset')."
}

# Parse args
GO_DIR=""
CODE_PATH=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help|-help)
      usage
      exit 0
      ;;
    -dir)
      if [[ $# -lt 2 ]]; then
        echo "Error: -dir requires an argument"
        usage
        exit 1
      fi
      GO_DIR="$2"
      shift 2
      ;;
    -*)
      echo "Error: unknown option '$1'"
      usage
      exit 1
      ;;
    *)
      if [[ -z "$CODE_PATH" ]]; then
        CODE_PATH="$1"
      else
        echo "Error: too many positional arguments"
        usage
        exit 1
      fi
      shift
      ;;
  esac
done

if [[ -z "$CODE_PATH" ]]; then
  echo "Error: missing package pattern argument"
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

# Run goose on the specified path
# Ignore errors as goose cannot handle some code snippet
DIR_ARGS=()
if [[ -n "$GO_DIR" ]]; then
  DIR_ARGS=("-dir" "$GO_DIR")
fi

"${GOOSE[@]}" -ignore-errors -out "$GOOSE_OUTPUT" "${DIR_ARGS[@]}" "$CODE_PATH"
"${PROOFGEN[@]}" -out "$PROOFGEN_OUTPUT" -configdir "$GOOSE_CONFIG_DIR" "${DIR_ARGS[@]}" "$CODE_PATH"
