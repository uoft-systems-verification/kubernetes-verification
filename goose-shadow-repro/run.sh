#!/usr/bin/env bash
# Reproduce the goose shadowing bug.
#   ./run.sh         Go test, translate with goose, check proof/Repro.v
#   ./run.sh clean   remove everything generated
# By default goose/proofgen are the versions pinned as tools in the enclosing
# module (../go.mod). Set PERENNIAL=<perennial checkout> to use that instead.
# Needs go and rocq with Perennial installed (e.g. the kubernetes-verification
# opam switch).
set -euo pipefail
repro="$(cd "$(dirname "$0")" && pwd)"
cd "$repro"

if [[ "${1:-}" == clean ]]; then
  rm -rf gen proof/*.vo* proof/*.glob proof/.*.aux .lia.cache
  exit 0
fi

export GOWORK=off   # keep perennial's go.work from claiming this module

echo "== Go behaviour"
go test .

if [[ -n "${PERENNIAL:-}" ]]; then
  echo "== goose (perennial checkout $(git -C "$PERENNIAL" log -1 --format='%h %s'))"
  (cd "$PERENNIAL" && go build -o "$repro/gen/bin/" ./goose/cmd/goose ./goose/cmd/proofgen)
else
  echo "== goose ($(cd .. && go list -m -f '{{with .Replace}}{{.Path}} {{.Version}}{{else}}{{.Path}} {{.Version}}{{end}}' github.com/mit-pdos/perennial))"
  (cd .. && go build -o "$repro/gen/bin/" \
    github.com/mit-pdos/perennial/goose/cmd/goose \
    github.com/mit-pdos/perennial/goose/cmd/proofgen)
fi
gen/bin/goose -dir . -out gen/code .
gen/bin/proofgen -dir . -out gen/generatedproof -configdir gen/code .
sed -n '/^Definition Defineⁱᵐᵖˡ/,/^$/p' gen/code/example_com/shadowrepro.v

echo "== Rocq"
Q=(-w -notation-incompatible-prefix
   -Q gen/code New.code -Q gen/generatedproof New.generatedproof -Q proof Repro)
rocq compile "${Q[@]}" gen/code/example_com/shadowrepro.v
rocq compile "${Q[@]}" gen/generatedproof/example_com/shadowrepro.v
rocq compile "${Q[@]}" proof/Repro.v
echo "BUG REPRODUCED: proof/Repro.v proves the translation diverges from Go"
