#!/usr/bin/env bash
# Reproduce the goose bugs in bugs/ and crash/.
#
#   ./run.sh             all bugs
#   ./run.sh 01 04       selected bugs
#   ./run.sh clean       remove everything generated
#
# goose/proofgen come from the perennial version pinned in go.mod (upstream,
# with all the bugs). Set PERENNIAL=<perennial checkout> to use a checkout
# instead, e.g. to check a fix: a fixed bug is then reported "not reproduced".
# Needs go and rocq with the Perennial library installed.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"
export GOWORK=off

if [[ "${1:-}" == clean ]]; then
  rm -rf gen proof/*.vo* proof/*.glob proof/.*.aux .lia.cache
  exit 0
fi
want() { [[ $# -eq 0 ]] || [[ " $* " == *" $n "* ]]; }

echo "== Go behaviour"
go test ./... || exit 1

mkdir -p gen/bin
if [[ -n "${PERENNIAL:-}" ]]; then
  echo "== goose from $PERENNIAL ($(git -C "$PERENNIAL" log -1 --format='%h %s'))"
  (cd "$PERENNIAL" && go build -o "$here/gen/bin/" ./goose/cmd/goose ./goose/cmd/proofgen) || exit 1
else
  echo "== goose from $(go list -m -f '{{.Path}}@{{.Version}}' github.com/mit-pdos/perennial)"
  go build -o gen/bin/ github.com/mit-pdos/perennial/goose/cmd/goose \
    github.com/mit-pdos/perennial/goose/cmd/proofgen || exit 1
fi
gen/bin/goose -dir . -out gen/code ./bugs || exit 1
gen/bin/proofgen -dir . -out gen/generatedproof -configdir gen/code ./bugs || exit 1

Q=(-w -notation-incompatible-prefix
   -Q gen/code New.code -Q gen/generatedproof New.generatedproof -Q proof GooseBugs)
rocq compile "${Q[@]}" gen/code/example_com/goosebugs/bugs.v || exit 1
rocq compile "${Q[@]}" gen/generatedproof/example_com/goosebugs/bugs.v || exit 1

echo "== results"
fail=0
report() { # report <ok?> <n> <name>
  if [[ $1 == 0 ]]; then echo "REPRODUCED      $2 $3"; else echo "not reproduced  $2 $3"; fail=1; fi
}
for p in proof/bug*.v; do
  f=$(basename "$p" .v); n=${f:3:2}; name=${f:6}
  want "$@" || continue
  if out=$(rocq compile "${Q[@]}" "$p" 2>&1); then report 0 "$n" "$name"
  else report 1 "$n" "$name"; echo "$out" | head -5 | sed 's/^/    /'; fi
done
n=14
if want "$@"; then
  out=$(gen/bin/goose -dir . -out gen/code ./crash 2>&1); rc=$?
  [[ $rc != 0 && "$out" == *"nil pointer dereference"*"glang.BinaryExpr.Coq"* ]]
  report $? 14 incdec16
fi
exit $fail
