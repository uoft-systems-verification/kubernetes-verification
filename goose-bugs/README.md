# Goose bugs

Minimal reproductions of bugs in goose (the Go-to-GooseLang translator in
perennial) and in the Go semantics it targets. Each bug has:

| file | contents |
|---|---|
| `bugs/NN_<name>_repro.go` | the Go code, with a comment explaining Go's behaviour, the model's, and the cause |
| `bugs/NN_<name>_repro_test.go` | a Go test that pins down Go's behaviour |
| `proof/bugNN_<name>.v` | a Rocq proof about the goose translation that contradicts Go |

(Rocq module names cannot start with a digit, hence `bugNN`.) Bug 14 crashes
goose, so it lives in its own package, `crash/`.

## Run

```bash
./run.sh              # all bugs; ~15 s
./run.sh 01 04        # selected bugs
./run.sh clean
```

`run.sh` runs the Go tests, builds goose and proofgen from the perennial
version pinned in `go.mod` (`mit-pdos/perennial@3fe5d0a957a9`, upstream master
2026-09-01), translates `bugs/`, and checks each proof, printing
`REPRODUCED` or `not reproduced` per bug. It needs Go, and `rocq` with the
Perennial library installed (e.g. the `kubernetes-verification` opam switch).

To check a fix, point it at a perennial checkout: a fixed bug is then
`not reproduced`.

```bash
PERENNIAL=~/Code/perennial ./run.sh
```

To step through a proof in VS Code, run `./run.sh` once and open this
directory as the workspace (it has its own `_RocqProject`).

## Bugs

Ordered by how easily they go unnoticed. The first ones silently change the
meaning of common Go code: a proof about the model succeeds, but it is about a
different program. The later ones are arithmetic corner cases, or make the
model get stuck or goose crash, which a verification effort notices.

| n | bug | running the Go program | translated code (proved) | where |
|---|---|---|---|---|
| 01 | `loop_var`: loop variables shared across iterations (Go 1.22+ has one per iteration) | 0 | 1 | goose `forStmt`, `rangeStmt` |
| 02 | `shadowed_define`: `x := x + 1` reads the new, zero-valued `x` | x+1 | 1 | goose `defineStmt` |
| 03 | `block_scope`: variables declared in `{ }` stay in scope after it | x | 42 | goose block printing |
| 04 | `defer_named_result`: deferred calls cannot change named results | 10 | 5 | goose `return`, `wrap_defer` |
| 05 | `empty_block`: everything after an empty `{ }` is dropped | 16 | `#()` | goose `stmtList` |
| 06 | `method_value`: `g := s.Get` does not copy a value receiver | 1 | 2 | goose method wrappers |
| 07 | `tuple_assign`: `p, *p = …` evaluates `*p` after assigning `p` | 70 | 7 | goose `assignStmt` |
| 08 | `op_assign_twice`: `*g() += 1` evaluates `g()` twice | 11 | 21 | goose `assignOpStmt`, `incDecStmt` |
| 09 | `eval_order`: `x + f()` evaluated in a different order than gc | 10 | 1 | goose model vs gc (both allowed by the spec) |
| 10 | `nil_map`: `len` / `delete` of a nil map get stuck | 0 | stuck | Rocq `map.v` |
| 11 | `shift_count`: shift count truncated to the value's type | 0 | 1 | goose `binExpr` |
| 12 | `u32_div`: `uint32` `/` and `%` are signed | 0x40000000 | 0xC0000000 | Rocq `predeclared.v` |
| 13 | `complement`: integer `^x` translated as boolean negation | 2^64-1 | stuck | goose `unaryExpr` |
| 14 | `incdec16`: `x++` on `int16`/`uint16` crashes goose | 42 | crash | goose `incDecStmt` |

## Evidence

The "running the Go program" column is what the function returns when the Go
code runs (checked by `go test`); the "translated code" column is what the
goose translation returns, which the proof establishes. For 01-09, 11 and 12
the proof shows the translation returns that value. The preconditions are satisfiable (only `is_pkg_init`), so the
specs are not vacuous; they are partial correctness (the model returns that
value or does not return), which differs from Go either way. Replacing each
spec's result by Go's makes the same proof fail (checked 2026-09-27).

Getting stuck is the absence of an applicable rule, which cannot be proved
from the `go.Semantics` assumptions. For those bugs the proof pins down what
can be checked: 10 proves that the nil map is `null` and that `len` on maps
reads its argument; 13 proves the translation applies boolean negation to a
`uint64`. For 14, `run.sh` checks that goose crashes.

Bug 02 was found while proving a Kubernetes controller
(`../goose-for-init-shadowing.md`) and bug 03 while reviewing its fix
(`../goose-block-scope.md`); the others by
differential testing: `go run ./goose/cmd/goose-difftest` runs random
Go programs against a GooseLang interpreter (`goose/interp`), and
`-pkg goose/difftest/testdata/scoping` runs hand-written cases. Bug 09 is not a
translation error: the Go specification allows both orders, but proofs about
the model can then describe a different execution than the compiled program.
