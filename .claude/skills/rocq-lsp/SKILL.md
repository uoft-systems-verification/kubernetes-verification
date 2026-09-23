---
name: rocq-lsp
description: Use rocq-lsp to inspect proof goals, locate failing tactics, and test tactic replacements in a Rocq file without recompiling it from the top. Use when debugging or repairing a proof in src/proof/, or when you need the goal state before or after a line.
---

# rocq-lsp

`rocq-lsp` keeps a warm VsRocq prover between commands, so repeated checks of one file reuse the unchanged
checked prefix. Use it to repair proofs in `src/proof/`. It does not replace `make`: it never builds or updates
dependencies, and it never edits your files.

## Setup

Run every command from the repository root, in the project's opam switch (`vsrocqtop` and `rocq` come from it):

```bash
eval $(opam env --switch=kubernetes-verification --set-switch)
source rocq-lsp-mcp/.venv/bin/activate
```

The prover loads the `.vos` of every dependency as-is. Before starting, build them with `make -j10 vos`; a missing
`.vos` makes a `Require` fail and a stale one is loaded unchanged.

## Commands

Positions are 1-indexed: `FILE:LINE` or `FILE:LINE:COLUMN`.

| Command | Use |
|---|---|
| `rocq-lsp start [PROJECT]` | Start the session. Every other command needs one. |
| `rocq-lsp goal FILE:LINE` | Proof state before and after that line, plus errors above it. |
| `rocq-lsp goal FILE:LAST_LINE` | The same on the last line, which checks the whole file. |
| `rocq-lsp goal FILE:LINE:COLUMN` | State at one point inside a line holding several tactics. |
| `rocq-lsp outline FILE` | Imports and declarations, with the line numbers the other commands want. |
| `rocq-lsp try FILE:LINE "  tac."` | Test replacement tactics without touching the file. |
| `rocq-lsp run-code` | Check a self-contained snippet read from stdin. |
| `rocq-lsp build FILE.vo` | Run make on a target, then reload the prover. |
| `rocq-lsp status` | Open files and how much memory they hold. |
| `rocq-lsp close FILE` | Free one file's prover state, keeping the session. |
| `rocq-lsp stop` | End the session and free every prover. |

`rocq-lsp --help` and `rocq-lsp COMMAND --help` list more options.

## Repair workflow

1. `rocq-lsp start`, then `rocq-lsp goal FILE:LINE` on the `Qed.` (or last line) of the proof. Read
   `--- errors ---` first: it gives the failing tactic's line and columns even when the position itself shows
   "No goals".
2. `rocq-lsp goal FILE:N` on the failing line to see the goal before and after it.
3. Optionally `rocq-lsp try FILE:N "  tac1." "  tac2."` to test replacements independently. `try` checks only the
   replacement tactic, not the rest of the proof.
4. Edit the file, then `rocq-lsp goal FILE:LAST_LINE` again. The repair is done when there are no goals and no
   `--- errors ---` section. Saved edits are picked up automatically; only the changed suffix is rechecked.
5. `rocq-lsp run-code` checks a throwaway snippet in the current project's load path, for example
   `echo 'Lemma t : 1 = 1. Proof. reflexivity. Qed.' | rocq-lsp run-code`. It needs a known project: run a file
   command first or pass `--project`.

## Notes

- Each open file holds prover state, often 1-4 GB for a large proof. Watch it with `status`, and `close` files
  you are done with.
- Checking has no time limit by default. To interrupt a long check, run `rocq-lsp stop` from another shell. To set
  a limit, restart with `ROCQ_LSP_TIMEOUT=900 rocq-lsp restart .`.
- The solver timeout rules in CLAUDE.md apply to tactics you try: wrap `set_solver`, `naive_solver`, and
  `vm_compute` in `Timeout 10`.
- Always end the session with `rocq-lsp stop` before finishing the task, so no prover is left running. An idle
  session also exits on its own after an hour.
