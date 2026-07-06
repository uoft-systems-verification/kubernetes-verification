#!/usr/bin/env python3
"""Post-process Goose proofgen output to avoid slow struct access proofs.

Goose proofgen emits one `AccessStrict` instance per generated struct field:

    Proof. solve_pointsto_access_struct. Qed.

That generic tactic destructs the entire struct ownership with named-prop
automation and then asks `iFrame` to rebuild it. Large generated structs make
that path expensive. This script rewrites those proof bodies to field-specific
proofs that peel only up to the accessed field and then rebuild directly.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from dataclasses import dataclass


MODULE_RE = re.compile(r"^Module\s+([A-Za-z0-9_']+)\.$")
END_RE = re.compile(r"^End\s+([A-Za-z0-9_']+)\.$")
TYPED_POINTSTO_RE = re.compile(r"^\s*#\[global\]Program Instance .*_typed_pointsto\b")
FIELD_RE = re.compile(r'^\s*"([^"]+)"\s')
ACCESS_RE = re.compile(r"^\s*#\[global\] Instance .*_access_(?:load|store)_")
FIELD_IN_ACCESS_RE = re.compile(r'l\.\[[^\n]*"([^"]+)"\]')
SLOW_ACCESS_PROOF = "Proof. solve_pointsto_access_struct. Qed."


@dataclass(frozen=True)
class RewriteStats:
    files_changed: int = 0
    proofs_rewritten: int = 0

    def __add__(self, other: "RewriteStats") -> "RewriteStats":
        return RewriteStats(
            files_changed=self.files_changed + other.files_changed,
            proofs_rewritten=self.proofs_rewritten + other.proofs_rewritten,
        )


def iter_v_files(paths: list[pathlib.Path]) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for path in paths:
        if path.is_dir():
            files.extend(sorted(path.rglob("*.v")))
        elif path.suffix == ".v":
            files.append(path)
    return files


def collect_struct_fields(lines: list[str]) -> dict[tuple[str, ...], list[str]]:
    module_stack: list[str] = []
    fields_by_module: dict[tuple[str, ...], list[str]] = {}
    collecting_for: tuple[str, ...] | None = None
    fields: list[str] = []

    for line in lines:
        module_match = MODULE_RE.match(line)
        if module_match:
            module_stack.append(module_match.group(1))

        if collecting_for is not None:
            field_match = FIELD_RE.match(line)
            if field_match and field_match.group(1) != "_":
                fields.append(field_match.group(1))
            if line.strip() == "|}.":
                fields_by_module[collecting_for] = fields
                collecting_for = None
                fields = []
        elif TYPED_POINTSTO_RE.match(line):
            collecting_for = tuple(module_stack)
            fields = []

        end_match = END_RE.match(line)
        if end_match and module_stack:
            module_stack.pop()

    return fields_by_module


def direct_access_proof(field_index: int) -> list[str]:
    prefix_hyps = [f"H{i}" for i in range(field_index)]
    frame_hyps = prefix_hyps + ["Hfield", "Hrest"]

    proof = [
        "Proof.",
        "  constructor.",
        '  iIntros "H".',
        '  iDestruct (typed_pointsto_not_null with "H") as %Hnotnull.',
        '  iDestruct (typed_pointsto_split with "H") as "H".',
        "  rewrite /= /named.",
    ]
    proof.extend(f'  iDestruct "H" as "[H{i} H]".' for i in range(field_index))
    proof.extend(
        [
            '  iDestruct "H" as "[Hfield Hrest]".',
            '  iSplitL "Hfield"; first iExact "Hfield".',
            '  iIntros "Hfield".',
            "  iApply typed_pointsto_combine; first done.",
            "  simpl. rewrite /named.",
            f'  iFrame "{" ".join(frame_hyps)}".',
            "Qed.",
        ]
    )
    return proof


def rewrite_file(path: pathlib.Path, check: bool) -> RewriteStats:
    original = path.read_text()
    lines = original.splitlines()
    fields_by_module = collect_struct_fields(lines)

    module_stack: list[str] = []
    out: list[str] = []
    rewritten = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        module_match = MODULE_RE.match(line)
        if module_match:
            module_stack.append(module_match.group(1))

        if ACCESS_RE.match(line):
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].strip() == SLOW_ACCESS_PROOF:
                    break
                if lines[i].strip().startswith("Proof."):
                    break
                i += 1

            if block[-1].strip() == SLOW_ACCESS_PROOF:
                access_text = "\n".join(block)
                field_match = FIELD_IN_ACCESS_RE.search(access_text)
                fields = fields_by_module.get(tuple(module_stack), [])
                if field_match and field_match.group(1) in fields:
                    field_index = fields.index(field_match.group(1))
                    out.extend(block[:-1])
                    out.extend(direct_access_proof(field_index))
                    rewritten += 1
                else:
                    out.extend(block)
            else:
                out.extend(block)
        else:
            out.append(line)

        end_match = END_RE.match(line)
        if end_match and module_stack:
            module_stack.pop()
        i += 1

    updated = "\n".join(out) + ("\n" if original.endswith("\n") else "")
    if updated == original:
        return RewriteStats()

    if check:
        print(f"{path}: would rewrite {rewritten} access proof(s)")
    else:
        path.write_text(updated)
        print(f"{path}: rewrote {rewritten} access proof(s)")
    return RewriteStats(files_changed=1, proofs_rewritten=rewritten)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="report files that would change without writing them",
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=pathlib.Path,
        default=[pathlib.Path("src/generatedproof")],
        help="generated proof files or directories to optimize",
    )
    args = parser.parse_args(argv)

    total = RewriteStats()
    for path in iter_v_files(args.paths):
        total += rewrite_file(path, args.check)

    print(
        f"optimized generated proofs: {total.proofs_rewritten} proof(s) "
        f"in {total.files_changed} file(s)"
    )
    if args.check and total.files_changed:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
