#!/usr/bin/env python3
"""Post-process Goose proofgen output to avoid slow generated struct proofs.

Goose proofgen emits one `AccessStrict` instance per generated struct field:

    Proof. solve_pointsto_access_struct. Qed.

That generic tactic destructs the entire struct ownership with named-prop
automation and then asks `iFrame` to rebuild it. Large generated structs make
that path expensive. For structs selected with `--optimize-access`, this script
rewrites those proof bodies to field-specific proofs that peel only up to the
accessed field and then rebuild directly.

For selected structs it can also replace `solve_into_val_typed_struct` with a
descriptor-based application of `generated_struct_into_val_typed`. The generic
allocation/load/store proof is checked once in `New.proof.generated_struct`;
the generated instance only describes the fields and proves record
reconstruction.
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
ACCESS_RE = re.compile(
    r"^\s*#\[global\] Instance ([A-Za-z0-9_']+)_access_(?:load|store)_"
)
FIELD_IN_ACCESS_RE = re.compile(r'l\.\[[^\n]*"([^"]+)"\]')
SLOW_ACCESS_PROOF = "Proof. solve_pointsto_access_struct. Qed."
INTO_VAL_RE = re.compile(
    r"^\s*#\[global\] Instance ([A-Za-z0-9_']+)_into_val_typed\b"
)
INTO_VAL_TYPES_RE = re.compile(
    r"IntoValTypedUnderlying\s+\((?P<record>[A-Za-z0-9_'.]+)\.t\)"
    r"\s+\((?P<impl>[^()\s]+)\)\."
)
SLOW_INTO_VAL_PROOF = "Proof. solve_into_val_typed_struct. Qed."
GENERATED_STRUCT_IMPORT = "From New.proof Require Import generated_struct."
CODE_FDS_RE = re.compile(
    r"^Definition\s+([A-Za-z0-9_']+)'fds_unsealed\b.*:=\s*\[\s*$"
)
CODE_FIELD_RE = re.compile(
    r'^\s*\(go\.(FieldDecl|EmbeddedField)\s+"([^"]+)"%go\s+(.+)\)\s*;?\s*$'
)
CODE_TYPE_RE = re.compile(
    r"^Definition\s+([A-Za-z0-9_']+)\b.*:\s*go\.type\s*:=\s*go\.Named\b"
)
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


class OptimizationError(RuntimeError):
    pass


@dataclass(frozen=True)
class CodeField:
    name: str
    go_type: str
    embedded: bool


@dataclass(frozen=True)
class RewriteStats:
    files_changed: int = 0
    access_proofs_rewritten: int = 0
    into_val_proofs_rewritten: int = 0

    def __add__(self, other: "RewriteStats") -> "RewriteStats":
        return RewriteStats(
            files_changed=self.files_changed + other.files_changed,
            access_proofs_rewritten=(
                self.access_proofs_rewritten + other.access_proofs_rewritten
            ),
            into_val_proofs_rewritten=(
                self.into_val_proofs_rewritten + other.into_val_proofs_rewritten
            ),
        )


def iter_v_files(paths: list[pathlib.Path]) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for path in paths:
        if path.is_dir():
            files.extend(sorted(path.rglob("*.v")))
        elif path.suffix == ".v":
            files.append(path)
    return files


def pop_module(module_stack: list[str], line: str) -> None:
    end_match = END_RE.match(line)
    if end_match and module_stack and end_match.group(1) == module_stack[-1]:
        module_stack.pop()


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

        pop_module(module_stack, line)

    return fields_by_module


def generated_code_path(proof_path: pathlib.Path) -> pathlib.Path:
    parts = list(proof_path.parts)
    try:
        generated_index = parts.index("generatedproof")
    except ValueError as error:
        raise OptimizationError(
            f"{proof_path}: path does not contain a generatedproof component"
        ) from error
    parts[generated_index] = "code"
    return pathlib.Path(*parts)


def collect_code_metadata(
    code_path: pathlib.Path,
) -> tuple[dict[str, list[CodeField]], set[str]]:
    if not code_path.exists():
        raise OptimizationError(f"{code_path}: matching generated code file not found")

    structs: dict[str, list[CodeField]] = {}
    local_types: set[str] = set()
    current_struct: str | None = None
    current_fields: list[CodeField] = []

    for line_number, line in enumerate(code_path.read_text().splitlines(), start=1):
        type_match = CODE_TYPE_RE.match(line)
        if type_match:
            local_types.add(type_match.group(1))

        if current_struct is None:
            fds_match = CODE_FDS_RE.match(line)
            if fds_match:
                current_struct = fds_match.group(1)
                current_fields = []
            continue

        if line.strip() == "].":
            structs[current_struct] = current_fields
            current_struct = None
            current_fields = []
            continue

        field_match = CODE_FIELD_RE.match(line)
        if not field_match:
            raise OptimizationError(
                f"{code_path}:{line_number}: cannot parse {current_struct} field: "
                f"{line.strip()}"
            )
        current_fields.append(
            CodeField(
                name=field_match.group(2),
                go_type=field_match.group(3),
                embedded=field_match.group(1) == "EmbeddedField",
            )
        )

    if current_struct is not None:
        raise OptimizationError(f"{code_path}: unterminated {current_struct}'fds_unsealed")
    return structs, local_types


def qualify_local_types(go_type: str, namespace: str, local_types: set[str]) -> str:
    def qualify(match: re.Match[str]) -> str:
        identifier = match.group(0)
        start, end = match.span()
        already_qualified = (
            (start > 0 and go_type[start - 1] == ".")
            or (end < len(go_type) and go_type[end] == ".")
        )
        if identifier in local_types and not already_qualified:
            return f"{namespace}.{identifier}"
        return identifier

    return IDENT_RE.sub(qualify, go_type)


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


def into_val_proof(
    record_ref: str,
    impl_ref: str,
    fields: list[CodeField],
    local_types: set[str],
) -> list[str]:
    namespace = record_ref.rsplit(".", 1)[0]
    descriptor_lines: list[str] = []
    for index, field in enumerate(fields):
        separator = ";" if index + 1 < len(fields) else ""
        go_type = qualify_local_types(field.go_type, namespace, local_types)
        accessor = f"{record_ref}.{field.name}'"
        descriptor_lines.extend(
            [
                "    build_generated_struct_field",
                f'      "{field.name}" {go_type}',
                f"      (fun v => v.({accessor}))",
                f"      (fun v x => v <|({accessor}) := x|>)",
                f"      (ltac:(tc_solve)) (ltac:(tc_solve)){separator}",
            ]
        )

    return [
        "Proof.",
        "  pose (fields := ([",
        *descriptor_lines,
        f"  ] : list (generated_struct_field {record_ref}.t {impl_ref}))).",
        "  assert (fields_unfold :",
        f"    {record_ref}'fds =→ generated_fields_decl fields).",
        "  {",
        "    constructor.",
        "    unfold fields.",
        f"    rewrite /{record_ref}'fds seal_eq.",
        "    reflexivity.",
        "  }",
        "  eapply (generated_struct_into_val_typed",
        "    (fields_unfold:=fields_unfold) fields).",
        "  - intros l v dq.",
        "    unfold fields.",
        "    simpl.",
        "    rewrite /named.",
        "    done.",
        "  - intros v.",
        "    unfold fields.",
        "    destruct v.",
        "    reflexivity.",
        "Qed.",
    ]


def selected_requests(
    requested: set[str], instance_name: str, record_ref: str
) -> set[str]:
    return {name for name in requested if name in (instance_name, record_ref)}


def insert_generated_struct_import(lines: list[str]) -> list[str]:
    if GENERATED_STRUCT_IMPORT in lines:
        return lines
    for index, line in enumerate(lines):
        if "New.proof.proof_prelude." in line:
            return lines[: index + 1] + [GENERATED_STRUCT_IMPORT] + lines[index + 1 :]
    raise OptimizationError("cannot find the proof_prelude import")


def rewrite_file(
    path: pathlib.Path,
    check: bool,
    requested_into_val: set[str],
    requested_access: set[str],
) -> tuple[RewriteStats, set[str], set[str]]:
    original = path.read_text()
    lines = original.splitlines()
    fields_by_module = collect_struct_fields(lines)
    code_structs: dict[str, list[CodeField]] | None = None
    local_types: set[str] | None = None

    module_stack: list[str] = []
    out: list[str] = []
    seen_into_val_requests: set[str] = set()
    seen_access_requests: set[str] = set()
    access_rewritten = 0
    into_val_rewritten = 0
    uses_generated_struct = False
    i = 0
    while i < len(lines):
        line = lines[i]
        module_match = MODULE_RE.match(line)
        if module_match:
            module_stack.append(module_match.group(1))

        into_val_match = INTO_VAL_RE.match(line)
        access_match = ACCESS_RE.match(line)
        if into_val_match:
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].strip().endswith(("Qed.", "Admitted.")):
                    break
                i += 1

            block_text = "\n".join(block)
            types_match = INTO_VAL_TYPES_RE.search(block_text)
            if not types_match:
                raise OptimizationError(
                    f"{path}: cannot parse types for {into_val_match.group(1)}_into_val_typed"
                )
            instance_name = into_val_match.group(1)
            record_ref = types_match.group("record")
            impl_ref = types_match.group("impl")
            matches = selected_requests(requested_into_val, instance_name, record_ref)
            seen_into_val_requests.update(matches)

            generated_proof = "generated_struct_into_val_typed" in block_text
            slow_proof = any(
                part.strip() == SLOW_INTO_VAL_PROOF for part in block
            )
            if matches and (slow_proof or generated_proof):
                uses_generated_struct = True
                if code_structs is None or local_types is None:
                    code_structs, local_types = collect_code_metadata(
                        generated_code_path(path)
                    )
                code_fields = code_structs.get(instance_name)
                proof_fields = fields_by_module.get(tuple(module_stack))
                if code_fields is None:
                    raise OptimizationError(
                        f"{path}: no parsed {instance_name}'fds_unsealed definition"
                    )
                if proof_fields is None:
                    raise OptimizationError(
                        f"{path}: no parsed {instance_name}_typed_pointsto fields"
                    )
                code_field_names = [field.name for field in code_fields]
                if proof_fields != code_field_names:
                    raise OptimizationError(
                        f"{path}: {instance_name} field mismatch between generated code "
                        "and TypedPointsto"
                    )
                if any(field.embedded for field in code_fields):
                    raise OptimizationError(
                        f"{path}: {instance_name} contains embedded fields, which the "
                        "checked fast-proof template does not support"
                    )
                proof_start = next(
                    index
                    for index, block_line in enumerate(block)
                    if block_line.strip().startswith("Proof.")
                )
                replacement = into_val_proof(
                    record_ref, impl_ref, code_fields, local_types
                )
                out.extend(block[:proof_start])
                out.extend(replacement)
                if block[proof_start:] != replacement:
                    into_val_rewritten += 1
            else:
                out.extend(block)
        elif access_match:
            instance_name = access_match.group(1)
            record_ref = ".".join(module_stack)
            matches = selected_requests(requested_access, instance_name, record_ref)
            seen_access_requests.update(matches)
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].strip() == SLOW_ACCESS_PROOF:
                    break
                if lines[i].strip().startswith("Proof."):
                    break
                i += 1

            if matches and block[-1].strip() == SLOW_ACCESS_PROOF:
                access_text = "\n".join(block)
                field_match = FIELD_IN_ACCESS_RE.search(access_text)
                fields = fields_by_module.get(tuple(module_stack), [])
                if not field_match:
                    raise OptimizationError(
                        f"{path}: cannot parse field for {instance_name} access proof"
                    )
                if field_match.group(1) not in fields:
                    raise OptimizationError(
                        f"{path}: field {field_match.group(1)} is absent from "
                        f"{instance_name}_typed_pointsto"
                    )
                field_index = fields.index(field_match.group(1))
                out.extend(block[:-1])
                out.extend(direct_access_proof(field_index))
                access_rewritten += 1
            else:
                out.extend(block)
        else:
            out.append(line)

        pop_module(module_stack, line)
        i += 1

    if uses_generated_struct:
        out = insert_generated_struct_import(out)

    updated = "\n".join(out) + ("\n" if original.endswith("\n") else "")
    if updated == original:
        return RewriteStats(), seen_into_val_requests, seen_access_requests

    if check:
        print(
            f"{path}: would rewrite {access_rewritten} access proof(s), "
            f"{into_val_rewritten} into-val proof(s)"
        )
    else:
        path.write_text(updated)
        print(
            f"{path}: rewrote {access_rewritten} access proof(s), "
            f"{into_val_rewritten} into-val proof(s)"
        )
    return (
        RewriteStats(
            files_changed=1,
            access_proofs_rewritten=access_rewritten,
            into_val_proofs_rewritten=into_val_rewritten,
        ),
        seen_into_val_requests,
        seen_access_requests,
    )


def parse_type_list(values: list[str]) -> set[str]:
    return {
        type_name.strip()
        for value in values
        for type_name in value.split(",")
        if type_name.strip()
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="report files that would change without writing them",
    )
    parser.add_argument(
        "--optimize-into-val-typed",
        action="append",
        default=[],
        metavar="TYPE[,TYPE...]",
        help="replace the slow checked IntoValTyped proof for selected structs",
    )
    parser.add_argument(
        "--optimize-access",
        action="append",
        default=[],
        metavar="TYPE[,TYPE...]",
        help="replace slow AccessStrict proofs for selected structs",
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=pathlib.Path,
        default=[pathlib.Path("src/generatedproof")],
        help="generated proof files or directories to optimize",
    )
    args = parser.parse_args(argv)
    requested_into_val = parse_type_list(args.optimize_into_val_typed)
    requested_access = parse_type_list(args.optimize_access)

    total = RewriteStats()
    seen_into_val_requests: set[str] = set()
    seen_access_requests: set[str] = set()
    try:
        for path in iter_v_files(args.paths):
            stats, seen_into_val, seen_access = rewrite_file(
                path, args.check, requested_into_val, requested_access
            )
            total += stats
            seen_into_val_requests.update(seen_into_val)
            seen_access_requests.update(seen_access)
    except OptimizationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    missing_into_val = requested_into_val - seen_into_val_requests
    if missing_into_val:
        print(
            "error: requested IntoValTyped struct(s) not found: "
            + ", ".join(sorted(missing_into_val)),
            file=sys.stderr,
        )
        return 2

    missing_access = requested_access - seen_access_requests
    if missing_access:
        print(
            "error: requested AccessStrict struct(s) not found: "
            + ", ".join(sorted(missing_access)),
            file=sys.stderr,
        )
        return 2

    print(
        "optimized generated proofs: "
        f"{total.access_proofs_rewritten} access proof(s), "
        f"{total.into_val_proofs_rewritten} into-val proof(s) "
        f"in {total.files_changed} file(s)"
    )
    if args.check and total.files_changed:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
