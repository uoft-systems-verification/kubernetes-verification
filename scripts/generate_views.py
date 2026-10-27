#!/usr/bin/env python3
"""Generate pure object views from the checked-out Kubernetes types.

Goose remains responsible for src/code and src/generatedproof. This generator
only writes translation configuration and pure ownership models in src/generatedviews.
scripts/goose.sh updates the configurations and regenerates these views. Use
--check to compare the checked-in views with the current Kubernetes Go types.

Pointers become options; slices and maps become optional lists/maps, preserving
nil versus allocated empty values. Heap-free Go records can themselves be pure
views. Configured exclusions omit fields from both the view and its ownership
predicate. This includes timestamps' shared runtime-managed timezone pointer.
Internal big.Int word buffers are lists: copying may change empty-buffer nilness
without changing their words. Their entire backing storage is still owned.
The generated models describe representation, not API validation or defaulting.
"""

import argparse
import functools
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
CORE = "k8s.io/api/core/v1"
APPS = "k8s.io/api/apps/v1"
META = "k8s.io/apimachinery/pkg/apis/meta/v1"
BIG_NAT = "math/big/nat"
PACKAGES = {
    # Go package: (local Rocq alias, generated file path, Goose module name).
    CORE: ("api_core_v1", "k8s_io/api/core/v1", "v1"),
    APPS: ("api_apps_v1", "k8s_io/api/apps/v1", "v1"),
    META: ("meta_v1", "k8s_io/apimachinery/pkg/apis/meta/v1", "v1"),
    "k8s.io/apimachinery/pkg/api/resource": ("resource", "k8s_io/apimachinery/pkg/api/resource", "resource"),
    "k8s.io/apimachinery/pkg/util/intstr": ("intstr", "k8s_io/apimachinery/pkg/util/intstr", "intstr"),
    "gopkg.in/inf.v0": ("inf", "gopkg_in/inf_v0", "inf"),
    "math/big": ("big", "math/big", "big"),
    "time": ("runtime_time", "time", "time"),
    "k8s.io/apimachinery/pkg/runtime": ("runtime", "k8s_io/apimachinery/pkg/runtime", "runtime"),
}
SCALARS = {
    "interface": "interface.t", "string": "go_string", "bool": "bool", "int": "w64", "uint": "w64",
    "int64": "w64", "uint64": "w64", "int32": "w32", "uint32": "w32",
    "int16": "w16", "uint16": "w16", "int8": "w8", "uint8": "w8",
}


def extract_schema(groups):
    """Reflect configured named roots using a temporary Go entry point."""
    imports = {}
    roots = []
    for name, group in groups.items():
        types = []
        for root in group["roots"]:
            package, _, typ = root.rpartition("/")
            alias = imports.setdefault(package, "pkg" + str(len(imports)))
            types.append(f"reflect.TypeFor[{alias}.{typ}]()")
        roots.append("{name: " + json.dumps(name) + ", types: []reflect.Type{" + ", ".join(types) + "}}")
    driver = '\n'.join([
        'package main', 'import (', '"reflect"',
        *(f'{alias} {json.dumps(package)}' for package, alias in imports.items()),
        ')', 'func main() {', 'extractSchema([]rootGroup{',
        *(root + ',' for root in roots), '})', '}',
    ])
    env = dict(os.environ)
    env.setdefault("GOCACHE", "/tmp/go-build")
    # Match scripts/goose.sh even when the installed Go version differs.
    env["GOTOOLCHAIN"] = "go" + next(
        line.split()[1] for line in (ROOT / "go.mod").read_text().splitlines()
        if line.startswith("go ")
    )
    with tempfile.TemporaryDirectory(prefix="generate-views-") as directory:
        helper = Path(directory) / "extract_schema.go"
        helper.write_text((ROOT / "scripts/extract_schema.go").read_text())
        main = Path(directory) / "main.go"
        main.write_text(driver)
        return json.loads(subprocess.check_output(
            ["go", "run", str(helper), str(main)], cwd=ROOT / "kubernetes", env=env, text=True,
        ))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", action="store_true", help="update Goose type translation configuration")
    parser.add_argument("--check", action="store_true", help="check views without writing files")
    parser.add_argument("--schema", type=Path, help="reuse a reflection schema for development")
    parser.add_argument("--view-config", type=Path, default=ROOT / "scripts/generate_views.toml",
                        help="roots, output groups, and ownership configuration (default: scripts/generate_views.toml)")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "src/generatedviews",
                        help="directory for generated views (default: src/generatedviews)")
    args = parser.parse_args()
    if args.config and args.check:
        parser.error("--config and --check cannot be combined")
    config = tomllib.loads(args.view_config.read_text())
    if set(config) - {"groups", "contexts", "named_collections", "exclude_fields"}:
        parser.error("unknown view configuration section")
    groups = config.get("groups", {})
    contexts = config.get("contexts", {})
    if not isinstance(groups, dict) or not groups:
        parser.error("groups must be a nonempty table")
    if not isinstance(contexts, dict):
        parser.error("contexts must be a table")

    def identifier(value):
        return isinstance(value, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", value)

    def qualified(value):
        return isinstance(value, str) and "." in value and all(identifier(part) for part in value.split("."))

    package_modules = {
        alias: "code." + path.replace("/", ".") + "." + module
        for alias, path, module in PACKAGES.values()
    }
    for name, context in contexts.items():
        if not isinstance(context, dict) or set(context) != {"imports", "aliases", "assumptions"}:
            parser.error(f"context {name} needs imports, aliases, and assumptions")
        if not isinstance(context["imports"], list) or not all(qualified(v) for v in context["imports"]):
            parser.error(f"context {name} imports must be qualified Rocq modules")
        if (not isinstance(context["aliases"], list)
                or not all(isinstance(v, str) and v in package_modules for v in context["aliases"])):
            parser.error(f"context {name} aliases must refer to PACKAGES aliases")
        assumptions = context["assumptions"]
        if (not isinstance(assumptions, dict) or not assumptions
                or not all(identifier(k) and isinstance(v, str) and v in context["aliases"]
                           for k, v in assumptions.items())):
            parser.error(f"context {name} assumptions must map binder names to its package aliases")
    modules = set()
    for name, group in groups.items():
        if (not identifier(name) or not isinstance(group, dict)
                or not {"module", "roots", "context"} <= set(group)
                or set(group) - {"module", "roots", "context", "exports"}):
            parser.error(f"group {name} needs module, roots, and context; exports is optional")
        if not identifier(group["module"]) or group["module"] in modules:
            parser.error(f"group {name} needs a unique Rocq module name")
        modules.add(group["module"])
        if not isinstance(group["context"], str) or group["context"] not in contexts:
            parser.error(f"unknown context for group {name}")
        if not isinstance(group["roots"], list) or not group["roots"]:
            parser.error(f"group {name} roots must be a nonempty list of Go type IDs")
        for root in group["roots"]:
            package, _, typ = root.rpartition("/") if isinstance(root, str) else ("", "", "")
            if package not in PACKAGES or not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", typ):
                parser.error(f"invalid root {root!r}: use a PACKAGES Go path followed by /ExportedType")
        exports = group.get("exports", {})
        if not isinstance(exports, dict) or not all(identifier(k) and qualified(v) for k, v in exports.items()):
            parser.error(f"group {name} exports must map alias names to qualified Rocq modules")
    named_collections = config.get("named_collections", [])
    if not isinstance(named_collections, list) or not all(isinstance(v, str) for v in named_collections):
        parser.error("named_collections must be a list of Go type IDs")
    named_collections = set(named_collections)
    if args.schema:
        schema = json.loads(args.schema.read_text())
    else:
        schema = extract_schema(groups)
    nodes = schema["Nodes"]
    if schema["Roots"] != {name: group["roots"] for name, group in groups.items()}:
        parser.error("reflection schema roots do not match configured groups; omit --schema to reflect them again")
    if any(nodes[root]["Kind"] != "struct" for roots in schema["Roots"].values() for root in roots):
        parser.error("view roots must be Go structs")
    exclusions = config.get("exclude_fields", {})
    if not isinstance(exclusions, dict):
        parser.error("exclude_fields must be a table of Go types and fields")
    for key, fields in exclusions.items():
        if key not in nodes or nodes[key]["Kind"] != "struct":
            parser.error(f"excluded type is not a reflected struct: {key}")
        if not isinstance(fields, dict):
            parser.error(f"exclusions for {key} must map field names to explanations")
        names = {f["Name"] for f in nodes[key]["Fields"]}
        for name, reason in fields.items():
            if name not in names:
                parser.error(f"unknown excluded field: {key}.{name}")
            if not isinstance(reason, str) or not reason.strip():
                parser.error(f"excluded field needs an explanation: {key}.{name}")
            if "(*" in reason or "*)" in reason:
                parser.error(f"exclusion explanation contains a Rocq comment delimiter: {key}.{name}")

    # Use the same projection for records, conversions, zero values, and ownership.
    view_fields = {
        key: [f for f in n.get("Fields") or [] if f["Name"] not in exclusions.get(key, {})]
        for key, n in nodes.items() if n["Kind"] == "struct"
    }

    owners = {}
    order = []

    def assign(key, group):
        if key in owners:
            return
        owners[key] = group
        n = nodes[key]
        for field in n.get("Fields") or []:
            assign(field["Type"], group)
        for child in (n.get("Key"), n.get("Elem")):
            if child:
                assign(child, group)
        order.append(key)

    for group in groups:
        for key in schema["Roots"][group]:
            assign(key, group)
    current_group = None

    def module(key):
        n = nodes[key]
        result = {"math/big/Int": "BigIntV", "gopkg.in/inf.v0/Dec": "DecimalV"}.get(
            key, n["Name"][0].upper() + n["Name"][1:] + "V")
        if current_group is not None and owners[key] != current_group:
            result = groups[owners[key]]["module"] + "." + result
        return result

    def physical(key):
        n = nodes[key]
        if n["Kind"] in {"ptr", "map"}:
            return "loc"
        if n["Kind"] == "slice":
            return "slice.t"
        if n["Name"] and n["Pkg"] in PACKAGES:
            return PACKAGES[n["Pkg"]][0] + "." + n["Name"] + ".t"
        if n["Kind"] in SCALARS:
            return SCALARS[n["Kind"]]
        raise ValueError("Unsupported physical type: " + key)

    @functools.cache
    def raw_pure(key):
        n = nodes[key]
        # Aliasing a Go record would retain any omitted fields, including nested ones.
        return n["Kind"] in SCALARS or (n["Kind"] == "struct" and
            not exclusions.get(key) and all(raw_pure(f["Type"]) for f in view_fields[key]))

    @functools.cache
    def owns_heap(key):
        n = nodes[key]
        return n["Kind"] in {"ptr", "slice", "map"} or (n["Kind"] == "struct" and
            any(owns_heap(f["Type"]) for f in view_fields[key]))

    def view(key):
        n = nodes[key]
        if key == BIG_NAT:
            return "list (" + view(n["Elem"]) + ")"
        if n["Kind"] == "struct":
            return module(key) + ".t"
        if n["Kind"] in SCALARS:
            return SCALARS[n["Kind"]]
        if n["Kind"] == "ptr":
            return "option (" + view(n["Elem"]) + ")"
        if n["Kind"] == "slice":
            return "option (list (" + view(n["Elem"]) + "))"
        if n["Kind"] == "map":
            if nodes[n["Key"]]["Kind"] != "string":
                raise ValueError("Non-string API map key: " + key)
            return "option (gmap go_string (" + view(n["Elem"]) + "))"
        raise ValueError("Unsupported view type: " + key)

    def of_go(key, value):
        if nodes[key]["Kind"] == "struct":
            return "(" + module(key) + ".of_go " + value + ")"
        if nodes[key]["Kind"] in SCALARS:
            return value
        raise ValueError("Heap-backed values have no of_go projection: " + key)

    def predicate(key):
        n = nodes[key]
        if n["Kind"] == "struct":
            return module(key) + ".deepown"
        if n["Kind"] == "interface":
            return "(λ c v (_ : dfrac), ⌜ c = interface.nil ∧ v = interface.nil ⌝)%I"
        if n["Kind"] in SCALARS:
            return "(λ c v (_ : dfrac), ⌜ c = v ⌝)%I"
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return "(deepown_" + op + " " + predicate(n["Elem"]) + ")"

    def persist(key):
        n = nodes[key]
        if n["Kind"] == "struct":
            return "apply " + module(key) + ".deepown_persist."
        if n["Kind"] in SCALARS:
            return 'iIntros "H". by iModIntro.'
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return ("apply deepown_" + op
                + "_persist. intros. " + persist(n["Elem"]))

    @functools.cache
    def has_zero(key):
        n = nodes[key]
        return n["Kind"] != "struct" or all(has_zero(f["Type"]) for f in view_fields[key])

    def zero(key):
        n = nodes[key]
        if key == BIG_NAT:
            return "[]"
        if n["Kind"] == "struct":
            return module(key) + ".zero"
        if n["Kind"] in {"ptr", "slice", "map"}:
            return "None"
        return "zero_val _"

    def zero_proof(key):
        n = nodes[key]
        if n["Kind"] == "struct":
            return "iApply " + module(key) + ".deepown_zero."
        if n["Kind"] in SCALARS:
            return "done."
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return "iApply deepown_" + op + "_nil."

    def field_entries(key, field):
        """Named ownership conjuncts, their persistence proof, and zero proof."""
        child_key = field["Type"]
        child = nodes[child_key]
        tag = "Hdeepown_" + ("ignorestorereaderror" if field["Name"] == "IgnoreStoreReadErrorWithClusterBreakingPotential" else field["Name"].lower())
        c = "c.(" + physical(key)[:-2] + "." + field["Name"] + "')"
        v = "v.(" + field["Name"] + "')"
        expression = predicate(child_key) + " " + c + " " + v + " dq"
        if key not in named_collections or child["Kind"] not in {"ptr", "slice", "map"}:
            proof = ""
            # Keep nontrivial struct predicates named even when exclusions make
            # them heap-free, so clients can use their abstraction unchanged.
            resource = not raw_pure(child_key)
            if resource:
                if child["Kind"] in {"ptr", "slice", "map"}:
                    op = "slice_list" if child_key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[child["Kind"]]
                    proof = 'iApply (deepown_' + op + '_persist with "' + tag + '"). intros. ' + persist(child["Elem"])
                else:
                    proof = 'iApply (' + module(child_key) + '.deepown_persist with "' + tag + '").'
            return [(tag, expression, proof, zero_proof(child_key), not resource)]

        if key == META + "/DeleteOptions" and field["Name"] == "DryRun":
            # TODO: Use this concise nilness/contents split for other slice fields.
            return [
                (tag + "_none", "⌜ " + c + " = slice.nil ↔ " + v + " = None ⌝", "", "done.", True),
                (tag, c + " ↦*{dq} default [] " + v, 'iApply (own_slice_persist with "' + tag + '").', "iApply own_slice_nil.", False),
                (tag + "_cap", "own_slice_cap go_string " + c + " dq", 'iPersist "' + tag + '_cap". by iModIntro.', "iApply (deepown_slice_cap_nil (C := go_string) (V := unit)).", False),
            ]
        elem = child["Elem"]
        ctype = physical(elem)
        if child["Kind"] == "slice" and not raw_pure(elem):
            proof = ('iApply (deepown_slice_persist with "' + tag + '"). intros. '
                     + persist(elem))
            return [(tag, expression, proof, zero_proof(child_key), False)]
        none = "slice.nil" if child["Kind"] == "slice" else "null"
        result = [(tag + "_none", "⌜ " + c + " = " + none + " ↔ " + v + " = None ⌝", "", "done.", True)]
        hypothesis = tag + "_some"
        opening = 'destruct ' + v + ' as [value|]; last done. '
        if child["Kind"] == "ptr":
            some = "∃ value_c, " + c + " ↦{dq} value_c ∗ " + predicate(elem) + " value_c value dq"
            # Persist the pointed-to cell and recurse on its represented value.
            proof = (opening + 'iDestruct "' + hypothesis + '" as (value_c) "[Hp Hv]". iPersist "Hp". '
                     + 'iAssert (|==> ' + predicate(elem) + ' value_c value DfracDiscarded)%I with "[Hv]" as ">Hv". '
                     + '{ ' + ('iApply (' + module(elem) + '.deepown_persist with "Hv").' if nodes[elem]["Kind"] == "struct" else 'iModIntro. iExact "Hv".') + ' } '
                     + 'iModIntro. iExists value_c. iFrame "# ∗".')
        elif child["Kind"] == "map":
            if nodes[elem]["Kind"] not in SCALARS:
                raise ValueError("Named map ownership requires scalar entries: " + child_key)
            some = "∃ values_c, " + c + " ↦${dq} values_c ∗ ⌜ values_c = value ⌝"
            proof = (opening + 'iDestruct "' + hypothesis + '" as (values_c) "[Hm %Heq]". '
                     + 'iMod (own_map_persist with "Hm") as "Hm". iModIntro. iExists values_c. iFrame "# ∗ %".')
        elif nodes[elem]["Kind"] in SCALARS:
            some = c + " ↦*{dq} value"
            proof = opening + 'iApply (own_slice_persist with "' + hypothesis + '").'
        elif raw_pure(elem):
            some = "∃ values_c, " + c + " ↦*{dq} values_c ∗ ⌜ value = " + module(elem) + ".of_go <$> values_c ⌝"
            proof = (opening + 'iDestruct "' + hypothesis + '" as (values_c) "[Hsl %Heq]". '
                     + 'iMod (own_slice_persist with "Hsl") as "Hsl". iModIntro. iExists values_c. iFrame "# ∗ %".')
        result.append((hypothesis, "(match " + v + " with Some value => " + some + " | None => True%I end)", proof, "done.", False))
        if child["Kind"] == "slice":
            result.append((tag + "_cap", "own_slice_cap " + ctype + " " + c + " dq",
                           'iPersist "' + tag + '_cap". by iModIntro.',
                           "iApply (deepown_slice_cap_nil (C := " + ctype + ") (V := unit)).", False))
        return result

    def update_configs():
        for pkg, (_, path, _) in PACKAGES.items():
            names = sorted(n["Name"] for n in nodes.values() if n["Pkg"] == pkg and n["Name"])
            config_path = ROOT / "src/code" / (path + ".v.toml")
            config_path.parent.mkdir(parents=True, exist_ok=True)
            if config_path.exists():
                text = config_path.read_text()
                config = tomllib.loads(text)
                missing = [name for name in names if name not in config.get("translate", [])]
                if missing:
                    end = text.index("]", text.index("translate"))
                    text = text[:end] + "\n    # Complete recursive object representations.\n" + "".join(
                        '    "' + name + '",\n' for name in missing) + text[end:]
            else:
                text = "translate = [\n" + "".join('    "' + name + '",\n' for name in names) + "]\n\nimports = [\"!*\"]\n"
            imports = []
            if pkg == CORE:
                imports = ["k8s.io/apimachinery/pkg/util/intstr"]
            elif pkg == APPS:
                imports = ["k8s.io/apimachinery/pkg/runtime"]
            elif pkg == "k8s.io/apimachinery/pkg/api/resource":
                imports = ["gopkg.in/inf.v0"]
            elif pkg == "gopkg.in/inf.v0":
                imports = ["math/big"]
            config = tomllib.loads(text)
            missing = [pkg for pkg in imports if pkg not in config.get("imports", [])]
            if missing:
                end = text.index("]", text.index("imports"))
                prefix = text[:end].rstrip()
                if prefix.endswith('"'):
                    prefix += ","
                text = prefix + "".join('\n    "' + pkg + '",' for pkg in missing) + "\n" + text[end:]
            if not config_path.exists() or config_path.read_text() != text:
                config_path.write_text(text)

    if args.config:
        update_configs()
        return

    header = [
        "(* Generated by scripts/generate_views.py; edit the generator rather than this file. *)",
        "From New.proof Require Import prelude empty_ffi util.",
        "From New.proof Require Export deepown.",
    ]
    structs = [key for key in order if nodes[key]["Kind"] == "struct"]
    outputs = {}
    for name, group in groups.items():
        context = contexts[group["context"]]
        imports = ["From " + module.rsplit(".", 1)[0] + " Require Export " + module.rsplit(".", 1)[1] + "."
                   for module in context["imports"]]
        aliases = ["Module " + alias + " := " + package_modules[alias] + "." for alias in context["aliases"]]
        dependencies = list(groups)[:list(groups).index(name)]
        outputs[name] = header + imports
        if dependencies:
            outputs[name].append("From New.generatedviews Require Export " + " ".join(dependencies) + ".")
        outputs[name] += aliases + ["", "Module " + group["module"] + "."]
    for key in structs:
        current_group = owners[key]
        context = contexts[groups[current_group]["context"]]
        lines = outputs[current_group]
        n = nodes[key]
        mod = module(key)
        ctype = physical(key)
        fields = view_fields[key]
        entries = [entry for field in fields for entry in field_entries(key, field)] if owns_heap(key) else []
        lines.extend([
            "", "Module " + mod + ".", "Section def.",
            "Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.",
            "Context {sem : go.Semantics}",
            *("  {" + binder + " : " + package_modules[alias] + ".Assumptions}"
              + ("." if index == len(context["assumptions"]) - 1 else "")
              for index, (binder, alias) in enumerate(context["assumptions"].items())),
            'Local Set Default Proof Using "All".', "",
        ])
        for name, reason in exclusions.get(key, {}).items():
            lines.extend(["(* " + key + "." + name + " is intentionally excluded from the view and deepown.",
                          "   " + " ".join(reason.split()) + " *)"])
        if raw_pure(key):
            lines.extend(["Definition t := " + ctype + ".",
                          "#[global] Instance eq_dec : EqDecision t.",
                          "Proof using Type. unfold t. solve_decision. Defined.",
                          "Definition of_go (c : " + ctype + ") : t := c.",
                          "Definition deepown (c : " + ctype + ") (v : t) (_dq : dfrac) : iProp Σ := ⌜c = v⌝."])
        else:
            lines.append("Record t := mk {")
            for f in fields:
                lines.append("  " + f["Name"] + "' : " + view(f["Type"]) + ";")
            lines.extend(["}.", "", "#[global] Instance eq_dec : EqDecision t.",
                          "Proof using Type. solve_decision. Defined.", ""])
            if not owns_heap(key):
                if fields:
                    lines.append("Definition of_go (c : " + ctype + ") : t := {|")
                    for f in fields:
                        value = "c.(" + ctype[:-2] + "." + f["Name"] + "')"
                        lines.append("  " + f["Name"] + "' := " + of_go(f["Type"], value) + ";")
                    lines.append("|}.")
                else:
                    lines.append("Definition of_go (c : " + ctype + ") : t := mk.")
                lines.append("Definition deepown (c : " + ctype + ") (v : t) (_dq : dfrac) : iProp Σ := ⌜of_go c = v⌝.")
            else:
                lines.append("Definition deepown (c : " + ctype + ") (v : t) dq : iProp Σ :=")
                for i, (tag, expr, _, _, pure) in enumerate(entries):
                    lines.append('  "' + ("%" if pure else "") + tag + '" ∷ ' + expr + ("." if i == len(entries) - 1 else " ∗"))
        if owns_heap(key) and len(fields) >= 10:
            lines.extend(["", "Lemma deepown_unfold c v dq : deepown c v dq ⊣⊢"])
            for i, (tag, expr, _, _, pure) in enumerate(entries):
                lines.append('  "' + ("%" if pure else "") + tag + '" ∷ ' + expr + ("." if i == len(entries) - 1 else " ∗"))
            lines.extend(["Proof. done. Qed."])
        lines.extend(["", "Definition deepown_l l v dq : iProp Σ := ∃ c, l ↦{dq} c ∗ deepown c v dq.", ""])
        if key in {META + "/Preconditions", META + "/DeleteOptions"}:
            lines.extend([
                "Definition valid_interface i (l : loc) : Prop :=",
                "  i = interface.mk (go.PointerType " + ctype[:-2] + ") #l.", "",
                "Definition deepown_i i v dq : iProp Σ :=",
                "  ∃ l, ⌜ valid_interface i l ⌝ ∗ deepown_l l v dq.", "",
            ])
        if has_zero(key):
            if raw_pure(key):
                lines.append("Definition zero : t := zero_val _.")
            elif not fields:
                lines.append("Definition zero : t := mk.")
            else:
                lines.append("Definition zero : t := {|")
                for f in fields:
                    lines.append("  " + f["Name"] + "' := " + zero(f["Type"]) + ";")
                lines.append("|}.")
            lines.extend(["Lemma deepown_zero dq : ⊢ deepown (zero_val " + ctype + ") zero dq.", "Proof."])
            if not owns_heap(key):
                lines.append("  rewrite /deepown /zero /of_go. iPureIntro. reflexivity.")
            else:
                lines.append("  rewrite /deepown /zero /=.")
                for entry in entries[:-1]:
                    lines.extend(["  iSplitL.", "  { " + entry[3] + " }"])
                lines.append("  " + entries[-1][3])
            lines.extend(["Qed.", ""])
        lines.extend(["Lemma deepown_persist c v dq :", "  deepown c v dq ⊢ |==> deepown c v DfracDiscarded.", "Proof."])
        if not owns_heap(key):
            lines.append('  rewrite /deepown. iIntros "H". by iModIntro.')
        else:
            lines.append('  rewrite /deepown. iNamed 1.')
            for tag, expression, proof, _, pure in entries:
                if pure:
                    continue
                discarded = expression.replace(" dq", " DfracDiscarded").replace("{dq}", "{DfracDiscarded}")
                lines.extend(["  iAssert (|==> " + discarded + ")%I",
                              '    with "[' + tag + ']" as ">' + tag + '".',
                              "  { " + proof + " }"])
            lines.append('  iModIntro. iFrame "# ∗ %".')
        lines.extend(["Qed.", "", "#[global] Instance deepown_persistent c v : Persistent (deepown c v DfracDiscarded).",
                      "Proof. rewrite /deepown."])
        if owns_heap(key):
            # Split before case analysis: destructing all optional fields together
            # creates exponentially many goals for records such as ObjectMeta.
            for i, (tag, _, _, _, _) in enumerate(entries):
                field = next((f for f in fields if tag == "Hdeepown_" + ("ignorestorereaderror" if f["Name"] == "IgnoreStoreReadErrorWithClusterBreakingPotential" else f["Name"].lower()) + "_some"), None)
                proof = ("destruct (v.(" + field["Name"] + "')); apply _." if field else "apply _.")
                if i < len(entries) - 1:
                    lines.extend(["  apply bi.sep_persistent.", "  { " + proof + " }"])
                else:
                    lines.append("  " + proof)
        else:
            lines.append("  apply _.")
        lines.extend([
            "Qed.", "",
            "Lemma deepown_l_persist l v dq :",
            "  deepown_l l v dq ⊢ |==> deepown_l l v DfracDiscarded.",
            "Proof.",
            '  iDestruct 1 as (c) "[Hl Hdeepown]".',
            '  iPersist "Hl". iMod (deepown_persist with "Hdeepown") as "Hdeepown".',
            '  iModIntro. iExists c. by iFrame "∗ #".',
            "Qed.", "",
            "#[global] Instance deepown_l_persistent l v :",
            "  Persistent (deepown_l l v DfracDiscarded).",
            "Proof. rewrite /deepown_l. apply _. Qed.",
            "End def.",
        ])
        if owns_heap(key) and len(fields) >= 10:
            lines.extend(["", "(* Avoid unfolding unrelated large ownership predicates during proof search. *)",
                          "#[global] Opaque deepown."])
        lines.append("End " + mod + ".")
    for group, lines in outputs.items():
        current_group = group
        # A Pod can reach PVC spec through an ephemeral volume before the PVC
        # root is visited. Reexport spec/status under their resource namespace
        # without duplicating the shared representation or introducing cycles.
        aliases = {}
        for root in schema["Roots"][group]:
            if owners[root] != group:
                canonical = module(root)
                aliases[canonical.rsplit(".", 1)[-1]] = canonical
            for field in view_fields[root]:
                child = field["Type"]
                if field["Name"] in {"Spec", "Status"} and nodes[child]["Kind"] == "struct" and owners[child] != group:
                    aliases[nodes[child]["Name"] + "V"] = module(child)
        for name, canonical in aliases.items():
            lines.extend(["", "Module " + name + " := " + canonical + "."])
        lines.extend(["", "End " + groups[group]["module"] + ".", ""])
        for name, target in groups[group].get("exports", {}).items():
            lines.extend(["Module " + name + " := " + target + ".", ""])
        target = args.output_dir / (group + ".v")
        generated = "\n".join(lines)
        if args.check:
            if not target.exists() or target.read_text() != generated:
                raise SystemExit(f"{target} is stale; run scripts/goose.sh")
        elif not target.exists() or target.read_text() != generated:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(generated)
    print(f"{'Checked' if args.check else 'Generated'} {len(structs)} struct views in {args.output_dir}")


if __name__ == "__main__":
    main()
