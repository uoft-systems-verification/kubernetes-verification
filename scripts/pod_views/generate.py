#!/usr/bin/env python3
"""Generate complete pure Pod field views from the checked-out Kubernetes types.

Goose remains responsible for src/code and src/generatedproof. This generator
only writes translation configuration and the pure ownership models in src/proof.
scripts/goose.sh updates the configurations and regenerates these views. Use
--check to compare the checked-in views with the current Kubernetes Go types.

Pointers become options; slices and maps become optional lists/maps, preserving
nil versus allocated empty values. Heap-free Go records can themselves be pure
views. Object metadata and timestamp fields reuse the existing ownership models;
timestamps describe instants, excluding the shared runtime time-zone objects.
Internal big.Int word buffers are lists: copying may change empty-buffer nilness
without changing their words. Their entire backing storage is still owned.
The generated models describe representation, not API validation or defaulting.
"""

import argparse
import functools
import json
import os
from pathlib import Path
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[2]
CORE = "k8s.io/api/core/v1"
META = "k8s.io/apimachinery/pkg/apis/meta/v1"
BIG_NAT = "math/big/nat"
PACKAGES = {
    CORE: ("api_core_v1", "k8s_io/api/core/v1"),
    META: ("meta_v1", "k8s_io/apimachinery/pkg/apis/meta/v1"),
    "k8s.io/apimachinery/pkg/api/resource": ("resource", "k8s_io/apimachinery/pkg/api/resource"),
    "k8s.io/apimachinery/pkg/util/intstr": ("intstr", "k8s_io/apimachinery/pkg/util/intstr"),
    "gopkg.in/inf.v0": ("inf", "gopkg_in/inf_v0"),
    "math/big": ("big", "math/big"),
}
EXISTING = {
    META + "/Time": "TimeV",
    META + "/ObjectMeta": "ObjectMetaV",
}
# Generate selectors separately: the legacy LabelSelectorV keeps its expression
# slice exclusive even at DfracDiscarded. Complete Pod views respect the supplied
# fraction throughout so they can be shared persistently.
SCALARS = {
    "string": "go_string", "bool": "bool", "int": "w64", "uint": "w64",
    "int64": "w64", "uint64": "w64", "int32": "w32", "uint32": "w32",
    "int16": "w16", "uint16": "w16", "int8": "w8", "uint8": "w8",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", action="store_true", help="update Goose type translation configuration")
    parser.add_argument("--check", action="store_true", help="check views without writing files")
    parser.add_argument("--schema", type=Path, help="reuse a reflection schema for development")
    args = parser.parse_args()
    if args.config and args.check:
        parser.error("--config and --check cannot be combined")
    if args.schema:
        schema = json.loads(args.schema.read_text())
    else:
        env = dict(os.environ)
        env.setdefault("GOCACHE", "/tmp/go-build")
        # Match scripts/goose.sh even when the installed Go version differs.
        env["GOTOOLCHAIN"] = "go" + next(
            line.split()[1] for line in (ROOT / "go.mod").read_text().splitlines()
            if line.startswith("go ")
        )
        schema = json.loads(subprocess.check_output(
            ["go", "run", str(Path(__file__).with_name("schema.go"))],
            cwd=ROOT / "kubernetes", env=env, text=True,
        ))
    nodes = schema["Nodes"]
    order = schema["Order"]

    def module(key):
        if key in EXISTING:
            return EXISTING[key]
        n = nodes[key]
        if n["Pkg"] == "math/big" and n["Name"] == "Int":
            return "BigIntV"
        if n["Pkg"] == "gopkg.in/inf.v0" and n["Name"] == "Dec":
            return "DecimalV"
        return n["Name"][0].upper() + n["Name"][1:] + "V"

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
        if key in EXISTING:
            return "meta_v1." + n["Name"] + ".t"
        raise ValueError("Unsupported physical type: " + key)

    @functools.cache
    def raw_pure(key):
        if key in EXISTING:
            return False
        n = nodes[key]
        return n["Kind"] in SCALARS or (n["Kind"] == "struct" and
            all(raw_pure(f["Type"]) for f in n["Fields"]))

    @functools.cache
    def owns_heap(key):
        if key in EXISTING:
            return key != META + "/Time"
        n = nodes[key]
        return n["Kind"] in {"ptr", "slice", "map"} or (n["Kind"] == "struct" and
            any(owns_heap(f["Type"]) for f in n["Fields"]))

    def view(key):
        n = nodes[key]
        if key == BIG_NAT:
            return "list (" + view(n["Elem"]) + ")"
        if key in EXISTING or n["Kind"] == "struct":
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
        if key in EXISTING or nodes[key]["Kind"] == "struct":
            return "(" + module(key) + ".of_go " + value + ")"
        if nodes[key]["Kind"] in SCALARS:
            return value
        raise ValueError("Heap-backed values have no of_go projection: " + key)

    def predicate(key):
        n = nodes[key]
        if key in EXISTING or n["Kind"] == "struct":
            return module(key) + ".deepown"
        if n["Kind"] in SCALARS:
            return "(λ c v (_ : dfrac), ⌜ c = v ⌝)%I"
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return "(deepown_" + op + " " + predicate(n["Elem"]) + ")"

    def persist(key):
        n = nodes[key]
        if key in EXISTING or n["Kind"] == "struct":
            return "apply " + module(key) + ".deepown_persist."
        if n["Kind"] in SCALARS:
            return 'iIntros "H". by iModIntro.'
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return ("apply deepown_" + op
                + "_persist. intros. " + persist(n["Elem"]))

    @functools.cache
    def has_zero(key):
        if key in EXISTING:
            return key == META + "/Time"
        n = nodes[key]
        return n["Kind"] != "struct" or all(has_zero(f["Type"]) for f in n["Fields"])

    def zero(key):
        n = nodes[key]
        if key == BIG_NAT:
            return "[]"
        if key in EXISTING or n["Kind"] == "struct":
            return module(key) + ".zero"
        if n["Kind"] in {"ptr", "slice", "map"}:
            return "None"
        return "zero_val _"

    def zero_proof(key):
        n = nodes[key]
        if key in EXISTING or n["Kind"] == "struct":
            return "iApply " + module(key) + ".deepown_zero."
        if n["Kind"] in SCALARS:
            return "done."
        op = "slice_list" if key == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[n["Kind"]]
        return "iApply deepown_" + op + "_nil."

    def update_configs():
        for pkg, (_, path) in PACKAGES.items():
            names = sorted(n["Name"] for n in nodes.values() if n["Pkg"] == pkg and n["Name"])
            config_path = ROOT / "src/code" / (path + ".v.toml")
            config_path.parent.mkdir(parents=True, exist_ok=True)
            if config_path.exists():
                text = config_path.read_text()
                config = tomllib.loads(text)
                missing = [name for name in names if name not in config.get("translate", [])]
                if missing:
                    end = text.index("]", text.index("translate"))
                    text = text[:end] + "\n    # Complete recursive Pod field representations.\n" + "".join(
                        '    "' + name + '",\n' for name in missing) + text[end:]
            else:
                text = "translate = [\n" + "".join('    "' + name + '",\n' for name in names) + "]\n\nimports = [\"!*\"]\n"
            imports = []
            if pkg == CORE:
                imports = ["k8s.io/apimachinery/pkg/util/intstr"]
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
            config_path.write_text(text)

    if args.config:
        update_configs()
        return

    lines = [
        "(* Generated by scripts/pod_views/generate.py; edit the generator rather than this file. *)",
        "From New.proof Require Import prelude empty_ffi util.",
        "From New.proof.kubernetes_types Require Export deepown objectmeta.",
        "Module api_core_v1 := code.k8s_io.api.core.v1.v1.",
        "Module meta_v1 := code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.",
        "Module resource := code.k8s_io.apimachinery.pkg.api.resource.resource.",
        "Module intstr := code.k8s_io.apimachinery.pkg.util.intstr.intstr.",
        "Module inf := code.gopkg_in.inf_v0.inf.",
        "Module big := code.math.big.big.",
        "", "Module PodFields.",
    ]
    structs = [key for key in order if nodes[key]["Kind"] == "struct" and key not in EXISTING]
    for key in structs:
        n = nodes[key]
        mod = module(key)
        ctype = physical(key)
        lines.extend([
            "", "Module " + mod + ".", "Section def.",
            "Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.",
            "Context {sem : go.Semantics}",
            "  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}",
            "  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}",
            "  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.",
            'Local Set Default Proof Using "All".', "",
        ])
        if raw_pure(key):
            lines.extend(["Definition t := " + ctype + ".",
                          "#[global] Instance eq_dec : EqDecision t.",
                          "Proof using Type. unfold t. solve_decision. Defined.",
                          "Definition of_go (c : " + ctype + ") : t := c.",
                          "Definition deepown (c : " + ctype + ") (v : t) (_dq : dfrac) : iProp Σ := ⌜c = v⌝."])
        else:
            lines.append("Record t := mk {")
            for f in n["Fields"]:
                lines.append("  " + f["Name"] + "' : " + view(f["Type"]) + ";")
            lines.extend(["}.", "", "#[global] Instance eq_dec : EqDecision t.",
                          "Proof using Type. solve_decision. Defined.", ""])
            if not owns_heap(key):
                lines.append("Definition of_go (c : " + ctype + ") : t := {|")
                for f in n["Fields"]:
                    lines.append("  " + f["Name"] + "' := " + of_go(f["Type"], "c.(" + ctype[:-2] + "." + f["Name"] + "')") + ";")
                lines.extend(["|}.", "Definition deepown (c : " + ctype + ") (v : t) (_dq : dfrac) : iProp Σ := ⌜of_go c = v⌝."])
            else:
                lines.append("Definition deepown (c : " + ctype + ") (v : t) dq : iProp Σ :=")
                for i, f in enumerate(n["Fields"]):
                    expr = (predicate(f["Type"]) + " c.(" + ctype[:-2] + "." + f["Name"]
                            + "') v.(" + f["Name"] + "') dq")
                    pure_tag = "" if owns_heap(f["Type"]) else "%"
                    lines.append('  "' + pure_tag + 'Hdeepown_' + f["Name"].lower() + '" ∷ ' + expr + ("." if i == len(n["Fields"]) - 1 else " ∗"))
        lines.extend(["", "Definition deepown_l l v dq : iProp Σ := ∃ c, l ↦{dq} c ∗ deepown c v dq.", ""])
        if has_zero(key):
            if raw_pure(key):
                lines.append("Definition zero : t := zero_val _.")
            else:
                lines.append("Definition zero : t := {|")
                for f in n["Fields"]:
                    lines.append("  " + f["Name"] + "' := " + zero(f["Type"]) + ";")
                lines.append("|}.")
            lines.extend(["Lemma deepown_zero dq : ⊢ deepown (zero_val " + ctype + ") zero dq.", "Proof."])
            if not owns_heap(key):
                lines.append("  rewrite /deepown /zero /of_go. iPureIntro. reflexivity.")
            else:
                lines.append("  rewrite /deepown /zero /=.")
                for f in n["Fields"][:-1]:
                    lines.extend(["  iSplitL.", "  { " + zero_proof(f["Type"]) + " }"])
                lines.append("  " + zero_proof(n["Fields"][-1]["Type"]))
            lines.extend(["Qed.", ""])
        lines.extend(["Lemma deepown_persist c v dq :", "  deepown c v dq ⊢ |==> deepown c v DfracDiscarded.", "Proof."])
        if not owns_heap(key):
            lines.append('  rewrite /deepown. iIntros "H". by iModIntro.')
        else:
            lines.append('  rewrite /deepown. iNamed 1.')
            for f in n["Fields"]:
                if not owns_heap(f["Type"]):
                    continue
                tag = "Hdeepown_" + f["Name"].lower()
                child = nodes[f["Type"]]
                if child["Kind"] in {"ptr", "slice", "map"}:
                    operation = "slice_list" if f["Type"] == BIG_NAT else {"ptr": "ptr", "slice": "slice", "map": "map"}[child["Kind"]]
                    field_proof = ('iApply (deepown_' + operation + '_persist with "' + tag
                                   + '"). intros. ' + persist(child["Elem"]))
                else:
                    field_proof = 'iApply (' + module(f["Type"]) + '.deepown_persist with "' + tag + '").'
                lines.extend(["  iAssert (|==> " + predicate(f["Type"]) + " c.(" + ctype[:-2] + "." + f["Name"] + "') v.(" + f["Name"] + "') DfracDiscarded)%I",
                              '    with "[' + tag + ']" as ">' + tag + '".',
                              "  { " + field_proof + " }"])
            lines.append('  iModIntro. iFrame "# ∗ %".')
        lines.extend(["Qed.", "", "#[global] Instance deepown_persistent c v : Persistent (deepown c v DfracDiscarded).",
                      "Proof. rewrite /deepown. apply _. Qed.", "End def.", "End " + mod + "."])
    lines.extend(["", "End PodFields.", ""])
    target = ROOT / "src/proof/kubernetes_types/pod_fields.v"
    generated = "\n".join(lines)
    if args.check:
        if not target.exists() or target.read_text() != generated:
            raise SystemExit(f"{target.relative_to(ROOT)} is stale; run scripts/goose.sh")
        print(f"Checked {len(structs)} complete struct views against Kubernetes Go types")
        return
    target.write_text(generated)
    print(f"Generated {len(structs)} complete struct views in {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
