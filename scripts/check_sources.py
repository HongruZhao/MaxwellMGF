#!/usr/bin/env python3
"""Check project proof-hole policy, declared inputs, audit coverage, and dependencies."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    "MaxwellMGF.Background.product_density",
    "MaxwellMGF.Background.gamma_mgf",
    "MaxwellMGF.Background.mgf_unique",
}


def without_comments(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j == -1 else j
        else:
            result.append(text[i])
            i += 1
    assert depth == 0, "Unclosed Lean comment"
    return "".join(result)


def main():
    audit = (ROOT / "AxiomAudit.lean").read_text()
    declarations, theorems = set(), []
    for p in sorted(ROOT.glob("MaxwellMGF/*.lean")):
        source = without_comments(p.read_text())
        assert not re.search(r"\b(sorry|admit|sorryAx)\b", source), p
        namespace = "MaxwellDemo" if p.stem == "Core" else "MaxwellMGF"
        if p.stem == "Background":
            namespace += ".Background"
        for name in re.findall(r"^axiom\s+(\w+)", source, re.M):
            declarations.add(namespace + "." + name)
        for name in re.findall(r"^theorem\s+(\w+)", source, re.M):
            full = namespace + "." + name
            assert "#print axioms " + full in audit, "Missing audit: " + full
            theorems.append(full)
    assert declarations == EXPECTED, declarations
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == "641fbd329d4ffb62bef83c51f54088469056bd36"
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0-rc2"
    log = (ROOT / "verification/axioms.log").read_text()
    assert "error:" not in log and "sorryAx" not in log
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S)
    dependencies = {n: set(re.findall(r"[\w.]+", xs)) for n, xs in entries}
    allowed = EXPECTED | {"propext", "Classical.choice", "Quot.sound"}
    for name in theorems:
        assert name in dependencies, "Missing audit output: " + name
        assert dependencies[name] <= allowed, (name, dependencies[name] - allowed)
    assert dependencies["MaxwellMGF.maxwell_mgf_project"] == allowed
    for name in ["MaxwellDemo.maxwell_characterization", "MaxwellDemo.speed_pushforward"]:
        assert dependencies[name].isdisjoint(EXPECTED)
    result = {
        "project_theorems_audited": len(theorems),
        "proof_holes": 0,
        "additional_axioms": sorted(EXPECTED),
        "main_theorem_axioms": sorted(dependencies["MaxwellMGF.maxwell_mgf_project"]),
        "lean": "v4.33.0-rc2",
        "mathlib": mathlib["rev"],
        "publication": "pending",
    }
    (ROOT / "verification/source-audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
