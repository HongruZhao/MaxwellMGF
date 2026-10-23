# Maxwell distribution in Lean 4

**Author:** Hongru Zhao

**Course:** STAT 4052, Fall 2026

This project derives Gaussian velocity components from a smooth, positive,
normalized, independent, isotropic density model. It then proves the chi-square
laws for squared components and their sum, and the Maxwell speed distribution.
The distribution statements are equalities of measures.

## Build

Install [Lean with elan](https://github.com/leanprover/elan), then run these
commands in this folder:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Lean `v4.33.0-rc2` and mathlib
`641fbd329d4ffb62bef83c51f54088469056bd36` are pinned in the dependency files.
The first command downloads the matching library cache. For a build, axiom
audit, and source check together, run `bash scripts/verify.sh` (requires Python 3).

## Result and assumptions

The main theorem is `MaxwellMGF.maxwell_mgf_project` in
[Project.lean](MaxwellMGF/Project.lean). Its full conclusion is `MaxwellMGF.Conclusions`.

The physical density model and differentiability assumptions are explicit
hypotheses. Three cited background results are assumed: the product-density
independence criterion, the Gamma MGF, and MGF uniqueness. Their exact statements
and references are in [ASSUMPTIONS.md](ASSUMPTIONS.md).
The code does not assume the Gaussian or Maxwell conclusions and does not prove
that collisions cause equilibrium.

## Files

- [Report](report/Maxwell_MGF_Report.pdf): three pages, including references and AI disclosure.
- [LaTeX source](report/latex/main.tex): editable report.
- [Core.lean](MaxwellMGF/Core.lean): Gaussian characterization and direct speed law.
- [Background.lean](MaxwellMGF/Background.lean): the three background axioms.
- [Distributions.lean](MaxwellMGF/Distributions.lean): independence, MGFs, and chi-square laws.
- [Speed.lean](MaxwellMGF/Speed.lean): speed transformation, density, and normalization.
- [AxiomAudit.lean](AxiomAudit.lean): theorem statements and axiom dependencies.
- [Verification logs](verification/): build, audit, PDF checks, and fresh-extraction replay.
- [Proof map](VERIFICATION_SCOPE.md) and [credits](PROVENANCE.md): detailed scope and reused work.

The checked development has no proof holes. Its 48 theorem audits disclose the
three background axioms. The local verification used the pinned compiled
mathlib cache; it did not rebuild every mathlib source file.

OpenAI Codex assisted with the code and report. The author remains responsible
for understanding the theorem and its assumptions.

**Repository:** [HongruZhao/MaxwellMGF](https://github.com/HongruZhao/MaxwellMGF) (private).
**Version:** `v1.0.3`. The instructor needs access to open or download it.
