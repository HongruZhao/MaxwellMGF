# Maxwell's Speed Law via MGFs

**Author: Hongru Zhao.** STAT 4052, Fall 2026. Local release v1.0.0.

**GitHub publication: pending.** No remote URL or remote commit is claimed. The
course submission is not administratively complete until a working repository
link and its checked commit/release are added to the report. No upload or
submission has been performed.

The main theorem derives independent Gaussian velocity components from a smooth,
positive, normalized, factorized isotropic density, then proves the one-square
and three-square chi-square laws through MGFs. It proves the Maxwell speed law
as an equality of measures, including the chi-square-to-speed pushforward and
normalization. The velocity vector and its nonnegative speed are distinct.

## Read first

- [Three-page report](report/Maxwell_MGF_Report.pdf).
- [Editable LaTeX](report/latex/main.tex).
- [Exact assumptions](ASSUMPTIONS.md): three disclosed textbook axioms and the
  separate physical/model hypotheses.
- [Statement-to-code map](VERIFICATION_SCOPE.md).
- [Axiom audit](verification/axioms.log) and [build log](verification/build.log).
- [Machine-readable source audit](verification/source-audit.json).
- [Fresh-extraction rebuild receipt](verification/clean-replay.json): the project
  modules and report were rebuilt from an extracted source archive using the
  same pinned library cache; all mathematical-source hashes and report text matched.

## Rebuild the Lean development

Install [elan](https://github.com/leanprover/elan), then open a terminal in this
directory. The toolchain is Lean **v4.33.0-rc2** and mathlib is pinned to
**641fbd329d4ffb62bef83c51f54088469056bd36**. All transitive dependency
revisions are in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The first command downloads dependencies and the matching compiled library
cache. Compiler/dependency binaries and `.lake/` are intentionally absent from
the source archive. Do not upgrade Lean independently of mathlib. On macOS or
Linux, after retrieving the cache, use:

```sh
bash scripts/verify.sh
```

This rebuilds the project, records current compiler/build/axiom logs, checks all
project theorem audit entries, rejects proof holes, and checks the exact set of
three permitted additional axioms. Python 3 is used only for the source/audit
check; the mathematical checker is Lean's kernel. On Windows, the three Lake
commands above can be run directly, followed by `python scripts/check_sources.py`.

## Formal statements and conventions

`MaxwellDemo.SmoothModel` contains differentiable real functions `g,H`, the
identity `g(x)+g(y)+g(z)=H(x²+y²+z²)`, integrability of `exp(g)`, and its integral
equal to one. Writing `f=exp(g)` ensures strict positivity. The law of the chosen
measurable velocity variable is assumed to have density
`f(v₀) f(v₁) f(v₂)` on `EuclideanSpace ℝ (Fin 3)`. This is the physical model;
there is no assumed Gaussian shape. Mutual independence is encoded by density
factorization, not deduced from perpendicular axes.

`MaxwellMGF.maxwell_mgf_project` returns a positive parameter `b` and the complete
`MaxwellMGF.Conclusions` proposition. The code defines
`sigma(b)=sqrt(1/(2*b))`, proves it positive, and proves that its square is the
variance. `varianceParameter` is the same variance as a nonnegative real, the
type used by mathlib's `gaussianReal`.

The velocity joint law is an actual product of three Gaussian measures on
`Fin 3 → ℝ`. This identifies the full law conventionally denoted
`N₃(0, sigma² I₃)`, not just three Gaussian marginals or a covariance matrix.
The joint MGF is expressed as the scalar MGF of the linear combination at 1.

The variables `squares b V i` are `2*b*(V_i)²`; `standardized_square` proves they
are exactly `(V_i/sigma)²`. `sumSquares` is their finite sum. The chi-square
distribution is represented by mathlib's **shape/rate** Gamma measure:

- chi-square 1 = `gammaMeasure (1/2) (1/2)`;
- chi-square 3 = `gammaMeasure (3/2) (1/2)`.

Every claimed distribution has a `Measure.map` equality. The square and sum MGFs
are proved for every `t<1/2`, together with the required exponential
integrability. MGF uniqueness is invoked on the explicit neighborhood
`abs(t)<1/4`.

`gamma_speed_pushforward` checks the transformation of the Gamma law by
`s ↦ sigma*sqrt(s)`. The density itself is verified by polar integration of the
derived Gaussian velocity density. `speedLaw_full_density` converts the
restricted positive-half-line representation to ordinary Lebesgue density on
the whole real line. `speed_density_sigma` proves the requested formula with
density zero for negative speeds. The value at zero is zero.

## Main files

| File | Role |
|---|---|
| `MaxwellMGF/Core.lean` | Calculus characterization, normalization, polar integration, speed pushforward, and a nonempty model witness. |
| `MaxwellMGF/Background.lean` | Exactly three explicitly declared and cited background axioms. |
| `MaxwellMGF/Distributions.lean` | Actual Gaussian marginal/joint laws, joint MGF, independent squares, square/sum MGFs and Gamma law equalities. |
| `MaxwellMGF/Speed.lean` | Scale conversion, pointwise speed identity, whole-line density, normalization, Gamma-to-speed pushforward. |
| `MaxwellMGF/Project.lean` | Complete result collected in `Conclusions` and proved in `maxwell_mgf_project`. |
| `AxiomAudit.lean` | Prints hypotheses, conclusion fields, exact background statements, and dependencies of every project theorem. |

The core reuses the existing local STAT 4052 Maxwell demonstration by Hongru Zhao
with Codex assistance. It is credited in `PROVENANCE.md`. A small expected-count
theorem retained in the core is not needed by the project's main theorem.

## Rebuild the report

Use [Tectonic](https://tectonic-typesetting.github.io/):

```sh
bash scripts/build-report.sh
```

Pass the compiler's absolute path as the first argument if it is not on PATH.
Alternatively compile `report/latex/main.tex` with pdfLaTeX twice. The LaTeX
source contains its bibliography and needs no external figures or `.bib` file.
The delivered PDF is three pages including references and contains no Lean
source code. Render every page again after changing the source.

## What is and is not verified

The full theorem is conditional on the physical model and three generic
mathematical axioms: product-density factorization, Gamma MGFs, and MGF
uniqueness. None assumes a Maxwell-specific conclusion. The core Gaussian
characterization and direct speed-law proof use only standard Lean/mathlib
foundations. See `ASSUMPTIONS.md` for precise statements and citations.

Local project modules were rebuilt against the pinned existing compiled
mathlib cache. This is not a fresh rebuild of all mathlib source. The existing
cache has file-type changes in two benchmark scripts and one batteries README;
there are no changed tracked Lean sources in those dependencies. The exact
status is recorded in `verification/dependency-status.txt`. These cache files
are not included in the archive or required by the project.

The mathematical theorem does not prove equilibrium from collisions, justify
the physical independence postulate, establish minimal regularity, or identify
temperature. The author must review the work and explain the theorem. The
report discloses Codex's role. Course team-size/subscription eligibility and
final submission remain the submitter's responsibility.

## Publication checklist

1. Review the report and assumptions, and confirm course team eligibility.
2. Create/push this repository to the intended GitHub account with appropriate
   visibility; no remote action has been taken here.
3. Rebuild from a fresh download of that remote version, and inspect its audit.
4. Replace the publication-pending line in the report with the verified URL and
   the exact commit or release; rebuild and inspect the final PDF.

References are linked in the report and in `ASSUMPTIONS.md`; library sources and
the reused local core are listed in `PROVENANCE.md`.
