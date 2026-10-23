# Maxwell distribution in Lean 4

**Author:** Hongru Zhao · **Course:** STAT 4052, Fall 2026

## Theorem

For a molecule in an ideal gas at equilibrium in its bulk rest frame, assume
**(1) isotropy** and
**(2) independent Cartesian velocity components**, with the positive, normalized,
smooth density specified in [SmoothModel](MaxwellMGF/Core.lean#L15-L22) and
[modelVelocityLaw](MaxwellMGF/Core.lean#L218-L219).
Conditional on the three external axioms below, the components are centered
Gaussian with a common variance, their
standardized squares have chi-square laws, and the speed has the Maxwell law.
The code proves equalities of probability measures and MGF finiteness.

The exact Lean endpoint is
[`MaxwellMGF.maxwell_mgf_project`](MaxwellMGF/Project.lean#L43-L78):

```lean
MaxwellMGF.maxwell_mgf_project.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ] (V : Ω → MaxwellDemo.Velocity) (hV : Measurable V)
  (M : MaxwellDemo.SmoothModel) (physicalModel : MeasureTheory.Measure.map V μ = MaxwellDemo.modelVelocityLaw M) :
  ∃ b, MaxwellMGF.Conclusions μ V b
```

[`Conclusions`](MaxwellMGF/Project.lean#L13-L40) contains the full result.
**[Read the complete theorem, exact conclusion, and definition locations](THEOREM.md).**

## External axioms used

The complete theorem assumes exactly three additional mathematical axioms,
declared in [Background.lean](MaxwellMGF/Background.lean). They are cited
background results; their proofs are not formalized in this project.

| Exact Lean name | What is assumed | Where it is used |
|---|---|---|
| [`MaxwellMGF.Background.product_density`](MaxwellMGF/Background.lean#L13-L20) | A normalized product density gives mutually independent coordinates and the stated marginal laws. | `model_facts`, then `derived_components`. |
| [`MaxwellMGF.Background.gamma_mgf`](MaxwellMGF/Background.lean#L25-L27) | For shape/rate Gamma(a,r), exp(t x) is integrable and the MGF is (1 − t/r)^(−a) whenever a,r > 0 and t < r. | The comparison Gamma MGFs in `square_law` and `sum_law`. |
| [`MaxwellMGF.Background.mgf_unique`](MaxwellMGF/Background.lean#L32-L37) | Two probability laws with finite, equal MGFs on a common open neighborhood of zero are equal. | Identifying the one-square and three-square laws; the Gamma-to-speed result uses the sum law. |

Isotropy, density factorization, positivity, normalization, and differentiability
are explicit **model hypotheses**. The three axioms above are separate global
inputs. The Gaussian shape, chi-square conclusions, and Maxwell speed law are
derived in the code.

The axiom audit also lists Lean's standard foundations: `propext`
(propositional extensionality), `Classical.choice`, and `Quot.sound`
(quotient soundness). The direct Gaussian characterization and polar speed
pushforward use only those standard foundations. See
[exact assumptions and references](ASSUMPTIONS.md) and
[the recorded audit](verification/axioms.log).

## Build and check

Install [Lean with elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Lean `v4.33.0-rc2` and mathlib
`641fbd329d4ffb62bef83c51f54088469056bd36` are pinned. For the build, axiom
audit, and source check together, run `bash scripts/verify.sh` (requires Python 3).
The 48 theorem audits disclose the three background axioms; there are no proof
holes. Verification reused the pinned compiled mathlib cache.

## Files

- [Theorem and definitions](THEOREM.md): exact Lean endpoint and full conclusion.
- [Core.lean](MaxwellMGF/Core.lean): Gaussian characterization and direct speed law.
- [Background.lean](MaxwellMGF/Background.lean): the three external axioms.
- [Distributions.lean](MaxwellMGF/Distributions.lean): independence, MGFs, and chi-square laws.
- [Speed.lean](MaxwellMGF/Speed.lean): speed transformation, density, and normalization.
- [Project.lean](MaxwellMGF/Project.lean): the assembled theorem.
- [AxiomAudit.lean](AxiomAudit.lean): printed statements and axiom dependencies.
- [Proof map](VERIFICATION_SCOPE.md), [verification logs](verification/), and [credits](PROVENANCE.md).

OpenAI Codex assisted with the Lean code and documentation. The author remains
responsible for understanding the theorem and its assumptions. Collision-driven
equilibration and temperature calibration are outside the theorem.

**Version:** `v1.0.5`. Anyone can read, download, or fork this public repository;
only the owner and authorized collaborators can change this repository.
