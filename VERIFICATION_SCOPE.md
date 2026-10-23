# Theorem-to-Lean correspondence

The primary theorem is `MaxwellMGF.maxwell_mgf_project`, which returns a positive
real b and the proposition `MaxwellMGF.Conclusions μ V b`. It is conditional on
the exact physical/model hypotheses printed in `AxiomAudit.lean` and the three
background axioms in `ASSUMPTIONS.md`.

| Mathematical statement | Checked declarations | Evidence boundary |
|---|---|---|
| Positive common factor, isotropic log-density, normalization | `MaxwellDemo.SmoothModel`; `physicalModel` argument | These are hypotheses, not proved empirical facts. |
| Linear log-derivative and quadratic log-density | `derivative_radial`, `derivative_linear`, `log_quadratic` | Differentiability is used explicitly. |
| b>0 and normalized Gaussian density | `decay_positive`, `maxwell_characterization` | No assumed Gaussian shape; standard mathlib foundations only. |
| Nonempty analytic model | `gaussianModel`, `model_nonempty` | A witness, not a premise of the characterization. |
| Factorization implies independence and correct marginals | `model_facts`, `derived_components` | Conditional on generic input A1. |
| One-dimensional Gaussian measure | `component_gaussian`; `Conclusions.componentGaussian` | Actual marginal pushforward to `gaussianReal`. |
| Full joint Gaussian law | `joint_gaussian`; `Conclusions.jointGaussian` | Product of three Gaussian measures on `Fin 3 → ℝ`; specifies the entire law. |
| Joint MGF and finiteness | `joint_mgf`; `Conclusions.velocityMGF`, `.velocityMGFFinite` | MGF of each linear combination evaluated at 1; all real coefficient vectors. |
| Positive σ and σ²=1/(2b) | `sigma_pos`, `sigma_sq`, `variance_coe` | `varianceParameter` is a nonnegative-real representation of the same number. |
| U_i=(V_i/σ)² | `standardized_square`; `Conclusions.squareDefinition` | `squares` is defined as 2b V_i² and proved equal to the displayed standardized square. |
| Squared components remain mutually independent | `squares_independent` | Proved mathlib measurable-composition lemma. |
| MGF and integrability of each U_i | `quadratic_mgf`, `quadratic_integrable`, `square_mgf`, `square_integrable` | Gaussian integral is evaluated; square-normal law is not an axiom. |
| Each U_i has chi-square 1 law | `square_law`; `Conclusions.squareLaw` | Actual map equality to the shape/rate Gamma(1/2,1/2); uses A2 and A3. |
| Sum MGF and finiteness for t<1/2 | `sum_mgf`, `sum_integrable` | Independence plus multiplication; no sum-law axiom. |
| S has chi-square 3 law | `sum_law`; `Conclusions.sumLaw` | Actual map equality to Gamma(3/2,1/2); uses A2/A3 on abs(t)<1/4. |
| R=σ sqrt S pointwise | `norm_sumSquares`, `speed_transform` | Nonnegativity of the norm fixes the square-root branch. |
| Maxwell speed measure | `MaxwellDemo.speed_pushforward`; `Conclusions.speedLaw` | Direct polar-integration proof; standard foundations only for the canonical Gaussian density. |
| Maxwell density in σ parameterization | `speed_density_sigma`; `Conclusions.speedDensity` | Includes zero density for negative speeds. |
| Gamma-to-speed transformation | `gamma_speed_pushforward`; `Conclusions.gammaSpeedLaw` | Equality of mapped Gamma measure and Maxwell measure. Composes actual laws; uses A2/A3. |
| Whole-line Lebesgue density | `speedLaw_full_density`; `Conclusions.speedDensityLaw` | The half-line restriction is removed with a pointwise zero-density argument. |
| Normalization | `speed_density_integral`; `Conclusions.normalized` | Integral over all real numbers equals 1. |

Core declarations are in namespace `MaxwellDemo`; all other project results are
in `MaxwellMGF`. The mathematical subscripts 1,2,3 correspond to Lean's indices 0,1,2.
In the joint-MGF statement, the sum of squared real coordinates is the Euclidean
squared norm of the coefficient vector.

## Actual checked scope

The direct density characterization and polar speed pushforward are entirely
proved using the pinned mathlib library. The complete MGF/Gamma route has three
explicit generic background inputs. These are not proof placeholders, but their
truth is assumed and cited rather than formalized here.

The formal code verifies the speed density by polar integration and proves the
Gamma transformation by map composition and the pointwise speed identity. It
does not contain a separate formal derivation of the Gamma-density Jacobian
simplification.

No collision dynamics, approach to equilibrium, physical independence proof,
temperature calibration, observed-count guarantee, or minimal-regularity
characterization is included in the main theorem.
