# Maxwell's theorem: Lean statement and definitions

## Mathematical statement

Assume a molecule's velocity in the bulk rest frame of an equilibrium ideal gas
has **(1) an isotropic density** and **(2) independent Cartesian components**.
In Lean these assumptions are encoded by `SmoothModel.radial` and the product
density in `physicalModel`. Also assume the positivity, normalization, and
differentiability specified below.

Conditional on the three external axioms listed in the [README](README.md#external-axioms-used),
there exists $b>0$, with $\sigma=\sqrt{1/(2b)}>0$, such that

$$
V_i\sim N(0,\sigma^2),\qquad
U_i=(V_i/\sigma)^2\sim\chi^2_1,\qquad
S=\sum_{i=1}^3 U_i\sim\chi^2_3.
$$

The components are mutually independent, as are their separate squares.
The speed $R=\lVert V\rVert=\sigma\sqrt{S}$ has density

$$
p_R(r)=\begin{cases}
\sqrt{2/\pi}\,r^2\sigma^{-3}e^{-r^2/(2\sigma^2)},&r\geq 0,\\
0,&r<0,
\end{cases}
\qquad \int_{\mathbb R}p_R(r)\,dr=1.
$$

The joint MGF and the square/sum MGFs, including their integrability conditions,
are part of the full conclusion below. The Gamma convention is **shape/rate**:
a chi-square law with $k$ degrees of freedom is Gamma(k/2, 1/2).
Lean indexes components by `Fin 3`
(indices 0, 1, 2).

## Exact Lean endpoint

The following is the output of `#check MaxwellMGF.maxwell_mgf_project`.
[The theorem and its proof](MaxwellMGF/Project.lean#L43-L78) are in namespace
`MaxwellMGF`.

```lean
MaxwellMGF.maxwell_mgf_project.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ] (V : Ω → MaxwellDemo.Velocity) (hV : Measurable V)
  (M : MaxwellDemo.SmoothModel) (physicalModel : MeasureTheory.Measure.map V μ = MaxwellDemo.modelVelocityLaw M) :
  ∃ b, MaxwellMGF.Conclusions μ V b
```

`μ` is the probability measure, `V` is the measurable velocity, `M` is the
smooth density model, and `physicalModel` asserts that the actual velocity law
has that model's density. The positive parameter `b` is a conclusion.

## Model definition

Copied from [`MaxwellDemo.SmoothModel`](MaxwellMGF/Core.lean#L15-L22):

```lean
structure SmoothModel where
  g : ℝ → ℝ
  H : ℝ → ℝ
  dg : Differentiable ℝ g
  dH : Differentiable ℝ H
  radial : ∀ x y z : ℝ, g x + g y + g z = H (x^2 + y^2 + z^2)
  integrable : Integrable (fun x => exp (g x))
  normalized : ∫ x : ℝ, exp (g x) = 1
```

Here $f(x)=\exp(g(x))>0$. The `radial` identity says that the product
$f(x)f(y)f(z)$ depends only on $x^2+y^2+z^2$, expressing isotropy.
The definition of [`MaxwellDemo.modelVelocityLaw`](MaxwellMGF/Core.lean#L218-L219)
is exactly:

```lean
def modelVelocityLaw (M : SmoothModel) : Measure Velocity :=
  volume.withDensity (fun v => ENNReal.ofReal (exp (M.g (v 0)) * exp (M.g (v 1)) * exp (M.g (v 2))))
```

Thus the theorem's `physicalModel` hypothesis supplies the factorized density.
Axiom A1 then connects that density to mathlib's independence predicate. The
smoothness condition includes differentiability of `H` on all real numbers.

## Exact conclusion definition

Copied from [`MaxwellMGF.Conclusions`](MaxwellMGF/Project.lean#L13-L40).
The source opens `MeasureTheory`, `ProbabilityTheory`, `Real`, and `MaxwellDemo`,
with the `NNReal` and `ENNReal` scopes and `{Ω : Type*} [MeasurableSpace Ω]`.
The field `speedLaw` refers to `MaxwellDemo.speedLaw` on its right-hand side.

```lean
structure Conclusions (μ : Measure Ω) (V : Ω → Velocity) (b : ℝ) : Prop where
  positive : 0 < b
  sigmaPositive : 0 < sigma b
  variance : (varianceParameter b : ℝ) = (sigma b)^2
  independent : iIndepFun (fun i ω => V ω i) μ
  componentGaussian : ∀ i, μ.map (fun ω => V ω i) = gaussianReal 0 (varianceParameter b)
  jointGaussian : μ.map (fun ω i => V ω i) =
    Measure.pi (fun _ : Fin 3 => gaussianReal 0 (varianceParameter b))
  velocityMGF : ∀ t : Fin 3 → ℝ,
    mgf (fun ω => ∑ i, t i * V ω i) μ 1 = exp ((sigma b)^2 * (∑ i, (t i)^2)/2)
  velocityMGFFinite : ∀ t : Fin 3 → ℝ,
    Integrable (fun ω => exp (∑ i, t i * V ω i)) μ
  squareDefinition : ∀ i ω, squares b V i ω = (V ω i / sigma b)^2
  squaresIndependent : iIndepFun (squares b V) μ
  squareMGF : ∀ i t, t < 1/2 → mgf (squares b V i) μ t = (1-2*t)^(-(1:ℝ)/2)
  squareMGFFinite : ∀ i t, t < 1/2 → Integrable (fun ω => exp (t*squares b V i ω)) μ
  squareLaw : ∀ i, μ.map (squares b V i) = gammaMeasure (1/2) (1/2)
  sumMGF : ∀ t, t < 1/2 → mgf (sumSquares b V) μ t = (1-2*t)^(-(3:ℝ)/2)
  sumMGFFinite : ∀ t, t < 1/2 → Integrable (fun ω => exp (t*sumSquares b V ω)) μ
  sumLaw : μ.map (sumSquares b V) = gammaMeasure (3/2) (1/2)
  speedTransform : ∀ ω, ‖V ω‖ = sigma b * sqrt (sumSquares b V ω)
  gammaSpeedLaw : (gammaMeasure (3/2) (1/2)).map (fun s => sigma b * sqrt s) = speedLaw b
  speedLaw : μ.map (fun ω => ‖V ω‖) = MaxwellDemo.speedLaw b
  speedDensity : ∀ r, MaxwellDemo.speedDensity b r = if 0 ≤ r then
    sqrt (2/π) * r^2 * (sigma b)⁻¹^3 * exp (-r^2/(2*(sigma b)^2)) else 0
  speedDensityLaw : μ.map (fun ω => ‖V ω‖) = volume.withDensity
    (fun r => ENNReal.ofReal (MaxwellDemo.speedDensity b r))
  normalized : ∫ r : ℝ, MaxwellDemo.speedDensity b r = 1
```

`μ.map X` denotes the actual law of `X`; `volume.withDensity` specifies a
Lebesgue density. These statements identify probability measures, including
normalization, rather than only proposing a density formula.

## Where the definitions are

| Name | Definition and meaning |
|---|---|
| `MaxwellDemo.Velocity` | [Core.lean:108](MaxwellMGF/Core.lean#L108): `EuclideanSpace ℝ (Fin 3)`. |
| `MaxwellDemo.SmoothModel` | [Core.lean:15–22](MaxwellMGF/Core.lean#L15-L22): model functions, isotropy, regularity, and normalization. |
| `MaxwellDemo.modelVelocityLaw` | [Core.lean:218–219](MaxwellMGF/Core.lean#L218-L219): the assumed product-density measure. |
| `MaxwellDemo.amplitude`, `componentDensity` | [Core.lean:82–84](MaxwellMGF/Core.lean#L82-L84): normalized Gaussian density in the parameter `b`. |
| `MaxwellMGF.varianceParameter` | [Distributions.lean:12](MaxwellMGF/Distributions.lean#L12): `(1/(2*b)).toNNReal`. |
| `MaxwellMGF.sigma` | [Speed.lean:9](MaxwellMGF/Speed.lean#L9): `sqrt (1/(2*b))`. |
| `MaxwellMGF.squares`, `sumSquares` | [Distributions.lean:111–112](MaxwellMGF/Distributions.lean#L111-L112): `2*b*(V ω i)^2` and their sum; `squareDefinition` proves the standardized-square identity. |
| `MaxwellDemo.speedDensity` | [Core.lean:110](MaxwellMGF/Core.lean#L110): the Maxwell density, zero for negative speeds. |
| `MaxwellDemo.speedLaw` | [Core.lean:162–163](MaxwellMGF/Core.lean#L162-L163): its measure on the positive half-line; `speedDensityLaw` proves the whole-line density equality. |
| `MaxwellMGF.Conclusions` | [Project.lean:13–40](MaxwellMGF/Project.lean#L13-L40): every field returned by the endpoint. |

The following are existing mathlib definitions, at the pinned revision
`641fbd329d4ffb62bef83c51f54088469056bd36`:

| Name | Definition |
|---|---|
| `ProbabilityTheory.gaussianReal` | [Gaussian/Real.lean:222](https://github.com/leanprover-community/mathlib4/blob/641fbd329d4ffb62bef83c51f54088469056bd36/Mathlib/Probability/Distributions/Gaussian/Real.lean#L222): Gaussian probability measure, parameterized by mean and variance. |
| `ProbabilityTheory.gammaMeasure` | [Gamma.lean:128](https://github.com/leanprover-community/mathlib4/blob/641fbd329d4ffb62bef83c51f54088469056bd36/Mathlib/Probability/Distributions/Gamma.lean#L128): Gamma measure with shape and rate. |
| `ProbabilityTheory.mgf` | [Moments/Basic.lean:121](https://github.com/leanprover-community/mathlib4/blob/641fbd329d4ffb62bef83c51f54088469056bd36/Mathlib/Probability/Moments/Basic.lean#L121): the integral of `exp (t * X)`. |
| `ProbabilityTheory.iIndepFun` | [Independence/Basic.lean:136](https://github.com/leanprover-community/mathlib4/blob/641fbd329d4ffb62bef83c51f54088469056bd36/Mathlib/Probability/Independence/Basic.lean#L136): mutual independence of a family of random variables. |

## External axioms and audit

The three additional global axioms are declared in namespace
`MaxwellMGF.Background`:

| Axiom | Exact declaration | Use |
|---|---|---|
| A1: `product_density` | [Background.lean:13–20](MaxwellMGF/Background.lean#L13-L20) | Gives independence and marginal laws from the assumed product density. |
| A2: `gamma_mgf` | [Background.lean:25–27](MaxwellMGF/Background.lean#L25-L27) | Supplies the comparison Gamma MGF and its integrability. |
| A3: `mgf_unique` | [Background.lean:32–37](MaxwellMGF/Background.lean#L32-L37) | Identifies laws from finite, equal MGFs near zero. |

[ASSUMPTIONS.md](ASSUMPTIONS.md) gives the full hypotheses and references for
these inputs. They are assumed background theorems, not proofs completed here.
They do not postulate the Maxwell characterization or the three-square law.
Physical model assumptions remain separate theorem hypotheses.

`#print axioms MaxwellMGF.maxwell_mgf_project` reports:

```text
'MaxwellMGF.maxwell_mgf_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 MaxwellMGF.Background.gamma_mgf,
 MaxwellMGF.Background.mgf_unique,
 MaxwellMGF.Background.product_density]
```

The first three are Lean's standard logical foundations. The other three are
the project's additional mathematical axioms. The audit of
`MaxwellDemo.maxwell_characterization` and `MaxwellDemo.speed_pushforward`
lists only standard foundations.

Run `lake env lean AxiomAudit.lean` to print the endpoint, definitions, and all
48 theorem dependency audits. The recorded output is in
[verification/axioms.log](verification/axioms.log).
