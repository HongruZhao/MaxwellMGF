import MaxwellMGF.Core

/-! Explicit textbook inputs permitted by the course rubric. None is a Maxwell
characterization, a three-component chi-square conclusion, or a speed-law conclusion.
The exact statements and references are recorded in ASSUMPTIONS.md. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace MaxwellMGF.Background

/-- General density-factorization criterion, in arbitrary finite dimension.
Reference: Taboga, Independent random variables, continuous variables and
mutual independence; the marginal statement follows by Tonelli. -/
axiom product_density {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (V : Ω → EuclideanSpace ℝ (Fin n))
    (hV : Measurable V) (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hi : Integrable f) (hm : ∫ x, f x = 1)
    (hlaw : μ.map V = volume.withDensity
      (fun v => ENNReal.ofReal (∏ i : Fin n, f (v i)))) :
    iIndepFun (fun i ω => V ω i) μ ∧
      ∀ i, μ.map (fun ω => V ω i) = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- Gamma Laplace integral, shape a and RATE r (not scale).
Reference: Siegrist, The Gamma Distribution, General Gamma Distribution, Moments.
This generic input is used at a=1/2 and a=3/2, r=1/2. -/
axiom gamma_mgf (a r t : ℝ) (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x : ℝ => exp (t*x)) (gammaMeasure a r) ∧
      mgf id (gammaMeasure a r) t = (1-t/r) ^ (-a)

/-- MGF uniqueness with an explicit common open neighborhood and finiteness.
Reference: Taboga, Moment generating function, Characterization of a distribution.
This input applies to arbitrary real random variables and target probabilities. -/
axiom mgf_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (hμ : ∀ t : ℝ, |t| < ε → Integrable (fun ω => exp (t*X ω)) μ)
    (hν : ∀ t : ℝ, |t| < ε → Integrable (fun x : ℝ => exp (t*x)) ν)
    (heq : ∀ t : ℝ, |t| < ε → mgf X μ t = mgf id ν t) : μ.map X = ν

end MaxwellMGF.Background
