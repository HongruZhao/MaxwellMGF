import MaxwellMGF.Speed

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
namespace MaxwellMGF
open MaxwellDemo

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The full result advertised in the report. Every law is a measure equality.
The three named textbook axioms are printed by AxiomAudit.lean. -/
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

/-- Conditional Maxwell--MGF theorem. No Gaussian shape is a hypothesis. -/
theorem maxwell_mgf_project {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : Ω → Velocity) (hV : Measurable V) (M : SmoothModel)
    (physicalModel : μ.map V = modelVelocityLaw M) :
    ∃ b : ℝ, Conclusions μ V b := by
  obtain ⟨b, hb, hind, hmarg, hjoint⟩ := derived_components V hV M physicalModel
  have hspeed : μ.map (fun ω => ‖V ω‖) = MaxwellDemo.speedLaw b := by
    change μ.map ((fun v : Velocity => ‖v‖) ∘ V) = _
    rw [← Measure.map_map measurable_norm hV, hjoint, speed_pushforward hb]
  refine ⟨b, {
    positive := hb
    sigmaPositive := sigma_pos hb
    variance := by rw [variance_coe hb, sigma_sq hb]
    independent := hind
    componentGaussian := fun i => by rw [hmarg i, component_gaussian hb]
    jointGaussian := joint_gaussian V hV hb hind hmarg
    velocityMGF := fun t => by rw [joint_mgf V hV hb hind hmarg, sigma_sq hb]
    velocityMGFFinite := ?_
    squareDefinition := fun i ω => (standardized_square hb (V ω i)).symm
    squaresIndependent := squares_independent V hind
    squareMGF := fun i t ht => square_mgf hb ht (by fun_prop) (hmarg i)
    squareMGFFinite := fun i t ht => square_integrable hb ht (by fun_prop) (hmarg i)
    squareLaw := fun i => square_law hb (by fun_prop) (hmarg i)
    sumMGF := fun t ht => sum_mgf V hV hb ht hind hmarg
    sumMGFFinite := fun t ht => sum_integrable V hV hb ht hind hmarg
    sumLaw := sum_law V hV hb hind hmarg
    speedTransform := speed_transform V hb
    gammaSpeedLaw := gamma_speed_pushforward V hV hb hind hmarg hjoint
    speedLaw := hspeed
    speedDensity := speed_density_sigma hb
    speedDensityLaw := by rw [hspeed, speedLaw_full_density]
    normalized := speed_density_integral hb }⟩
  intro t
  have hp : 0 < mgf (fun ω => ∑ i, t i * V ω i) μ 1 := by
    rw [joint_mgf V hV hb hind hmarg]
    exact exp_pos _
  simpa only [one_mul] using mgf_pos_iff.mp hp

end MaxwellMGF
