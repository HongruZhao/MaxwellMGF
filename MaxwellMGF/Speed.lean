import MaxwellMGF.Distributions

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
namespace MaxwellMGF
open MaxwellDemo

def sigma (b : ℝ) : ℝ := sqrt (1/(2*b))

theorem sigma_pos {b : ℝ} (hb : 0 < b) : 0 < sigma b := by
  unfold sigma; positivity

theorem sigma_sq {b : ℝ} (hb : 0 < b) : (sigma b)^2 = 1/(2*b) := by
  unfold sigma
  exact sq_sqrt (by positivity)

theorem b_sigma {b : ℝ} (hb : 0 < b) : b = 1/(2*(sigma b)^2) := by
  rw [sigma_sq hb]
  field_simp

theorem standardized_square {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (x/sigma b)^2 = 2*b*x^2 := by
  rw [div_pow, sigma_sq hb]
  field_simp

theorem norm_sumSquares {Ω : Type*} [MeasurableSpace Ω] (V : Ω → Velocity) (b : ℝ) (ω : Ω) :
    sumSquares b V ω = 2*b*‖V ω‖^2 := by
  simp [sumSquares, squares, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  ring

theorem speed_transform {Ω : Type*} [MeasurableSpace Ω] (V : Ω → Velocity)
    {b : ℝ} (hb : 0 < b) (ω : Ω) : ‖V ω‖ = sigma b * sqrt (sumSquares b V ω) := by
  rw [norm_sumSquares, sqrt_mul (by positivity : 0 ≤ 2*b), sqrt_sq (norm_nonneg _)]
  have hs : sigma b * sqrt (2*b) = 1 := by
    rw [sigma, ← sqrt_mul (by positivity : 0 ≤ 1/(2*b))]
    have hh : 1/(2*b)*(2*b) = 1 := by field_simp
    rw [hh, sqrt_one]
  rw [← mul_assoc, hs, one_mul]

theorem speed_density_sigma {b : ℝ} (hb : 0 < b) (r : ℝ) :
    speedDensity b r = if 0 ≤ r then
      sqrt (2/π) * r^2 * (sigma b)⁻¹^3 * exp (-r^2/(2*(sigma b)^2)) else 0 := by
  have hs := sigma_pos hb
  have hpi := pi_pos
  have hroot := sq_sqrt (show 0 ≤ 2*π by positivity)
  have hrootpos : 0 < sqrt (2*π) := by positivity
  have hr : sqrt (2/π) = sqrt (2*π)/π := by
    rw [show (2:ℝ)/π = (2*π)/(π^2) by field_simp,
      sqrt_div (by positivity : 0 ≤ 2*π), sqrt_sq hpi.le]
  have hA : amplitude b = (sqrt (2*π)*sigma b)⁻¹ := by
    unfold amplitude
    congr 1
    conv_lhs => rw [b_sigma hb]
    have hh : π/(1/(2*sigma b^2)) = (2*π)*sigma b^2 := by field_simp
    rw [hh, sqrt_mul (by positivity : 0 ≤ 2*π), sqrt_sq hs.le]
  have hcoef : 4*π*amplitude b^3 = sqrt (2/π) * (sigma b)⁻¹^3 := by
    rw [hA, hr]
    field_simp
    nlinarith [congrArg (fun x : ℝ => x^2) (sq_sqrt (show 0 ≤ π*2 by positivity))]
  unfold speedDensity
  split_ifs with h
  · have hexp : -b*r^2 = -r^2/(2*sigma b^2) := by
      conv_lhs => rw [b_sigma hb]
      ring
    rw [hexp, hcoef]
    ring
  · rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem speedLaw_full_density (b : ℝ) :
    speedLaw b = volume.withDensity (fun r => ENNReal.ofReal (speedDensity b r)) := by
  rw [speedLaw, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext r
  by_cases h : 0 < r
  · simp [h]
  · by_cases h0 : r = 0
    · subst r; simp [speedDensity]
    · have hr : r < 0 := lt_of_le_of_ne (le_of_not_gt h) h0
      simp [h, speedDensity, not_le.mpr hr]

theorem speed_density_integral {b : ℝ} (hb : 0 < b) : ∫ r : ℝ, speedDensity b r = 1 := by
  have heq : speedDensity b = (Ioi (0:ℝ)).indicator (speedDensity b) := by
    funext r
    by_cases h : 0 < r
    · simp [h]
    · by_cases h0 : r = 0
      · subst r; simp [speedDensity]
      · have hr : r < 0 := lt_of_le_of_ne (le_of_not_gt h) h0
        simp [h, speedDensity, not_le.mpr hr]
  calc
    _ = ∫ r : ℝ, (Ioi (0:ℝ)).indicator (speedDensity b) r := congrArg (fun f : ℝ → ℝ => ∫ r, f r) heq
    _ = ∫ r in Ioi (0:ℝ), speedDensity b r := integral_indicator measurableSet_Ioi
    _ = 1 := speed_normalized hb

/-- The chi-square-to-speed change of variables is an actual measure equality. -/
theorem gamma_speed_pushforward (V : Ω → Velocity) (hV : Measurable V) {b : ℝ} (hb : 0 < b)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b)
    (hjoint : μ.map V = velocityLaw b) :
    (gammaMeasure (3/2) (1/2)).map (fun s => sigma b * sqrt s) = speedLaw b := by
  rw [← sum_law V hV hb hind hmarg, Measure.map_map (by fun_prop) (by unfold sumSquares squares; fun_prop)]
  have heq : (fun s => sigma b*sqrt s) ∘ sumSquares b V = fun ω => ‖V ω‖ :=
    funext fun ω => (speed_transform V hb ω).symm
  rw [heq]
  change μ.map ((fun v : Velocity => ‖v‖) ∘ V) = _
  rw [← Measure.map_map measurable_norm hV, hjoint, speed_pushforward hb]

end MaxwellMGF
