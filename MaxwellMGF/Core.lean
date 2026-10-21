import Mathlib

/-!
STAT 4052: a smooth, conditional reconstruction of Maxwell (1860), Proposition IV.
Adapted from the existing local MaxwellDemo by Hongru Zhao with Codex assistance.
Physical hypotheses are explicit parameters. This core module declares no new axioms.
-/
noncomputable section
open MeasureTheory Set Real

namespace MaxwellDemo

/-- Log-density formulation of positive independent, identically distributed components
and a differentiable radial log-density. Normalization is not assumed here. -/
structure SmoothModel where
  g : ℝ → ℝ
  H : ℝ → ℝ
  dg : Differentiable ℝ g
  dH : Differentiable ℝ H
  radial : ∀ x y z : ℝ, g x + g y + g z = H (x^2 + y^2 + z^2)
  integrable : Integrable (fun x => exp (g x))
  normalized : ∫ x : ℝ, exp (g x) = 1

/-- Differentiate the radial equation in its first coordinate. -/
theorem derivative_radial (M : SmoothModel) (x y z : ℝ) :
    deriv M.g x = deriv M.H (x^2 + y^2 + z^2) * (2*x) := by
  have hleft := ((M.dg x).hasDerivAt.add_const (M.g y)).add_const (M.g z)
  have hinner := (((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (z^2)
  have hright := (M.dH (x^2 + y^2 + z^2)).hasDerivAt.comp x hinner
  have heq : (fun t : ℝ => M.g t + M.g y + M.g z) =
      (fun t => M.H (t^2 + y^2 + z^2)) := funext fun t => M.radial t y z
  rw [heq] at hleft
  have := hleft.unique hright
  simpa using this

/-- Isotropy also allows us to differentiate in the second coordinate. -/
theorem derivative_linear (M : SmoothModel) (x : ℝ) :
    deriv M.g x = x * deriv M.g 1 := by
  have hx := derivative_radial M x 1 0
  have h1 := derivative_radial M 1 x 0
  have hswap : (1:ℝ)^2 + x^2 + 0^2 = x^2 + 1^2 + 0^2 := by ring
  rw [hswap] at h1
  rw [hx, h1]
  ring

/-- A zero-derivative argument integrates the linear log-derivative. -/
theorem log_quadratic (M : SmoothModel) (x : ℝ) :
    M.g x = M.g 0 + (deriv M.g 1 / 2) * x^2 := by
  let F : ℝ → ℝ := fun t => M.g t - (deriv M.g 1 / 2) * t^2
  have hF (t : ℝ) : HasDerivAt F 0 t := by
    have h := (M.dg t).hasDerivAt.sub (((hasDerivAt_id t).pow 2).const_mul (deriv M.g 1 / 2))
    have hh : HasDerivAt F (deriv M.g t - (deriv M.g 1 / 2) * (2*t)) t := by
      convert! h using 1
      simp
    
    have hd : deriv M.g t - (deriv M.g 1 / 2) * (2*t) = 0 := by
      rw [derivative_linear M t]
      ring
    rwa [hd] at hh
  have hc := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
    (fun t => (hF t).deriv) x 0
  dsimp [F] at hc
  simpa using (sub_eq_iff_eq_add.mp hc)

/-- Integrability forces the quadratic coefficient to be negative. -/
theorem decay_positive (M : SmoothModel) : 0 < -(deriv M.g 1 / 2) := by
  by_contra hn
  have hc : 0 ≤ deriv M.g 1 / 2 := by linarith
  have hdom : Integrable (fun _ : ℝ => exp (M.g 0)) := by
    apply M.integrable.mono' stronglyMeasurable_const.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    rw [log_quadratic M x]
    nlinarith [sq_nonneg x]
  rcases integrable_const_iff.mp hdom with hz | hf
  · exact (exp_ne_zero _) hz
  · have := hf.measure_univ_lt_top
    simp at this

/-- Normalizing factor for exp(-b*x^2). -/
def amplitude (b : ℝ) : ℝ := (sqrt (π / b))⁻¹

def componentDensity (b x : ℝ) : ℝ := amplitude b * exp (-b*x^2)

/-- Conditional Maxwell characterization: the Gaussian is derived, not assumed. -/
theorem maxwell_characterization (M : SmoothModel) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, exp (M.g x) = componentDensity b x := by
  let b := -(deriv M.g 1 / 2)
  have hb : 0 < b := decay_positive M
  have hshape (x : ℝ) : exp (M.g x) = exp (M.g 0) * exp (-b*x^2) := by
    rw [log_quadratic M x, exp_add]
    congr 2
    dsimp [b]
    ring
  have hnorm : exp (M.g 0) * sqrt (π / b) = 1 := by
    have hh := M.normalized
    rw [show (fun x => exp (M.g x)) =
      (fun x => exp (M.g 0) * exp (-b*x^2)) from funext hshape] at hh
    rwa [integral_const_mul, integral_gaussian] at hh
  have hs : sqrt (π / b) ≠ 0 := ne_of_gt (sqrt_pos.2 (div_pos pi_pos hb))
  have hA : exp (M.g 0) = amplitude b := by
    dsimp [amplitude]
    simpa [one_div] using ((eq_div_iff hs).2 hnorm : exp (M.g 0) = 1 / sqrt (π / b))
  exact ⟨b, hb, fun x => by rw [hshape, hA]; rfl⟩


abbrev Velocity := EuclideanSpace ℝ (Fin 3)
def velocityDensity (b : ℝ) (v : Velocity) : ℝ := amplitude b ^ 3 * exp (-b * ‖v‖^2)
def speedDensity (b r : ℝ) : ℝ := if 0 ≤ r then 4*π*amplitude b^3*r^2*exp (-b*r^2) else 0

theorem radial_integral (F : ℝ → ℝ) :
    (∫ v : Velocity, F ‖v‖) = 4*π * ∫ r in Ioi (0:ℝ), r^2 * F r := by
  have h := integral_fun_norm_addHaar (volume : Measure Velocity) F
  have hv : (volume : Measure Velocity).real (Metric.ball 0 1) = π*4/3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three, show 0 ≤ π*4/3 by positivity]
  simp only [hv, show Module.finrank ℝ Velocity = 3 by simp, smul_eq_mul] at h
  convert h using 1
  norm_num
  ring

theorem velocity_normalized {b : ℝ} (hb : 0 < b) : ∫ v : Velocity, velocityDensity b v = 1 := by
  simp only [velocityDensity]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  have hp : 0 < π/b := div_pos pi_pos hb
  have hs : sqrt (π/b) ≠ 0 := ne_of_gt (sqrt_pos.2 hp)
  have hr : (π/b)^((3:ℝ)/2) = sqrt (π/b)^3 := by
    rw [sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    norm_num
  simp only [show Module.finrank ℝ Velocity = 3 by simp, Nat.cast_ofNat]
  rw [hr, amplitude, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hs)]

theorem speed_test_function (b : ℝ) (ψ : ℝ → ℝ) :
    (∫ v : Velocity, ψ ‖v‖ * velocityDensity b v) =
      ∫ r in Ioi (0:ℝ), ψ r * speedDensity b r := by
  change (∫ v : Velocity, (fun r => ψ r * (amplitude b^3 * exp (-b*r^2))) ‖v‖) = _
  rw [radial_integral (fun r => ψ r * (amplitude b^3 * exp (-b*r^2))), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [speedDensity, if_pos (le_of_lt (show 0 < r from hr))]
  ring


/-- Both functions are nonnegative; positivity of b is required for normalization. -/
theorem velocity_nonneg (b : ℝ) (v : Velocity) : 0 ≤ velocityDensity b v := by
  unfold velocityDensity amplitude
  positivity

theorem speed_nonneg (b r : ℝ) : 0 ≤ speedDensity b r := by
  unfold speedDensity amplitude
  split_ifs <;> positivity

theorem speed_normalized {b : ℝ} (hb : 0 < b) :
    ∫ r in Ioi (0:ℝ), speedDensity b r = 1 := by
  have h := speed_test_function b (fun _ => 1)
  simpa only [one_mul, velocity_normalized hb] using h.symm

def velocityLaw (b : ℝ) : Measure Velocity :=
  volume.withDensity (fun v => ENNReal.ofReal (velocityDensity b v))

def speedLaw (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (speedDensity b r))

/-- The mass of a measurable set under an integrable nonnegative density. -/
theorem density_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x)
    (s : Set α) (hs : MeasurableSet s) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) s =
      ENNReal.ofReal (∫ x, s.indicator f x ∂μ) := by
  rw [withDensity_apply _ hs, integral_indicator hs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hn)).symm

/-- Full measure-level statement: the norm of the velocity has Maxwell's speed law. -/
theorem speed_pushforward {b : ℝ} (hb : 0 < b) :
    Measure.map (fun v : Velocity => ‖v‖) (velocityLaw b) = speedLaw b := by
  have hv := integrable_of_integral_eq_one (velocity_normalized hb)
  have hq := integrable_of_integral_eq_one (speed_normalized hb)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_norm hs]
  change volume.withDensity (fun v => ENNReal.ofReal (velocityDensity b v))
      ((fun v : Velocity => ‖v‖) ⁻¹' s) =
    (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (speedDensity b r)) s
  rw [density_mass volume _ hv (velocity_nonneg b) _ (hs.preimage measurable_norm),
    density_mass (volume.restrict (Ioi 0)) _ hq (speed_nonneg b) s hs]
  congr 1
  calc
    _ = ∫ v : Velocity, (s.indicator (fun _ => (1:ℝ))) ‖v‖ * velocityDensity b v := by
      apply integral_congr_ae
      filter_upwards with v
      by_cases h : ‖v‖ ∈ s <;> simp [h]
    _ = ∫ r in Ioi (0:ℝ), (s.indicator (fun _ => (1:ℝ))) r * speedDensity b r :=
      speed_test_function b _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases h : r ∈ s <;> simp [h]

theorem velocity_isProbability {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (velocityLaw b) where
  measure_univ := by
    rw [velocityLaw, density_mass volume _ (integrable_of_integral_eq_one (velocity_normalized hb))
      (velocity_nonneg b) univ MeasurableSet.univ]
    simp [velocity_normalized hb]

/-- The coordinate product agrees with the radial Gaussian density. -/
theorem component_product (b : ℝ) (v : Velocity) :
    componentDensity b (v 0) * componentDensity b (v 1) * componentDensity b (v 2) =
      velocityDensity b v := by
  have hn : ‖v‖^2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  unfold componentDensity velocityDensity
  rw [hn]
  rw [show -b * ((v 0)^2 + (v 1)^2 + (v 2)^2) =
    (-b*(v 0)^2 + -b*(v 1)^2) + -b*(v 2)^2 by ring, exp_add, exp_add]
  ring

def modelVelocityLaw (M : SmoothModel) : Measure Velocity :=
  volume.withDensity (fun v => ENNReal.ofReal (exp (M.g (v 0)) * exp (M.g (v 1)) * exp (M.g (v 2))))

/-- The physical law is a hypothesis about a selected particle, not a global axiom. -/
theorem particle_speed_distribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → Velocity) (hV : Measurable V) (M : SmoothModel)
    (physical_model : Measure.map V μ = modelVelocityLaw M) :
    ∃ b : ℝ, 0 < b ∧ Measure.map (fun ω => ‖V ω‖) μ = speedLaw b := by
  obtain ⟨b, hb, hf⟩ := maxwell_characterization M
  have hmodel : modelVelocityLaw M = velocityLaw b := by
    unfold modelVelocityLaw velocityLaw
    congr 1
    funext v
    rw [hf, hf, hf, component_product]
  refine ⟨b, hb, ?_⟩
  change Measure.map ((fun v : Velocity => ‖v‖) ∘ V) μ = speedLaw b
  rw [← Measure.map_map measurable_norm hV, physical_model, hmodel, speed_pushforward hb]


/-- One-dimensional Gaussian normalization. -/
theorem component_normalized {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, componentDensity b x = 1 := by
  simp only [componentDensity]
  rw [integral_const_mul, integral_gaussian, amplitude, inv_mul_cancel₀]
  exact ne_of_gt (sqrt_pos.2 (div_pos pi_pos hb))

theorem amplitude_standard {b : ℝ} (hb : 0 < b) : amplitude b = sqrt (b/π) := by
  rw [amplitude, sqrt_div pi_pos.le, inv_div, sqrt_div hb.le]

theorem speed_isProbability {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (speedLaw b) where
  measure_univ := by
    rw [speedLaw, density_mass (volume.restrict (Ioi 0)) _
      (integrable_of_integral_eq_one (speed_normalized hb)) (speed_nonneg b) univ MeasurableSet.univ]
    simp [speed_normalized hb]

/-- Expected finite population counts need equal marginals, not mutual independence. -/
theorem expected_count {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (events : Fin N → Set Ω)
    (he : ∀ i, MeasurableSet (events i)) (p : ℝ)
    (hp : ∀ i, μ.real (events i) = p) :
    (∫ ω, ∑ i : Fin N, (events i).indicator (fun _ => (1:ℝ)) ω ∂μ) = N*p := by
  rw [integral_finsetSum _ (fun i _ => (integrable_const (1:ℝ)).indicator (he i))]
  simp [he, hp]


/-- A concrete witness confirms that the mathematical model is nonempty. -/
theorem exp_log_amplitude {b : ℝ} (hb : 0 < b) (x : ℝ) :
    exp (log (amplitude b) - b*x^2) = componentDensity b x := by
  have ha : 0 < amplitude b := by unfold amplitude; positivity
  rw [sub_eq_add_neg, exp_add, exp_log ha]
  simp [componentDensity, neg_mul]

def gaussianModel (b : ℝ) (hb : 0 < b) : SmoothModel where
  g := fun x => log (amplitude b) - b*x^2
  H := fun s => 3*log (amplitude b) - b*s
  dg := by fun_prop
  dH := by fun_prop
  radial := by intro x y z; ring
  integrable := by
    simpa only [exp_log_amplitude hb] using
      (integrable_of_integral_eq_one (component_normalized hb))
  normalized := by
    simpa only [exp_log_amplitude hb] using component_normalized hb

theorem model_nonempty : Nonempty SmoothModel := ⟨gaussianModel 1 (by norm_num)⟩

end MaxwellDemo
