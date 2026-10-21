import MaxwellMGF.Background

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
namespace MaxwellMGF
open MaxwellDemo

def componentLaw (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (componentDensity b x))

def varianceParameter (b : ℝ) : ℝ≥0 := (1/(2*b)).toNNReal

theorem variance_coe {b : ℝ} (hb : 0 < b) :
    (varianceParameter b : ℝ) = 1/(2*b) := by
  unfold varianceParameter
  exact Real.coe_toNNReal _ (by positivity)

theorem component_gaussian {b : ℝ} (hb : 0 < b) :
    componentLaw b = gaussianReal 0 (varianceParameter b) := by
  have hv : varianceParameter b ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast (show 0 < (varianceParameter b : ℝ) by rw [variance_coe hb]; positivity)
  rw [gaussianReal_of_var_ne_zero _ hv]
  unfold componentLaw
  congr 1
  funext x
  unfold gaussianPDF
  congr 1
  unfold componentDensity amplitude gaussianPDFReal
  rw [variance_coe hb]
  have hden : 2 * π * (1/(2*b)) = π/b := by field_simp
  have hexp : -(x-0)^2 / (2*(1/(2*b))) = -b*x^2 := by field_simp; ring
  rw [hden, hexp]

theorem quadratic_mgf {b t : ℝ} (hb : 0 < b) (ht : t < 1/2) :
    mgf (fun x : ℝ => 2*b*x^2) (componentLaw b) t = (1-2*t)^(-(1:ℝ)/2) := by
  have hd : 0 < 1-2*t := by linarith
  have hmeas : Measurable (fun x => ENNReal.ofReal (componentDensity b x)) := by
    unfold componentDensity; fun_prop
  unfold mgf componentLaw
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (by simp)]
  simp only [smul_eq_mul]
  have hf : (fun x : ℝ => (ENNReal.ofReal (componentDensity b x)).toReal * exp (t*(2*b*x^2))) =
      fun x => amplitude b * exp (-(b*(1-2*t))*x^2) := by
    funext x
    rw [ENNReal.toReal_ofReal (by unfold componentDensity amplitude; positivity)]
    unfold componentDensity
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hf, integral_const_mul, integral_gaussian]
  rw [amplitude, show π/(b*(1-2*t)) = (π/b)/(1-2*t) by rw [div_div],
    sqrt_div (by positivity : 0 ≤ π/b)]
  have hs : sqrt (π/b) ≠ 0 := ne_of_gt (sqrt_pos.2 (by positivity))
  have halg : (sqrt (π/b))⁻¹ * (sqrt (π/b) / sqrt (1-2*t)) = (sqrt (1-2*t))⁻¹ := by
    field_simp
  rw [halg, sqrt_eq_rpow, ← rpow_neg hd.le]
  congr 1
  ring

theorem quadratic_integrable {b t : ℝ} (hb : 0 < b) (ht : t < 1/2) :
    Integrable (fun x : ℝ => exp (t*(2*b*x^2))) (componentLaw b) := by
  have hd : 0 < b*(1-2*t) := mul_pos hb (by linarith)
  unfold componentLaw
  rw [integrable_withDensity_iff_integrable_smul' (by unfold componentDensity; fun_prop) (by simp)]
  have hf : (fun x : ℝ => (ENNReal.ofReal (componentDensity b x)).toReal • exp (t*(2*b*x^2))) =
      fun x => amplitude b * exp (-(b*(1-2*t))*x^2) := by
    funext x
    rw [ENNReal.toReal_ofReal (by unfold componentDensity amplitude; positivity)]
    simp only [smul_eq_mul, componentDensity, mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hf]
  exact (integrable_exp_neg_mul_sq hd).const_mul _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem square_mgf {b t : ℝ} (hb : 0 < b) (ht : t < 1/2)
    {X : Ω → ℝ} (hX : Measurable X) (hlaw : μ.map X = componentLaw b) :
    mgf (fun ω => 2*b*(X ω)^2) μ t = (1-2*t)^(-(1:ℝ)/2) := by
  have hh := mgf_map (μ := μ) (X := fun x : ℝ => 2*b*x^2) (t := t) hX.aemeasurable (by fun_prop)
  rw [hlaw, quadratic_mgf hb ht] at hh
  exact hh.symm

omit [IsProbabilityMeasure μ] in
theorem square_integrable {b t : ℝ} (hb : 0 < b) (ht : t < 1/2)
    {X : Ω → ℝ} (hX : Measurable X) (hlaw : μ.map X = componentLaw b) :
    Integrable (fun ω => exp (t*(2*b*(X ω)^2))) μ := by
  have hh : Integrable (fun x : ℝ => exp (t*(2*b*x^2))) (μ.map X) := by
    rw [hlaw]; exact quadratic_integrable hb ht
  exact (integrable_map_measure (by fun_prop) hX.aemeasurable).mp hh

theorem square_law {b : ℝ} (hb : 0 < b) {X : Ω → ℝ}
    (hX : Measurable X) (hlaw : μ.map X = componentLaw b) :
    μ.map (fun ω => 2*b*(X ω)^2) = gammaMeasure (1/2) (1/2) := by
  haveI := isProbabilityMeasure_gammaMeasure (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  apply Background.mgf_unique μ _ (by fun_prop) _ (1/4) (by norm_num)
  · intro t ht
    exact square_integrable hb (by have := (abs_lt.mp ht).2; linarith) hX hlaw
  · intro t ht
    exact (Background.gamma_mgf (1/2) (1/2) t (by norm_num) (by norm_num)
      (by have := (abs_lt.mp ht).2; linarith)).1
  · intro t ht
    rw [square_mgf hb (by have := (abs_lt.mp ht).2; linarith) hX hlaw,
      (Background.gamma_mgf (1/2) (1/2) t (by norm_num) (by norm_num)
        (by have := (abs_lt.mp ht).2; linarith)).2]
    congr 1 <;> ring

def squares (b : ℝ) (V : Ω → Velocity) (i : Fin 3) (ω : Ω) : ℝ := 2*b*(V ω i)^2
def sumSquares (b : ℝ) (V : Ω → Velocity) (ω : Ω) : ℝ := ∑ i, squares b V i ω

theorem model_facts (V : Ω → Velocity) (hV : Measurable V) (M : SmoothModel)
    (hmodel : μ.map V = modelVelocityLaw M) :
    iIndepFun (fun i ω => V ω i) μ ∧
      ∀ i, μ.map (fun ω => V ω i) =
        volume.withDensity (fun x => ENNReal.ofReal (exp (M.g x))) := by
  apply Background.product_density μ 3 V hV (fun x => exp (M.g x))
    (M.dg.continuous.measurable.exp) (fun x => (exp_pos _).le) M.integrable M.normalized
  simpa [modelVelocityLaw, Fin.prod_univ_three] using hmodel

theorem derived_components (V : Ω → Velocity) (hV : Measurable V) (M : SmoothModel)
    (hmodel : μ.map V = modelVelocityLaw M) :
    ∃ b : ℝ, 0 < b ∧ iIndepFun (fun i ω => V ω i) μ ∧
      (∀ i, μ.map (fun ω => V ω i) = componentLaw b) ∧ μ.map V = velocityLaw b := by
  obtain ⟨b, hb, hf⟩ := maxwell_characterization M
  obtain ⟨hind, hmarg⟩ := model_facts V hV M hmodel
  refine ⟨b, hb, hind, ?_, ?_⟩
  · intro i
    rw [hmarg i]
    simp only [hf, componentLaw]
  · rw [hmodel]
    unfold modelVelocityLaw velocityLaw
    congr 1
    funext v
    rw [hf, hf, hf, component_product]

omit [IsProbabilityMeasure μ] in
theorem joint_gaussian (V : Ω → Velocity) (hV : Measurable V) {b : ℝ} (hb : 0 < b)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b) :
    μ.map (fun ω i => V ω i) = Measure.pi (fun _ : Fin 3 => gaussianReal 0 (varianceParameter b)) := by
  rw [hind.map_fun_eq_pi_map (fun i => by fun_prop)]
  congr 1
  funext i
  rw [hmarg i, component_gaussian hb]

omit [IsProbabilityMeasure μ] in
theorem joint_mgf (V : Ω → Velocity) (hV : Measurable V) {b : ℝ} (hb : 0 < b)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b) (t : Fin 3 → ℝ) :
    mgf (fun ω => ∑ i, t i * V ω i) μ 1 = exp ((1/(2*b)) * (∑ i, (t i)^2)/2) := by
  have hi := hind.comp (fun i x => t i*x) (by intro i; fun_prop)
  have hh := hi.mgf_sum (by intro i; fun_prop) Finset.univ (t := 1)
  have hmg (i : Fin 3) : mgf (fun ω => t i * V ω i) μ 1 = exp ((1/(2*b))*(t i)^2/2) := by
    rw [mgf_const_mul, mul_one, mgf_gaussianReal (by rw [hmarg i, component_gaussian hb]), variance_coe hb]
    simp
  change mgf (fun ω => ∑ i, t i * V ω i) μ 1 = _ at hh
  rw [hh]
  simp only [Function.comp_def]
  simp_rw [hmg]
  rw [← exp_sum]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  ring

omit [IsProbabilityMeasure μ] in
theorem squares_independent (V : Ω → Velocity) {b : ℝ}
    (hind : iIndepFun (fun i ω => V ω i) μ) : iIndepFun (squares b V) μ := by
  exact hind.comp (fun _ x => 2*b*x^2) (by intro i; fun_prop)

theorem sum_mgf (V : Ω → Velocity) (hV : Measurable V) {b t : ℝ} (hb : 0 < b) (ht : t < 1/2)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b) :
    mgf (sumSquares b V) μ t = (1-2*t)^(-(3:ℝ)/2) := by
  have hh := (squares_independent V (b := b) hind).mgf_sum (by intro i; unfold squares; fun_prop) Finset.univ (t := t)
  change mgf (sumSquares b V) μ t = _ at hh
  rw [hh]
  have hi (i : Fin 3) : mgf (squares b V i) μ t = (1-2*t)^(-(1:ℝ)/2) :=
    square_mgf hb ht (by fun_prop) (hmarg i)
  simp_rw [hi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← rpow_natCast, ← rpow_mul (by linarith : 0 ≤ 1-2*t)]
  congr 1
  ring

theorem sum_integrable (V : Ω → Velocity) (hV : Measurable V) {b t : ℝ} (hb : 0 < b) (ht : t < 1/2)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b) :
    Integrable (fun ω => exp (t*sumSquares b V ω)) μ := by
  simpa only [sumSquares, Finset.sum_apply] using
    (squares_independent V (b := b) hind).integrable_exp_mul_sum (s := Finset.univ)
      (by intro i; unfold squares; fun_prop) (fun i _ => square_integrable hb ht (by fun_prop) (hmarg i))

theorem sum_law (V : Ω → Velocity) (hV : Measurable V) {b : ℝ} (hb : 0 < b)
    (hind : iIndepFun (fun i ω => V ω i) μ)
    (hmarg : ∀ i, μ.map (fun ω => V ω i) = componentLaw b) :
    μ.map (sumSquares b V) = gammaMeasure (3/2) (1/2) := by
  haveI := isProbabilityMeasure_gammaMeasure (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)
  apply Background.mgf_unique μ _ (by unfold sumSquares squares; fun_prop) _ (1/4) (by norm_num)
  · intro t ht
    exact sum_integrable V hV hb (by have := (abs_lt.mp ht).2; linarith) hind hmarg
  · intro t ht
    exact (Background.gamma_mgf (3/2) (1/2) t (by norm_num) (by norm_num)
      (by have := (abs_lt.mp ht).2; linarith)).1
  · intro t ht
    rw [sum_mgf V hV hb (by have := (abs_lt.mp ht).2; linarith) hind hmarg,
      (Background.gamma_mgf (3/2) (1/2) t (by norm_num) (by norm_num)
        (by have := (abs_lt.mp ht).2; linarith)).2]
    congr 1 <;> ring

end MaxwellMGF
