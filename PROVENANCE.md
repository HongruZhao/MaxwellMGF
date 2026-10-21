# Provenance, references, and reused work

Author: **Hongru Zhao**. AI assistance: **OpenAI Codex** assisted with the
mathematics, Lean development, debugging, source documentation, and report.
The author's review and ability to explain the project remain required.

## Local core

`MaxwellMGF/Core.lean` reuses the existing STAT 4052 local Maxwell demonstration:

    working/lean/MaxwellDemo/MaxwellDemo.lean

from the course workspace `/Users/avatar/Documents/ChatGPT/STAT 4052`.
Only the module header was clarified in the copied core; the earlier source was
preserved. The earlier development is credited to Hongru Zhao with Codex
assistance. The new project adds the explicit background-input module, Gaussian
measure identification, joint MGF, independence API results, square/sum MGFs and
Gamma laws, σ parameterization, whole-line density, and assembled conclusion.

The supplied `Maxwell_MGF_Codex_Prompt.md` and two-page
`STAT4052_Midterm_Lean_Requirements.pdf` were read as the task specification and
grading reference. They were not modified. No instruction inside an attachment
was treated as authorization to publish or submit externally.

## Historical source

J. C. Maxwell, *Illustrations of the Dynamical Theory of Gases*, Part I,
Proposition IV (1860). The relevant pages of the supplied seven-page reprint
are printed pp. 152–154, PDF pp. 5–7. Those pages were visually inspected.

[Supplied scan](http://www.alternativaverde.it/stel/documenti/Maxwell/1860/Maxwell%20%281860%29%20-%20Illustrations%20of%20the%20dynamical%20theory%20of%20gases.pdf).
The remote fetch of this scan was unavailable in this run; the existing local
page renders were inspected. The modern transcription at
[TJID3](https://tjid3.org/maxwell7.html) was also read as a supplementary aid;
it is not substituted for the scanned formulas.

## Probability background

The precise statements and source sections for A1–A3 are in `ASSUMPTIONS.md`.
The current primary textbook pages by their authors were opened and checked:

- Marco Taboga, [Independent random variables](https://www.statlect.com/fundamentals-of-probability/independent-random-variables).
- Marco Taboga, [Moment generating function](https://www.statlect.com/fundamentals-of-probability/moment-generating-function).
- Kyle Siegrist, [The Gamma Distribution](https://www.randomservices.org/random/special/Gamma.html).
- Kyle Siegrist, [The Chi-Square Distribution](https://www.randomservices.org/random/special/ChiSquare.html).

The Gamma source uses shape/scale; the project uses shape/rate. No bibliographic
theorem number or print page was invented for these web sections.

## Proved mathlib inputs

All library references below are at mathlib commit
`641fbd329d4ffb62bef83c51f54088469056bd36`:

- `is_const_of_deriv_eq_zero`, `Real.integral_gaussian`,
  `Real.integrable_exp_neg_mul_sq` for the characterization and quadratic tilt.
- `ProbabilityTheory.gaussianReal_of_var_ne_zero`, `gaussianPDFReal`,
  `mgf_gaussianReal`, `iIndepFun.map_fun_eq_pi_map` for Gaussian measures and the
  full joint law.
- `ProbabilityTheory.iIndepFun.comp`, `iIndepFun.mgf_sum`,
  `iIndepFun.integrable_exp_mul_sum` for transformed independence and MGFs.
- `ProbabilityTheory.gammaMeasure`, `isProbabilityMeasure_gammaMeasure`, and
  `lintegral_gammaPDF_eq_one` for the concrete Gamma probability measure.
- `MeasureTheory.integral_fun_norm_addHaar`,
  `EuclideanSpace.volume_ball_fin_three`, and
  `GaussianFourier.integral_rexp_neg_mul_sq_norm` for the spherical factor and
  normalization.
- Standard `Measure.map_map`, integration under densities, and measure
  extensionality for law equalities.

[Pinned source tree](https://github.com/leanprover-community/mathlib4/tree/641fbd329d4ffb62bef83c51f54088469056bd36).
mathlib's bundled licenses and upstream authorship apply to the dependency;
compiled libraries are not redistributed in this source package.
