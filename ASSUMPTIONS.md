# Exact assumptions and external inputs

The main theorem is `MaxwellMGF.maxwell_mgf_project`. There are exactly three
new global mathematical axioms, all in `MaxwellMGF/Background.lean`. They are
permitted background inputs under the supplied course rubric. The final result
is conditional on them. The source audit checks their exact names; no
Maxwell-specific conclusion is postulated.

## Physical and analytic theorem hypotheses

Let μ be a probability measure on a measurable space Ω, and V a measurable
map to three-dimensional Euclidean space. The model provides differentiable
functions g,H: R→R, with

    g(x)+g(y)+g(z) = H(x²+y²+z²), for all real x,y,z;
    f(x)=exp(g(x)) is integrable and has integral 1.

Thus f is strictly positive and measurable. H is assumed differentiable on all
of R, a sufficient extension condition even though squared radii are nonnegative.
The separate physical-law hypothesis is

    map V μ = Lebesgue.withDensity (v ↦ ofReal(f(v₀)f(v₁)f(v₂))).

It expresses a common normalized marginal factor and mutually independent
components. The equation involving H encodes isotropy. Equilibrium in the bulk
rest frame is the physical setting for choosing this density model. It is not
proved from collisions. Orthogonal coordinate axes do not imply independence.

Source: J. C. Maxwell (1860), *Illustrations of the Dynamical Theory of Gases*,
Part I, Proposition IV; supplied reprint pp. 152–154, PDF pp. 5–7.
[Original supplied scan](http://www.alternativaverde.it/stel/documenti/Maxwell/1860/Maxwell%20%281860%29%20-%20Illustrations%20of%20the%20dynamical%20theory%20of%20gases.pdf).
The relevant scan pages were inspected in this run. Maxwell's historical
discussion motivates the assumptions; it does not make them universal physical
truths. The explicit smoothness/positivity conditions are this project's
mathematical regularity assumptions.

## A1: `MaxwellMGF.Background.product_density`

For any probability space (Ω,μ), finite n, measurable V:Ω→Rⁿ, and measurable
nonnegative integrable f:R→R with integral 1, if map V μ has density
`∏ i:Fin n, f(v_i)` with respect to Euclidean Lebesgue measure, then:

1. the coordinates V_i are mutually independent in mathlib's `iIndepFun` sense;
2. for each i, map V_i μ equals the measure with density f.

This is a general product-density criterion. It has no radial or Gaussian
premise/conclusion. Marginal identification follows by Tonelli and normalization
of the other factors. It is used in `model_facts` and `derived_components`.

Reference: Marco Taboga, *Independent random variables*, sections
“Independence between continuous random variables” and “Mutually independent
random variables,” [StatLect](https://www.statlect.com/fundamentals-of-probability/independent-random-variables).
These sections explicitly give the density-factorization criterion.

## A2: `MaxwellMGF.Background.gamma_mgf`

For all a,r>0 and all t<r, exp(t*x) is integrable under the **shape/rate**
Gamma(a,r) measure, and

    mgf id (gammaMeasure a r) t = (1-t/r)^(-a).

The Gamma measure itself is mathlib's `gammaMeasure`, defined by its density
with respect to ordinary Lebesgue measure; it is not an abstract placeholder.
Its probability normalization is a proved library theorem. A2 is used only
for comparison MGFs when identifying the one-square and three-square laws.
The square-normal MGF is derived separately by the proved Gaussian integral.

Reference: Kyle Siegrist, *The Gamma Distribution*, “Moments” of the standard
Gamma law and the generating-function result for the general Gamma law,
[Random](https://www.randomservices.org/random/special/Gamma.html).
The source uses shape k and **scale b**; substituting a=k and r=1/b gives the
formula in the code. Its condition t<1/b becomes t<r. The chi-square convention
Gamma(n/2, rate=1/2) is independently given by
[The Chi-Square Distribution](https://www.randomservices.org/random/special/ChiSquare.html),
“Distribution Functions.”

## A3: `MaxwellMGF.Background.mgf_unique`

Let μ be a probability measure, X:Ω→R a measurable map, and ν a probability
measure on R. If ε>0 and, for every real t with abs(t)<ε,

- exp(t*X) is μ-integrable;
- exp(t*x) is ν-integrable;
- mgf X μ t = mgf id ν t;

then map X μ = ν.

This statement includes existence on an actual common neighborhood of zero,
not just equality of formal moments or totalized integral values. It is used
with ε=1/4 for each square and for the sum.

Reference: Marco Taboga, *Moment generating function*, “Definition” and
“Characterization of a distribution via the moment generating function,”
[StatLect](https://www.statlect.com/fundamentals-of-probability/moment-generating-function).

## Foundations and dependency boundary

`#print axioms MaxwellMGF.maxwell_mgf_project` reports A1–A3 plus `propext`,
`Classical.choice`, and `Quot.sound`. These three standard foundations are not
new project scientific axioms. Bound model hypotheses are visible in the
printed theorem/model structure, not in the global axiom list.

`MaxwellDemo.maxwell_characterization` and `MaxwellDemo.speed_pushforward`
depend only on the standard foundations. The Gamma-to-speed theorem uses A2
and A3 through identification of the sum law. The complete assembled theorem
also uses A1. `verification/axioms.log` provides the actual dependency output.

The background results are stated as axioms to keep the project focused. Their
truth is cited and assumed, not kernel-proved in this development. There are
no unfinished proof placeholders in the submitted Lean modules.
