# o048: Entropy.smooth_gaussian_transport

Type: `∀ m : ℕ, 1 ≤ m → (fun (H : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ → ℝ → Prop) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => (fun (T : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => ∀ V : ((EuclideanSpace ℝ (Fin m)) → ℝ), regular V → ∃ φ : ((EuclideanSpace ℝ (Fin m)) → ℝ), T V φ) (fun U φ : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧ ConvexOn ℝ Set.univ φ ∧ MeasureTheory.Measure.map (gradient φ) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (Real.exp (-U x))))) (fun V : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ H V a b) ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x)) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (fun x => Real.exp (-V x)) = 1 ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * Real.log (Real.exp (-V x))) MeasureTheory.volume)) (fun (F : ((EuclideanSpace ℝ (Fin m)) → ℝ)) (a b : ℝ) => ∀ x v : (EuclideanSpace ℝ (Fin m)), a * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v ∧ (fderiv ℝ (fderiv ℝ F) x v) v ≤ b * ‖v‖ ^ 2)`

Statement: Section 2.2, the full-space regularity paragraph: every smooth uniformly convex probability potential has a smooth convex gradient transport from the standard Gaussian.

Role in the glue of o005: Supplies a smooth convex Gaussian transport for each regular target in the universal premise of the normalization child.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__smooth_gaussian_transport.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof and split of Entropy.normalized_transport

This is Section 2 of the supplied paper: the regularity paragraph in
Section 2.2, the two-sided contraction bounds (2.9), the inverse-hazard
parameter (2.10), and Proposition 2.3. The final change-of-variables
identities are already proved on o005 branch x0015 and remain in the glue.

Write E = EuclideanSpace R (Fin m), gamma = stdGaussian E, rho_V(x) =
exp(-V(x)), and q(a) = gaussianPDFReal 0 1 a /
cdf(gaussianReal 0 1)(-a). Let H(F,a,b) mean
 a ||v||^2 <= D(DF)(x)(v)(v) <= b ||v||^2 for all x,v.
The predicate regular is exactly the frozen parent's smoothness,
positive bounded Hessian, mass, second moment and entropy integrability
hypotheses. The predicate T(U,phi) means phi is smooth and convex and
(gradient phi)#gamma = rho_U volume. Each child expands these predicates
using typed lambda applications: no Submission definitions are present
in its frozen type. Smooth means ContDiff at the inner ENat top, not at
the outer WithTop top.

## Child smooth_transport: full-space smooth Gaussian transport

Apply accepted Submission.Lib.Brenier.exists_convex_gradient_transport to
the standard Gaussian and rho_V volume. These are probability measures
with finite second moments; gamma is absolutely continuous and has full
support. This supplies a finite convex potential and its gradient law.
For m >= 2 use the full-space regularity theorem cited in Section 2.2
(Cordero-Erausquin and Figalli, Theorem 1.1, extending Caffarelli's interior
theory). Both domains are E, and both densities are smooth and locally
bounded above and below away from zero. It yields a smooth convex
potential with the same gradient law. In dimension one the monotone map
is the inverse target CDF composed with the Gaussian CDF; positivity of
the smooth densities makes that map smooth, and its primitive is convex.

This child concludes only T(V,phi). It does not choose affine coordinates,
prove quantitative contraction, introduce q, or normalize a matrix mean.
The genuinely missing analytic part beyond accepted Brenier is smooth
regularity. The child may be further split along the cited regularity
argument if needed.

## Child hessian_bounds: two-sided Caffarelli contraction, equation (2.9)

Assume T(V,phi), 0 < a <= b, and H(V,a,b). Caffarelli's quantitative
contraction theorem gives Lip(gradient phi) <= 1/sqrt(a), because the
source Gaussian potential has Hessian I. Smoothness converts this bound
to the upper quadratic-form bound for D^2 phi. The positive smooth
source and target density equations give a positive Jacobian; the
inverse transport is the gradient of the Legendre potential. Applying
contraction to the inverse, whose source Hessian is at most b I and
whose target Gaussian Hessian is I, gives the lower bound
D^2 phi >= 1/sqrt(b) I. Thus
 H(phi, (sqrt b)^-1, (sqrt a)^-1).

This child assumes the transport rather than constructing it, so it is
independent of the existence child's proof. Keeping the explicit a,b is
necessary: Proposition 2.3 requires constants uniform along a homotopy
and controlled under positive linear maps. Merely asserting some bounds
separately for each target would hide this uniformity argument.

## Child inverse_hazard_lift: equation (2.10), smooth matrix parameter

Given smooth phi and H(phi,a,b) with 0 < a <= b, set
 J(x)_ij = (fderiv R (gradient phi) x (PiLp.single 2 j 1)) i,
 A(x) = cfc (Function.invFun q) (J(x)).
Symmetry of the Hessian and the quadratic bounds put J's spectrum in the
compact interval [a,b] within the positive axis. Lemma 2.1 is available
in the accepted GaussianTransport library: q is a smooth increasing
bijection R -> (0,infinity), with positive derivative. Its inverse is
smooth there. Smooth matrix spectral calculus makes every entry of A
smooth, including at repeated eigenvalues; no smooth eigenbasis is
assumed. Spectral compactness bounds all entries of A, which is Hermitian.
The scalar inverse identities and composition of continuous functional
calculus giv
