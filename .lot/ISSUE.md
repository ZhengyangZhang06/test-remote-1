# o007: Entropy.smooth_approximation

Type: `∀ m : ℕ, 1 ≤ m → (fun (density : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m)) → ℝ) => (fun (mean : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m))) => (fun (covariance : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) => (fun (entropy : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∃ V : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, regular (V n)) ∧ Filter.Tendsto (fun n => entropy (density (V n))) Filter.atTop (nhds (entropy f)) ∧ (∀ i j, Filter.Tendsto (fun n => covariance (density (V n)) i j) Filter.atTop (nhds (covariance f i j))) ∧ Filter.Tendsto (fun n => mean (density (V n))) Filter.atTop (nhds (mean f)) ∧ Filter.Tendsto (fun n => MeasureTheory.integral MeasureTheory.volume (fun x => |density (V n) x - f x|)) Filter.atTop (nhds 0)) (fun V => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖ ^ 2) ∧ MeasureTheory.Integrable (density V) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (density V) = 1 ∧ MeasureTheory.Integrable (fun x => density V x * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => density V x * Real.log (density V x)) MeasureTheory.volume)) (fun f => -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)))) (fun f => Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - mean f i) * (x j - mean f j))))) (fun f => MeasureTheory.integral MeasureTheory.volume (fun x => f x • x))) (fun V x => Real.exp (-V x))`

Statement: Lemma 5.2 (using Lemma 5.1): approximate a log-concave density by normalized exponentials of smooth potentials with positive bounded Hessian, preserving entropy, centered covariance, means and L1 mass.

Role in the glue of o001: Supply the sequence to which the smooth estimate applies and the convergence needed in the final limit passage.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__smooth_approximation.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof and proposed paper-aligned cut for Entropy.lower_bound

This proof follows Sections 2, 3--4 and Appendix A, and Section 5 of the
supplied paper. There are three substantive analytic interfaces: normalized
smooth Gaussian transport (Proposition 2.3 and its prerequisites), the
normalized smooth estimate with its strict remainder (Theorem 3.1), and
convex approximation preserving entropy and covariance (Lemma 5.2).
The final continuity argument belongs in the glue.

For a probability density f on EuclideanSpace R (Fin m), write b(f) for
its vector first moment, C(f) for its centered second-moment matrix, and
H(f) = -integral f log f. These abbreviations will be expanded in every
frozen statement. For a smooth real potential V, uniform convexity means
c_minus * norm(v)^2 <= D(DV)(x)(v)(v) <= c_plus * norm(v)^2 for all x,v,
where c_minus and c_plus are strictly positive. This is the coordinate-free
version of the paper's two Hessian inequalities.

## Approximation: Lemmas 5.1 and 5.2

Set V=-log f on the convex positive set and V=+infinity outside it.
The hypotheses on f give a proper lower semicontinuous convex extended
potential; mass one ensures a full-dimensional effective domain. Lemma 5.1
proves V(x)>=a*norm(x)-b: a finite-volume convex sublevel containing a ball
is bounded, and convexity along rays gives linear coercivity. For each
positive integer j form Q_j(x)=inf_y(V(y)+j*norm(x-y)^2/2), convolve with an
even smooth unit-mass mollifier of radius 1/j, and add norm(x)^2/j.
The minimizer defining Q_j is unique; its monotonicity gives a j-Lipschitz
gradient. Thus the smoothed potential has Hessian between 2/j and j+2/j.
The estimates Q_j>=a*norm(x)-b-a^2/(2j) and
0<=Q_j*mollifier-Q_j<=1/(2j) give convergence and a common exponential
tail. Dominated convergence applies to mass, first moments, second moments,
and V_j exp(-V_j). Absorb log Z_j into each potential so exp(-V_j) is
already a probability density. The resulting densities have convergent
L1 distance, means, covariance entries, and entropy.

## Normalized Gaussian transport: Section 2 through Proposition 2.3

Let gamma_m be standard Gaussian measure. Put
q(a)=varphi(a)/Phi(-a) and t(a)=-log Phi(-a).
Lemma 2.1 proves q is a smooth increasing bijection R -> (0,infinity),
0<q'<1, and q''>=0. For any smooth probability potential with positive
bounded Hessian, Brenier transport is a smooth gradient and the two
Caffarelli contraction inequalities bound its Jacobian above and below.
The matrix field A=q^{-1}(D^2 phi) is therefore smooth and bounded.

Proposition 2.3 chooses a positive definite linear change of variables P
for which integral A dgamma_m=0. It deforms the density from Gaussian,
uses transport uniqueness and strict log-determinant concavity to prove
continuity of integral q^{-1}(J), and bounds all zeros in a compact subset
of the positive definite cone using covariance, Jensen and Gaussian
Poincare. The Gaussian endpoint has one zero of nonzero Brouwer degree;
homotopy invariance supplies a zero for the target density. The transformed
potential remains smooth with positive bounded Hessian. Change of variables
gives H(P#f)=H(f)+log|det P| and
log det C(P#f)=log det C(f)+2log|det P|. Their entropy gaps agree.
The transport interface retains P and its pushforward identity, so the
same normalization can be used in the equality analysis.

## Normalized strict remainder: Theorem 3.1

For a normalized transport write X_r=integral x_r A dgamma_m,
Y=A-sum_r x_r X_r, and B=sum_r X_r^2. Theorem 3.1 states
2H-2m-log det C >= integral tr(Y^T Y)/500 + sum_i omega(lambda_i(B))/1000,
with omega the exact nonnegative weight in (3.1). In the frozen interface
tr(Y^T Y) is the sum of squares of all matrix entries; these are equal
without a symmetry assumption. The eigenvalue term is retained for reuse
in Section 6, rather than discarded in the child.

Here is the paper's derivation of that estimate. Lemma 2.4 obtains finite
Jacobian energy from the twice differentiated Monge
