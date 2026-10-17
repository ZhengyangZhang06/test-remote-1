# o004: Cone.simplex_iff_product

Type: `∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), SimplexIsotropic.IsConvexBody K → ∀ f : (EuclideanSpace ℝ (Fin (n + 1))) → ℝ, f = Set.indicator {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i} (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) → ((∃ L : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))), ∃ a : (EuclideanSpace ℝ (Fin (n + 1))), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin (n + 1), 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin (n + 1) => L.symm (x - a) i)) else 0)) ↔ SimplexIsotropic.IsSimplex K)`

Statement: Section 7, equations (7.7)--(7.8) and converse: the exponential density on the cone over K is an invertible affine exponential product if and only if K is the convex hull of n+1 affinely independent vertices.

Role in the glue of root: Translate analytic equality into the exact frozen IsSimplex predicate, and prove the converse equality for every simplex.

Depends on: none
Weight: 4
Module: Submission/Obl/Cone__simplex_iff_product.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof of both holes and proposed cut

The proof follows the supplied paper, *A sharp entropy bound and the simplex
inequality for isotropic constants*. The four children are the inequality in
Theorem 1.2, its equality classification proved in Section 6, the cone density
and moment calculation (7.1)--(7.5), and the geometric identification of the
exponential-product cone laws with simplices (7.7)--(7.8). The elementary
conversion of the resulting determinant inequality into the stated real-power
constant stays in the root glue. These are independent analytic, integration,
and finite-dimensional geometric tasks, not reformulations of either root hole.

## Density convention and the analytic children

For a nonnegative real function f on E_m = EuclideanSpace R (Fin m), put
b_f = integral x, f(x) * x, C_f(i,j) = integral x,
f(x)(x_i-b_f,i)(x_j-b_f,j), and H_f = -integral x, f(x) log f(x).
The integral is with respect to the standard Euclidean Lebesgue measure.
Here scalar multiplication is used in the vector mean. Require that f is
upper semicontinuous, log f is concave on {f>0}, integral f = 1, and that f,
f times norm(x)^2, and f log f are integrable. ConcaveOn includes convexity
of {f>0}. These hypotheses describe the upper semicontinuous representatives
of the paper's log-concave densities; V=-log f on {f>0}, V=+infinity elsewhere
is proper lower semicontinuous and convex. No special density definition is
assumed by a child: its frozen statement binds these expressions through explicit defining equalities.

Child Entropy.lower_bound asserts m + log(det C_f)/2 <= H_f (Theorem 1.2,
inequality part). Its proof is Sections 2--5, as follows. For smooth uniformly
convex V, Gaussian optimal transport supplies J=D^2 phi with positive upper
and lower bounds. With t(a)=-log Phi(-a), q=t', set A=q^{-1}(J) using symmetric
spectral calculus. Lemma 2.1 gives q'>0, q'<1 and the Gaussian/exponential
transport. Proposition 2.3 chooses a positive definite affine normalization
with E A=0 by a homotopy from the Gaussian; contraction estimates, Gaussian
Poincare and covariance bounds make the zero set compact. Lemma 2.4 permits
the cutoff integrations by parts. Proposition 2.5, obtained by multiplying the
Jacobian equation by k(A)^2, k=t/q, gives
 E tr k(A)^2 >= ||partial A||^2 - ||partial k(A)||^2 + C,
where C is the nonnegative eigenvalue-separation surplus. Its divided
differences and arithmetic/logarithmic mean comparisons must be retained.

Write A=sum x_r X_r+Y, B=sum X_r^2; Y has Gaussian degrees at least two.
The covariance completion (Lemma 3.2) with the Ornstein--Uhlenbeck resolvent
and the log-determinant supporting plane S=(37 I/40+3 B/40)^(-1) express the
signed entropy deficit D=2m+log det C_f-2H_f. The exact expansion in Lemma 3.3
and the commutator square in Lemma 3.4 control noncommuting factors.
Proposition 3.5 absorbs the supporting-plane cost and retains
-(sum omega(lambda_i(B)))/1000; Proposition 3.6 charges the divided-difference
error to the same C above. Their scalar estimates are proved in Section 4
and Appendix A by rational bounds and analytic tail estimates, not sampling.
After cancellation, the remaining quadratic form is
 Q(u,v)=43 u^2/100+26 uv/100+68 v^2/25.
For chaos degree d>=2 put r=1/d. The identity
 1-r-Q(1,r-1/2)-7r/50 = (1-2r)(1+68r)/50 >= 0
proves Theorem 3.1:
 2H_f-2m-log det C_f >= ||Y||^2/500 + sum omega(lambda_i(B))/1000.
In particular the entropy inequality holds in the smooth case. Lemma 5.1
supplies linear coercivity of V. Lemma 5.2 uses Moreau envelopes, mollification
and a quadratic correction to approximate by smooth uniformly convex
potentials, with convergence of entropy, means and covariance. The limiting
covariance is positive definite, since a Lebesgue probability density cannot
be concentrated on a proper affine hyperplane. Passage to the limit proves
the analytic inequality for the stated representatives.

Child Entropy.equality_cases asserts H_f=m+log(det C_f)/2 if and only if f is,
almos
