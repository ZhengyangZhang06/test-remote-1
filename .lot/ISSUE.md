# o026: Entropy.continuous_jacobian_of_l2_limit

Type: `∀ m : ℕ, ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ J : (EuclideanSpace ℝ (Fin m)) → ((EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m))), (∀ n, ContDiff ℝ 1 (Fseq n)) → (∀ n, MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) → MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → (∀ n, MeasureTheory.MemLp (fderiv ℝ (Fseq n)) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) → MeasureTheory.MemLp J 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → Continuous J → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq n x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖fderiv ℝ (Fseq n) x - J x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → ∃ G : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 G ∧ Filter.EventuallyEq (MeasureTheory.ae (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) G F ∧ (∀ x, fderiv ℝ G x = J x)`

Statement: If C1 maps and their classical Jacobians converge in Gaussian L2 and the limiting Jacobian field is continuous, the limiting map has a global C1 representative with exactly that derivative.

Role in the glue of o010: Replace the centered L2 limit by an almost-everywhere equal C1 map and preserve its mean and squared L2 convergence in glue.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__continuous_jacobian_of_l2_limit.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof of the linear transport limit and proposed cuts

Write E = EuclideanSpace R (Fin m), gamma = stdGaussian E, and
|M|_F^2 = sum_i sum_j (M i j)^2. All matrix energies below are these
explicit Frobenius sums, not the default norm on matrices.

## Finite-dimensional extraction

For real Hermitian coefficients, symmetry gives
sum_r |X_nr|_F^2 = trace(sum_r X_nr * X_nr).
The right side converges to m and is bounded. Thus the whole finite
coefficient array is bounded in a finite-dimensional real space. Extract
a strictly increasing subsequence sigma on which the array converges to
X. Hermitian symmetry is closed and matrix multiplication and finite sums
are continuous, so every X_r is Hermitian and sum_r X_r * X_r = I.
The owned Compactness.lean helper implements this step. Its original
proof was written by x0027 (2912f26, reported 2026-10-17T06:34Z) and
merged into this branch. It uses finite-dimensional compactness and no
unaccepted module. Earlier posts reported the same result in x0007's
EntropyMatrix candidate, but that source/package was unavailable here;
no dependency on that candidate remains.

Replace F_n, A_n, X_n by their sigma subsequences. The residual energies
still tend to zero since a strictly increasing map N -> N tends to infinity.

## Proved-helper step: convergence of the functional-calculus fields

Let L_n(x) = sum_r x_r X_nr, L(x) = sum_r x_r X_r,
J_n(x) = cfc q (A_n(x)), and J(x) = cfc q (L(x)). The assumed Frobenius
contraction on Hermitian matrices makes the map U -> cfc q U continuous
on that closed subspace; no independent regularity assumption on q is
needed. Linear combinations of the X_r are Hermitian, so J is continuous.
The same contraction against zero bounds |cfc q U|_F by |U|_F plus the
fixed finite value |cfc q 0|_F. For J_n, the implemented proof also reads its entries from DF_n on
coordinate basis vectors; the C1 hypothesis makes them continuous
directly. Thus all entries of J_n and J are Gaussian L2 functions.

Gaussian coordinate orthogonality gives
 integral |L_n - L|_F^2 dgamma = sum_r |X_nr - X_r|_F^2 -> 0.
The checked helper uses the sufficient Cauchy-Schwarz bound
 integral |L_n-L|_F^2 <= (integral ||x||^2 dgamma)
                         * sum_r |X_nr-X_r|_F^2;
this requires only the finite Gaussian second moment.
The pointwise inequality
 |J_n - J|_F^2 <= |A_n - L|_F^2
                 <= 2 |A_n - L_n|_F^2 + 2 |L_n - L|_F^2
then proves integral |J_n-J|_F^2 dgamma -> 0. Every energy here is
integrable: each A_n entry is L2 by hypothesis and Gaussian coordinates
have finite second moments. This integrability is essential, since the
Bochner integral convention alone would not measure a nonintegrable
nonnegative residual correctly. This step contains no map convergence,
subsequence extraction, or normalization of X.

## Child 1: a Gaussian derivative-to-function L2 bound

This child asks only for a finite positive Gaussian Poincare constant:
for each m there is C>0 such that every centered C1 map h with
h and Dh in Gaussian L2 satisfies integral ||h||^2 <= C integral ||Dh||^2.
The L2 completeness and centering consequence is proved in the owned
L2Limit.lean helper from x0027 (15b7450, reported 06:31Z). In both child
types the derivative is a continuous linear endomorphism and the norm
is its operator norm. For such a derivative D, |D|_F^2 <= m ||D||^2;
therefore operator-norm L2 convergence implies entrywise/Frobenius L2
convergence. The proved entriesCLM bridge converts the Frobenius
convergence above into operator-norm convergence. Assume C1
maps H_n are centered and in L2(gamma), their derivative matrices J_n
have L2 entries, and J_n converge to an L2 matrix field J. There is a
centered L2 function H with integral ||H_n-H||^2 dgamma -> 0.

For each difference H_n-H_k, the Gaussian Poincare inequality is
 integral ||H_n-H_k||^2 dgamma <= integral |J_n-J_k|_F^2 dgamma.
The right side is at most 2m integral ||J_n-J||^2 plus
2m integral ||J_k-J||^2, and hence tends to zero. The classe
