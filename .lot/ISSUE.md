# o024: Entropy.orthogonal_gaussian_exponential_law

Type: `∀ m : ℕ, 1 ≤ m → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) F = 0 → ∀ Q : (EuclideanSpace ℝ (Fin m)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ a : (EuclideanSpace ℝ (Fin m)), (∀ x : (EuclideanSpace ℝ (Fin m)), ∀ i : Fin m, (Q.symm (F (Q x) - a)) i = -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x i))) → (MeasureTheory.Measure.map F (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (|LinearMap.det Q.toLinearEquiv.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ Q.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => Q.symm (x - a) i)) else 0)))) ∧ ((fun i j => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => F x i * F x j)) = (1 : (Matrix (Fin m) (Fin m) ℝ)))`

Statement: Last paragraph of Lemma 6.1: an orthogonally conjugated coordinatewise -log Gaussian-survival map has the explicit affine exponential-product density, and when centered its full raw second-moment matrix equals I.

Role in the glue of o011: Applied to Q and a from normal_form, proves the density using L=Q.toLinearEquiv and the covariance conjunct of o011.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__orthogonal_gaussian_exponential_law.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Decomposition of o011: linear Jacobian rigidity

We split Lemma 6.1 of the supplied paper at its displayed rigid-map formula.
The first child proves that deterministic formula; the second proves the
last paragraph of the lemma, including the density and centered covariance
required by the frozen parent. They have no dependency on one another.
Only their statements meet in the glue.

Write E = EuclideanSpace R (Fin m), gamma = stdGaussian E,
Phi(t) = cdf (gaussianReal 0 1) t, phi(t) = gaussianPDFReal 0 1 t,
q(t) = phi(t)/Phi(-t), and T(t) = -log(Phi(-t)). These are notation in
this explanation only: the frozen children expand the functions explicitly.

## Child 1: deterministic normal form (Lemma 6.1 through rigid-map)

Assume m >= 1, F is C1, every X_r is real Hermitian, sum_r X_r^2 = I,
and DF(x) = q(A(x)), where A(x) = sum_r x_r X_r. No Gaussian moment
or centering hypothesis is needed in this child. We prove that there are
a linear isometry equivalence Q : E -> E and a vector a such that

    (Q^{-1}(F(Q y) - a))_i = T(y_i)    for every y and i.

First extract the integrability conditions of the Jacobian. The Gaussian
density is real analytic and its cdf is real analytic near zero, with
Phi(0)=1/2. Consequently q is analytic near zero. Its scalar identities give

    q(0) = sqrt(2/pi),
    q'(0) = 2/pi > 0,
    q''(0) = sqrt(2/pi) * (4/pi - 1) > 0.

Positivity in the last identity uses pi < 4. The power series for q,
evaluated by matrix multiplication, converges locally around A=0. On
Hermitian matrices it agrees with the real continuous functional calculus:
diagonalize the matrix and apply the scalar series at each eigenvalue.
The series and its differentiated series converge uniformly on smaller
balls. Thus J(x)=q(A(x)) is analytic near zero and

    J(x) = q(0) I + q'(0) A(x) + q''(0)/2 * A(x)^2 + O(|x|^3),

with differentiated remainder O(|x|^2). Since F is C1 and DF=J, the
analyticity of J upgrades F to C3 locally. Equality of mixed derivatives
therefore gives (partial_r J)e_s = (partial_s J)e_r. Comparing its constant
and linear terms, using the two nonzero scalar derivatives, gives

    X_r e_s = X_s e_r,
    (X_r A(x) + A(x) X_r)e_s = (X_s A(x) + A(x) X_s)e_r.

The first identity says A(x)z=A(z)x, so A(x)e_s=X_s x. Canceling the
terms with leftmost A(x) in the second identity leaves
(X_r X_s - X_s X_r)x=0 near zero. This homogeneous linear identity holds
everywhere, hence all the X_r commute. This is the difficult analytic
compatibility step; merely assuming F is C1 causes no loss of derivatives
because its prescribed Jacobian is analytic locally.

Choose a common orthonormal eigenbasis of the commuting real symmetric
matrices, with orthogonal matrix U. After rotating input and output the
coefficient of y_i is

    Xtilde_i = U^T (sum_r U_ri X_r) U.

It is diagonal; orthogonality gives sum_i Xtilde_i^2=I; and the first
compatibility identity gives Xtilde_i e_j=Xtilde_j e_i. For i != j the two
sides lie in distinct coordinate lines, so both vanish. Thus only the
ith diagonal entry of Xtilde_i can be nonzero, and its square is one.
Write this entry sigma_i, so sigma_i is 1 or -1. It follows that

    U^T A(U y) U = diag(sigma_i y_i),
    D[U^T F(U y)] = diag(q(sigma_i y_i)).

The Gaussian cdf is strictly positive at every finite point. Its derivative
and the evenness of phi give T'=q on all of R. The accepted o009 CDF and
Hazard modules (lib a6f3986fe0) already expose cdf_eq_mass, mass_pos,
hasDerivAt_mass, and hasDerivAt_hazard in namespace
Submission.Obl.Entropy__gaussian_hazard_lipschitz, so the scalar derivative
and positivity steps can reuse those proofs. Therefore the vector
(sigma_i T(sigma_i y_i))_i has precisely this Jacobian. The difference has
zero derivative on the connected space E, hence is a constant w, pointwise:

    U^T F(U y) = (sigma_i T(sigma_i y_i))_i + w.

For the frozen child we absorb the signs into the orthogonal map. Let
S=diag(sigma_i), Q=U S, and a=U w. Substitute y=S z in this last form
