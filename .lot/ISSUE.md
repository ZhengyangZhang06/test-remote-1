# o044: Entropy.gaussian_covariance_variational

Type: `∀ m : ℕ, 1 ≤ m → (fun γ => ((fun I => ((fun L2 => ((fun W => (∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖^2) MeasureTheory.volume → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 F → MeasureTheory.Measure.map F γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f x)) → ∀ J : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), L2 J → (∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i) → ∀ a : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), ∀ b : Fin m → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), L2 a → (∀ r, L2 (b r)) → (∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => (a x i j - J x i j) * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => b r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))))) → ∀ P : (Matrix (Fin m) (Fin m) ℝ), P.PosDef → Matrix.trace (P * (Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) i) * (x j - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) j))))) ≤ W P a + Finset.sum Finset.univ (fun r : Fin m => W P (b r)))) (fun (P : (Matrix (Fin m) (Fin m) ℝ)) (H : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) => I (fun x => Matrix.trace ((H x).transpose * P * H x))))) (fun (H : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) => ∀ i j, MeasureTheory.MemLp (fun x => H x i j) 2 γ))) (MeasureTheory.integral γ))) ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))))`

Statement: Lemma 3.2 covariance representation and dual estimate, before completion: if DF=a-partial* b in compact-test Gaussian distributions, tr(P Cov(F)) is at most the row-weighted L2 energy of a,b. F has the stated probability density as its pushforward.

Role in the glue of o019: Apply with F=gradient phi, a=k(A)+u and b=v-K. No entropy or k-specific identity is built into this child.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__gaussian_covariance_variational.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof of o019 and its two-child decomposition

This cut follows Section 3 of the supplied paper: equation (3.2), the
covariance representation and dual estimate in Lemma 3.2, and the
H1--Hminus1 completion in that lemma. All definitions in the child types
are expanded using only Mathlib and ChallengeDeps. The scalar functions
are exactly q(a)=gaussianPDFReal(0,1,a)/Phi(-a), t(a)=-log Phi(-a), and
k(a)=t(a)/q(a). The direction e_r is PiLp.single 2 r 1, and all matrix
weights act on rows.

Write gamma for standard Gaussian measure, I for integration against it,
F=gradient phi, J=q(A)=DF, k for k(A), and K_r=partial_r k(A). Write
N(H)=I sum_ij H_ij^2 and W(P,H)=I trace(H^transpose P H). Covariance always
uses the Bochner mean in the frozen statement.

## Entropy identity: proved helper, not a child

The owned files GaussianDensity, Injective, ChangeVariables, Spectral and
Entropy were merged from o019 branch x0045, commits a86b31e and b7cacb9.
Their proofs have been read and built locally. They are checked with this
split, so this step does not require an unproved obligation.

Every q(a) is positive. Functional calculus makes J positive definite.
Along the line from x to y the scalar product of F with y-x has strictly
positive derivative when x differs from y. Hence F is injective. The
change-of-variables theorem for an injective C1 map gives the Jacobian
formula on its image. Combining it with F_*gamma=f dy gives
  |det DF(x)| f(F(x)) = gaussianDensity(x)
almost everywhere. For a merely a.e. measurable f, take a nonnegative
measurable representative and transfer equality using absolute continuity
and the pushforward. No smoothness of f and no surjectivity of F is used.

The integrability of f log f transports to log f composed with F.
Subtracting the known Gaussian log density shows log det J is integrable.
The scalar identity
  log q(a) = -a^2/2 - log(2*pi)/2 + t(a)
and the Hermitian spectral theorem give
  log det J = -sum_ij A_ij^2/2 - m log(2*pi)/2 + trace t(A).
Bounded continuous A has Gaussian L2 entries. Integrating the identity
therefore also establishes integrability of trace t(A), and gives
  2m + 2 integral(f log f) = N(A) - 2 I(trace t(A)) + m.                 (1)
This is equation (3.2) with the common log covariance determinant removed.

## Child cfc: C1 bounded matrix functional calculus

Entropy.c1_bounded_matrix_calculus isolates the regularity used in the
spectral calculus of Sections 2--3. For every C1 real g and bounded C1
Hermitian field A, it asserts that g(A) has C1 bounded entries. No higher
regularity, derivative L2 bound, or energy inequality is requested.
The C1 upgrade of weak testing below is proved, so C1 is sufficient here.

Here is the matrix-calculus proof. Fix a Hermitian base matrix A, with
spectral projectors P_i and eigenvalues lambda_i. The exact difference
identity
  g(B)-g(A) = sum_i P_i (B-A) cfc(g[lambda_i, .])(B)
uses continuous divided differences, including g'(lambda_i) at repeated
eigenvalues. Continuity of CFC yields the Frechet derivative
  Dg(A)[H] = sum_ij g[lambda_i,lambda_j] P_i H P_j.
To see that this derivative is continuous, approximate g' uniformly by
polynomials on a compact interval containing all nearby spectra, and
integrate the approximating polynomials to approximate g. The Frobenius
operator norm of the derivative error is bounded by the scalar derivative
error, using orthogonality of the spectral blocks. Thus the derivative is
a locally uniform limit of polynomial matrix derivatives. Composition
with the C1 field A proves the C1 assertion. A global entry bound R for A
puts every spectrum in [-mR,mR]. The spectral theorem bounds the operator
norm of g(A) by max_{[-mR,mR]} |g|, also bounding its entries.

x0063 has reported a locally checked implementation of this C1 calculus
in MatrixCFCDifferentiation (235fa5d, post at 06:59Z), but that package is
not yet in accepted lib. The child has been reduced to match this existing
candidate rather than asking for unneeded C-
