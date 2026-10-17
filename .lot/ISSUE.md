# o008: Entropy.centered_slack_transports

Type: `∀ m : ℕ, 1 ≤ m → (fun (q : ℝ → ℝ) (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (ω : ℝ → ℝ) => ∀ f : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, (∀ x, 0 ≤ f n x) ∧ MeasureTheory.Integrable (f n) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (f n) = 1 ∧ MeasureTheory.Integrable (fun x => f n x * ‖x‖ ^ 2) MeasureTheory.volume) → ∀ P : ℕ → (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ G : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ A : ℕ → (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), (∀ n, ContDiff ℝ 1 (G n)) → (∀ n i j, Continuous (fun x => A n x i j)) → (∀ n x, (A n x).IsHermitian) → (∀ n, ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A n x i j| ≤ R) → (∀ n x i j, cfc q (A n x) i j = (fderiv ℝ (G n) x (PiLp.single 2 j (1 : ℝ))) i) → (∀ n, MeasureTheory.Measure.map (G n) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (|LinearMap.det (P n).toLinearMap|⁻¹ * f n ((P n).symm x)))) → (fun (X : ℕ → Fin m → (Matrix (Fin m) (Fin m) ℝ)) => (fun (B : ℕ → (Matrix (Fin m) (Fin m) ℝ)) => (fun (energy : ℕ → ℝ) => ∀ hB : ∀ n, (B n).PosSemidef, ∀ δ : ℕ → ℝ, Filter.Tendsto (δ) Filter.atTop (nhds (0)) → (∀ n, energy n / 500 + Finset.sum Finset.univ (fun i : Fin m => ω ((hB n).isHermitian.eigenvalues i)) / 1000 ≤ δ n) → ∃ F : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), (∀ n, ContDiff ℝ 1 (F n) ∧ MeasureTheory.MemLp (F n) 2 γ ∧ MeasureTheory.integral γ (F n) = 0) ∧ (∀ n, MeasureTheory.Measure.map (F n) γ = MeasureTheory.Measure.map (fun x => P n (x - MeasureTheory.integral MeasureTheory.volume (fun y => f n y • y))) (MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f n x)))) ∧ (∀ n i j, MeasureTheory.MemLp (fun x => A n x i j) 2 γ) ∧ (∀ n r, (X n r).IsHermitian) ∧ (∀ n x v i, (fderiv ℝ (F n) x v) i = Finset.sum Finset.univ (fun j : Fin m => cfc q (A n x) i j * v j)) ∧ Filter.Tendsto (energy) Filter.atTop (nhds (0)) ∧ Filter.Tendsto (B) Filter.atTop (nhds (1 : (Matrix (Fin m) (Fin m) ℝ)))) (fun n => MeasureTheory.integral γ (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => ((A n x - Finset.sum Finset.univ (fun r : Fin m => x r • X n r)) i j) ^ 2))))) (fun n => Finset.sum Finset.univ (fun r : Fin m => X n r * X n r))) (fun n r => Matrix.of (fun i j => MeasureTheory.integral γ (fun x => x r * A n x i j)))) (fun t : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 t / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun z : ℝ => (3 * (z - 1) ^ 2 / (37 + 3 * z)) * ((3 : ℝ) / 20 + ((49 : ℝ) / 100) * (37 / (37 + 3 * z))) * (if z = 0 then (13 : ℝ) / 100 else min ((13 : ℝ) / 100) (32 / (25 * Real.sqrt z))))`

Statement: Section 6, vanishing-slack and centering: for smooth Gaussian transports of affine images of probability densities, a strict remainder tending to zero yields centered square-integrable transports with the same Jacobians, vanishing nonlinear residual, and coefficient square sum converging to identity.

Role in the glue of o002: Converts the data supplied by reused normalization and remainder into the centered sequence required by Gaussian compactness.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__centered_slack_transports.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof and proposed decomposition of Entropy.equality_cases

We follow Section 6 of the supplied paper, with the strict remainder of
Theorem 3.1 and the approximation of Lemma 5.2 as explicit inputs. Put
E = EuclideanSpace R (Fin m), gamma = ProbabilityTheory.stdGaussian E,
Phi = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1),
q(s) = ProbabilityTheory.gaussianPDFReal 0 1 s / Phi(-s), and
T(s) = -log(Phi(-s)). A scalar function of a symmetric matrix means
Mathlib's real continuous functional calculus. Squared Frobenius norms
will be written as sums of the squares of all entries, never as an
unqualified matrix norm.

## 1. Approximation with vanishing strict remainder

The shared inputs are the separately frozen children of o001:
o005 Entropy.normalized_transport (Proposition 2.3),
o006 Entropy.normalized_remainder (Theorem 3.1), and
o007 Entropy.smooth_approximation (Lemma 5.2). The checked local
Assembly.lean glue applies these three statements directly. It does
not repeat Sections 2--5. These are the interfaces described by
x0009's 2026-10-17T05:57 finding and subsequently frozen by the tree.
The glue's Context.lean definitions are just local abbreviations for
their exact types, and are not used in any frozen child statement.
The first new child, centered_slack_transports, assumes the resulting
raw transport and remainder data, and proves centering, square
integrability, and the vanishing-field and coefficient limits.

For an equality density f, Lemma 5.2 supplies smooth uniformly convex
probability densities f_j converging in L1, entropy, means b_j, and
covariances C_j to f, b, C. C is positive definite: zero variance in a
nonzero direction would force a Lebesgue probability density to be
supported on a null affine hyperplane. This positivity is now supplied
directly in the glue by the accepted helper
Submission.Lib.EntropyTools.densityCovariance_posDef (x0004, g00008),
so it is not part of a new child. Thus the log determinants converge
and the entropy gaps tend to zero.

The assembly glue applies o005 pointwise and uses choice to obtain
normalizers P_j, smooth potentials phi_j, and bounded smooth symmetric
fields A_j. Differentiating phi_j gives a C1 Gaussian map G_j. From
o005's W_j(x)=V_j(P_j^{-1}x)+log|det P_j|, the glue proves the exact
affine-density identity using exp of a sum and det P_j != 0. It then
applies o006 to each normalized triple. These steps are all proved
in Assembly.lean, rather than deferred to a construction axiom.

The first child centers G_j to F_j=G_j-E G_j. Its raw law identity
and the finite second moment of f_j imply Gaussian L2 integrability
of G_j by affine change of variables. Its mean is P_j b_j, so the law
of F_j is the image of f_j dx under x -> P_j(x-b_j). Centering leaves
the Jacobian unchanged. The coordinate-basis Jacobian identity supplied
by o005 extends to every direction by linearity. Boundedness and
continuity of A_j give entrywise Gaussian MemLp 2. Set
X_jr = E_gamma[x_r A_j], and
Y_j = A_j - sum_r x_r X_jr. The fields and maps have Gaussian square
integrability. Theorem 3.1 gives
 E_gamma |Y_j|_F^2 -> 0, sum_i omega(lambda_i(sum_r X_jr^2)) -> 0.
The scalar weight omega is continuous, nonnegative, zero only at one,
and coercive at infinity. Concretely its final factor is 13/100 at
lambda=0 and min(13/100,32/(25 sqrt(lambda))) otherwise, and
omega(lambda)/sqrt(lambda) -> 24/125. For each epsilon>0, its infimum
on the nonnegative lambdas with |lambda-1|>=epsilon is positive:
restrict to a compact interval using coercivity and use its unique
zero there. Each eigenvalue is nonnegative because the coefficients
are symmetric and B_j=sum_r X_jr^2 is positive semidefinite. The finite
sum tending to zero forces every eigenvalue to approach one. Orthogonal
spectral decomposition then bounds ||B_j-I|| by the largest eigenvalue
distance, proving sum_r X_jr^2 -> I. To apply the remainder to the transported law, use affine invariance:
H(W_j)=H(f_j)+log|det P_j| and
det Cov(W_j)=(d
