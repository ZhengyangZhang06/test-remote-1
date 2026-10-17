# o012: Entropy.affine_limit_density

Type: `∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → MeasureTheory.Integrable f (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (f) = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x • x) → ∀ C : (Matrix (Fin m) (Fin m) ℝ), C = (fun i j => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x * (x i - b i) * (x j - b j))) → C.PosDef → ∀ fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, ∀ bseq : ℕ → (EuclideanSpace ℝ (Fin m)), ∀ Cseq : ℕ → (Matrix (Fin m) (Fin m) ℝ), ∀ Pseq : ℕ → (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), (∀ n, (∀ x, 0 ≤ fseq n x) ∧ MeasureTheory.Integrable (fseq n) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fseq n) = 1 ∧ MeasureTheory.Integrable (fun x => fseq n x * ‖x‖ ^ 2) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) ∧ bseq n = MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => (fseq n) x • x) ∧ Cseq n = (fun i j => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => (fseq n) x * (x i - (bseq n) i) * (x j - (bseq n) j)))) → (Filter.Tendsto (fun n => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => |fseq n x - f x|)) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (bseq) Filter.atTop (nhds (b))) → (Filter.Tendsto (Cseq) Filter.atTop (nhds (C))) → (∀ n, MeasureTheory.Measure.map (Fseq n) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = MeasureTheory.Measure.map (fun x => Pseq n (x - bseq n)) ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (fseq n x)))) → (∀ n, ContDiff ℝ 1 (Fseq n) ∧ MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) ∧ MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (Fseq n) = 0) → ∀ σ : ℕ → ℕ, StrictMono σ → ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (F) = 0 → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq (σ n) x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → (∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), MeasureTheory.Measure.map F (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))).withDensity (fun x => ENNReal.ofReal (|LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)))) → ((fun i j => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => F x i * F x j)) = (1 : (Matrix (Fin m) (Fin m) ℝ))) → ∃ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∃ a : (EuclideanSpace ℝ (Fin m)), ∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)`

Statement: Section 6, normalized-covariance-limit through the penultimate paragraph: recover an affine exponential-product density from subsequential L2 convergence of centered affine normalizations, positive limiting covariance, and an exponential-product limit with covariance I.

Role in the glue of o002: Transfers the classified normalized law back to the original density, with the exact Jacobian factor.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__affine_limit_density.lean

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
