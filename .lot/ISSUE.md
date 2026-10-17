# o017: Entropy.integrated_two_eigenvalue

Type: `∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun γ => (fun I => (fun L2 => (fun d => (fun Z => (fun t => (fun q => (fun k => (fun K => (fun X => (fun Y => (fun b => (fun l => (fun p => (fun δ => (fun σ => (fun U => (fun sep => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → ∀ g : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), (∀ r x, (g r x).IsHermitian) → (∀ r, L2 (g r)) → (fun N => (fun Dr => (fun Lr => (fun f0 => (fun Mr => (fun PB => (fun G => (fun Q => (fun QE => (∀ a, 0 < p a) ∧ PB ≤ QE + sep) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => Q (G r x i j) (g r x i j - G r x i j / 2))))))) (fun a b => (43/100)*a^2 + (26/100)*a*b + (68/25)*b^2)) (d Y)) (Finset.sum Finset.univ (fun r : Fin m => (40/37)*N (fun x => Dr r x - (7/25 : ℝ) • g r x) + (42/37)*N (fun x => Dr r x - (3/4 : ℝ) • g r x) + (27/592)*N (g r) + (40/3)*N (Lr r) + (5/17)*N (fun x => Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x))))) (fun r x => d (fun y => cfc f0 (A y)) r x - X r * cfc (deriv f0) (A x) - 2 • (Dr r x * cfc b (A x)) - (80/3 : ℝ) • (Lr r x * cfc l (A x)) + (3/2 : ℝ) • (g r x * cfc b (A x)))) (fun a => k a * (1 + b a))) (fun r x => d (fun y => cfc b (A y)) r x - X r * cfc l (A x))) (fun r x => K r x - X r * cfc b (A x))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => σ ((hA x).eigenvalues i) ((hA x).eigenvalues j) * ((U x).transpose * Z r x * U x) i j ^ 2)))))) (fun x => ((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))) (fun a b => (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100 else if min a b < -1 then 38/100 else 68/100)) / 16 * (1 + (δ a b)^2/30 + (δ a b)^4/1680) * (δ a b)^2)) (fun a b => Real.log (q a) - Real.log (q b))) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (d (fun x => cfc k (A x)))) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (d A)) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))`

Statement: Proposition 3.6 and its Section 4 and Appendix A certificates, integrated in a pointwise orthonormal eigenbasis of A.

Role in the glue of o006: Proves p positive and bounds the derivative residual budget by the chaos quadratic form plus precisely the transport separation surplus.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__integrated_two_eigenvalue.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Paper proof of normalized_remainder (o006)

This cut follows Theorem 3.1 of the supplied paper, with the analytic inputs
of Lemma 2.4 and Proposition 2.5 and the estimates of Sections 3--4.
All definitions below will be expanded in the closed child propositions;
no new definition is assumed as an axiom.

Write gamma for standard Gaussian measure and E for its expectation.
Set t(a)=-log Phi(-a), q(a)=varphi(a)/Phi(-a), k=t/q,
b=k', l=b', f=k(1+b), alpha=3/40, s=40/37, beta=7/25,
c=3/2, gamma0=3/4, epsilon=3/20, kappa=49/100,
p=f'-b^2-l^2/alpha, e=f'-2b^2-2l^2/alpha,
and h0=f-ck-2(b-beta)l/alpha.

The hypotheses give a smooth convex gradient transport with bounded
symmetric A, J=q(A), and E A=0. Since q is positive and continuous,
bounded A bounds J above and away from zero. The pushforward identity
and change of variables give the density equation. Lemma 2.4 justifies
its differentiated versions by compact cutoffs and gives Gaussian H1
regularity of A and k(A). Entropy change of variables and
log q(a)=-a^2/2-log(2*pi)/2+t(a) give
D=2m+log det C-2H=E tr(A^2-2t(A))+log det C+m.

Put X_r=E(x_r A), Y=A-sum_r x_r X_r, B=sum_r X_r^2,
Z_r=partial_r A, G_r=partial_r Y, g_r=partial_r N^{-1}Y,
and V0=||G||^2-||Y||^2. The X_r are symmetric, so B is positive
semidefinite; it is not assumed positive definite. The zero mean and
first-chaos subtraction put Y in Gaussian chaoses of degree at least two.
Thus partial* g=Y. Covariance completion (Lemma 3.2) gives
C=W+E(2t-k^2-sum_r K_r^2), K_r=partial_r k(A),
where W is the H^{-1} row Gram matrix of U=q-(Id+N)k. For any
representation U=u-partial* v its weighted trace is at most
||u||_S^2+||v||_S^2. Proposition 2.5 supplies the eigenvalue separation
surplus Csep in E tr k^2 >= ||Z||^2-||K||^2+Csep.

Let S=((37/40)I+(3/40)B)^{-1}, T=S-I, Hmat=-T(B-I),
and rho=(3/20)I+(49/100)(37/40)S. The log-determinant supporting
plane and covariance completion imply equation (3.10), the paper's
reduction of D to -V0-Csep plus matrix terms.

Use D_r=K_r-X_r b and L_r=partial_r b-X_r l. The identity
q-k=ab-l gives U=Yb+sum X_r L_r+(B-I)l-partial* D.
Lemma 3.3 expands the covariance bound with all factor orders retained.
Lemma 3.4 controls the commutator and its compensating quadratic term
by (1+s/8)||D-gamma0*g||^2. Block Cauchy--Schwarz bounds the
remaining S square, and weighted completion reserves -E tr(Hmat rho p).
The resulting scalar absorption expression is
Rabs=tr(T-log S)-E tr(Hmat rho p(A))
 +s E tr(Y^2 ((b-beta)^2+alpha*h0^2/(4(1-epsilon-kappa)p))(A)).
The other terms are the derivative residual squares in (3.23).

Proposition 3.5 proves
Rabs <= (69/500)||Y||^2 - (1/1000) sum_i omega(lambda_i(B)).
It uses the averaged spectral measure of A along each B eigenvector,
whose first two moments are 0 and lambda_i+E||Y v_i||^2, and a
quadratic minorant of p. The logarithmic supporting-plane cost is
absorbed while keeping exactly omega, including its cutoff 13/100 at
lambda=0. No simultaneous diagonalization of A and B is used.

Proposition 3.6 bounds the remaining derivative residual squares,
entrywise in an eigenbasis of A and averaged over transposed entries,
by sum Q(G,g-G/2)+Csep, where
Q(u,v)=(43/100)u^2+(26/100)uv+(68/25)v^2.
The separation surplus cancels. On chaos degree d>=2, g=G/d and
||G||^2=d||Y||^2. The exact scalar factorization already proved in
Submission.Lib.EntropyTools.Remainder gives
sum Q(G,g-G/2) <= V0-(7/50)||Y||^2.
Therefore D <= ((69/500)-(7/50))||Y||^2-Omega/1000
= -||Y||^2/500-Omega/1000, proving the frozen conclusion.

The six interfaces below cover these paper steps. The Lean glue combines
them by definitional substitution and ordered-ring arithmetic. No analytic
child is claimed proved by this submission.

## Final six-child interfaces

The final cut separates the two-eigenvalue certificate from matrix algebra:

1. `Entropy.transport_energy_surplus` is Lemma 2.4 and Proposition 2.5.
   It gives entrywise L2 derivatives Z=partial A and K=partial k(A),
   and ||Z||^2-||K||^2+Csep
