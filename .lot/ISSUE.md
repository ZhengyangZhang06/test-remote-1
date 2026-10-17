# o028: Entropy.transport_integrated_multiplier

Type: `∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) => (fun (L2 : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Prop) => (fun (d : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (J : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (ka : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (H : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (Z : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (K : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (I : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (N : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → ℝ) => (fun (R : (EuclideanSpace ℝ (Fin m)) → ℝ) => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ V φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V → (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖^2) → ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → (∀ i j : Fin m, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => z x * (-(if i = j then 1 else 0) + (J x * Matrix.of (fun u v => (fderiv ℝ (fderiv ℝ V) (gradient φ x) (PiLp.single 2 u (1 : ℝ))) (PiLp.single 2 v (1 : ℝ))) * J x) i j + Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) = -Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => I (fun x => fderiv ℝ z x (PiLp.single 2 s (1 : ℝ)) * (J x)⁻¹ s r * H r x i j)))) → (∀ r, L2 (H r)) → (∀ r, L2 (K r)) → MeasureTheory.Integrable R γ ∧ I R ≤ N ka) (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (ka x * ka x) i j * Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) + Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => (J x)⁻¹ r s * Matrix.trace ((K s x * ka x + ka x * K s x) * H r x))))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (MeasureTheory.integral γ)) (d ka)) (d A)) (d J)) (fun x => cfc k (A x))) (fun x => cfc q (A x))) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))`

Statement: Given the weak Jacobian equation and finite Jacobian and k(A) energy, testing it with k(A)^2 gives an integrable fixed-coordinate multiplier density R and E R <= E ||k(A)||_F^2.

Role in the glue of o018: Provides the upper bound for the common multiplier integral; its integrability is used in the spectral lifting.

Depends on: o027
Weight: 5
Module: Submission/Obl/Entropy__transport_integrated_multiplier.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof of o018: transport energy and separation surplus

This proof follows Lemma 2.4 and Proposition 2.5 of the supplied informal
paper. The cut separates global transport analysis from scalar inequalities
and from the spectral matrix calculation. It does not use mean zero of A.
The four closed propositions in split.json expand every definition using only Mathlib and ChallengeDeps.

Write gamma for standard Gaussian measure, E for its integral, q(a) for the
Gaussian hazard, t(a)=-log Phi(-a), k=t/q, J=q(A), and ka=k(A). Write
J_r=partial_r J, Z_r=partial_r A, K_r=partial_r ka. All matrix products
below retain their indicated order. A squared norm means the sum of the
squares of all entries, integrated against gamma.

## 1. Finite energy

Bounded A and positive smooth q bound the eigenvalues of J in a compact
interval [lambda,Lambda] contained in (0,infinity). The Hessian identity
J=D²phi makes grad phi uniformly strongly monotone and globally Lipschitz,
so it is a smooth global diffeomorphism. Its pushforward identity gives
log det J=V(grad phi)-|x|²/2-(m/2)log(2*pi).

Twice differentiating this equation and using symmetry of third and
fourth derivatives yields
L J_ij=-delta_ij+(J D²V(grad phi) J)_ij
             +tr(J^-1 J_i J^-1 J_j),
where L u=tr(J^-1 D²u)-grad V(grad phi) dot grad u.
The Hessian cofactor divergence identity identifies L with Gaussian
weighted divergence of J^-1 grad u. Thus compactly supported tests obey
E(v L u)=-E(grad v dot J^-1 grad u).

Tracing the equation and using D²V >= 0 gives
L tr J >= -m+Lambda^-2 sum_r |J_r|².
Test against chi_R², where 0<=chi_R<=1 are smooth compact radial cutoffs
converging to one, with |grad chi_R|<=C/R. Cauchy--Schwarz and Young's
inequality absorb half the derivative term and leave a bound independent
of R. Fatou proves entrywise L2 of all J_r. Bounded derivatives of the
spectral maps q^-1 and k composed with q^-1 on [lambda,Lambda] then give
entrywise L2 of Z_r and K_r. The first child also exports the weak
Jacobian equation just proved: for every smooth compactly supported z,

E[z*(-delta_ij+(J D²V(grad phi) J)_ij
               +tr(J^-1 J_i J^-1 J_j))]
 = -sum_r,s E[(partial_s z)(J^-1)_sr (J_r)_ij].

Thus the next child need not reconstruct change of variables or the
cofactor divergence identity.

## 2. The integrated matrix multiplier

Set P=ka*ka and P_s=K_s*ka+ka*K_s. Define the fixed-coordinate density

R(x)=sum_i,j P_ij tr(J^-1 J_i J^-1 J_j)
   +sum_r,s (J^-1)_rs tr(P_s J_r).

Apply the compact-test integration by parts identity to the Jacobian
equation with multiplier P and pass to the limit through cutoffs.
Every coefficient built from J, J^-1 and ka is bounded. Both displayed
quadratic derivative terms are integrable by the finite-energy result.
The cutoff error tends to zero by Cauchy--Schwarz. The term
tr(P J D²V(grad phi) J) is nonnegative since P and J commute and P>=0.
Dropping it proves E R <= E tr(ka²)=||ka||². This is the second child, assuming the weak equation rather than a
pushforward identity; it has no scalar logarithmic-average estimate or eigenvalue surplus.

## 3. The scalar secant comparison

For a scalar f, write f[a,b]=(f(a)-f(b))/(a-b) when a!=b and f'(a)
when a=b. Put d=q-a, b=k', and define

B(a,b)=(q(a)k(a)²-q(b)k(b)²)/(q(a)-q(b))  (a!=b),
B(a,a)=k(a)²+2 k(a) k'(a)/d(a).

This B is the arithmetic average in lambda=q(a) of
M=(1-(k')²)/d², because (lambda*k(q^-1(lambda))²)'=M.
The needed scalar conclusion is that B is symmetric and monotone in
each endpoint, and that

1-k[a,b]²+sigma(a,b)
 <= q[a,b]² * B(a,b)/(q(a)q(b)),

where sigma is exactly the parent statement's right-continuous step
coefficient times delta², with delta=log q(a)-log q(b).

Here is the proof, including where the quantitative certificate enters.
The scalar bounds 0<k'<1/2, k''>0, and M'/(M*d)>=m0(a) follow from the
paper's analytic tail and rational compact-interval certificates. They
imply monotonicity of B. In logarithmic lambda coordinates let a bar
mean a uniform a
