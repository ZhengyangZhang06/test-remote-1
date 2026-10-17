# o029: Entropy.hazard_secant_surplus

Type: `∀ a b : ℝ, (fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (DD : (ℝ → ℝ) → ℝ → ℝ → ℝ) => (fun (B : ℝ → ℝ → ℝ) => (fun (δ : ℝ → ℝ → ℝ) => (fun (σ : ℝ → ℝ → ℝ) => B a b = B b a ∧ (a ≤ b → ∀ c : ℝ, B a c ≤ B b c) ∧ 1 - (DD k a b)^2 + σ a b ≤ (DD q a b)^2 * B a b / (q a * q b)) (fun a b : ℝ => (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100 else if min a b < -1 then 38/100 else 68/100)) / 16 * (1 + (δ a b)^2/30 + (δ a b)^4/1680) * (δ a b)^2)) (fun a b : ℝ => Real.log (q a) - Real.log (q b))) (fun a b : ℝ => if a = b then k a ^ 2 + 2 * k a * deriv k a / (q a - a) else (q a * k a ^ 2 - q b * k b ^ 2) / (q a - q b))) (fun (f : ℝ → ℝ) (a b : ℝ) => if a = b then deriv f a else (f a - f b) / (a - b))) (fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))`

Statement: The arithmetic M-average B between q(a) and q(b) is symmetric and monotone in each a endpoint, and its q-divided-difference weight dominates 1-k[a,b]^2 plus the exact logarithmic-separation surplus, including the diagonal case.

Role in the glue of o018: Supplies the scalar symmetry, monotonicity and pair inequality to the matrix spectral comparison.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__hazard_secant_surplus.lean

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
