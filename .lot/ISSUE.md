# o035: Entropy.two_eigenvalue_matrix_bridge

Type: `∀ k q : ℝ → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) k → Continuous q → (∀ a : ℝ, 0 < q a) → (fun (b : ℝ → ℝ) => (fun (l : ℝ → ℝ) => (fun (f : ℝ → ℝ) => (fun (p : ℝ → ℝ) => (fun (e : ℝ → ℝ) => (fun (Q : ℝ → ℝ → ℝ) => (fun (delta : ℝ → ℝ → ℝ) => (fun (sigma : ℝ → ℝ → ℝ) => (∀ a : ℝ, 0 < p a) → ((fun (dd : (ℝ → ℝ) → ℝ → ℝ → ℝ) => (fun (dk : ℝ → ℝ → ℝ) => (fun (db : ℝ → ℝ → ℝ) => (fun (psi : ℝ → ℝ → ℝ) => (fun (H : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) => ∀ a c G g Z : ℝ, (H a c G g Z + H c a G g Z)/2 ≤ Q G (g-G/2) + sigma a c*Z^2) (fun a c G g Z => (40/37)*(G*b c + Z*dk a c - (7/25)*g)^2 + (42/37)*(G*b c + Z*dk a c - (3/4)*g)^2 + (27/592)*g^2 + (40/3)*(G*l c + Z*db a c)^2 + (5/17)*(G*e c + Z*psi a c + (3/2)*g*b c)^2 / p c)) (fun a c => dd f a c - deriv f c - 2*b c*dk a c - (80/3)*l c*db a c)) (fun a c => dd b a c - l c)) (fun a c => dd k a c - b c)) (fun v a c => if a = c then deriv v c else (v a - v c)/(a-c))) → ∀ m : ℕ, 1 ≤ m → ∀ A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun gamma => (fun I => (fun L2 => (fun d => (fun Z => (fun K => ∀ X : Fin m → Matrix (Fin m) (Fin m) ℝ, (∀ r, (X r).IsHermitian) → (fun Y => (fun U => (fun sep => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → ∀ g : Fin m → (EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ), (∀ r x, (g r x).IsHermitian) → (∀ r, L2 (g r)) → (fun N => (fun Dr => (fun Lr => (fun Mr => (fun PB => (fun G => (fun QE => PB ≤ QE + sep) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => Q (G r x i j) (g r x i j - G r x i j / 2))))))) (d Y)) (Finset.sum Finset.univ (fun r : Fin m => (40/37)*N (fun x => Dr r x - (7/25 : ℝ) • g r x) + (42/37)*N (fun x => Dr r x - (3/4 : ℝ) • g r x) + (27/592)*N (g r) + (40/3)*N (Lr r) + (5/17)*N (fun x => Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x))))) (fun r x => d (fun y => cfc f (A y)) r x - X r * cfc (deriv f) (A x) - 2 • (Dr r x * cfc b (A x)) - (80/3 : ℝ) • (Lr r x * cfc l (A x)) + (3/2 : ℝ) • (g r x * cfc b (A x)))) (fun r x => d (fun y => cfc b (A y)) r x - X r * cfc l (A x))) (fun r x => K r x - X r * cfc b (A x))) (fun F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (I (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => sigma ((hA x).eigenvalues i) ((hA x).eigenvalues j) * ((U x).transpose * Z r x * U x) i j ^ 2)))))) (fun x => ((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))) (fun x : EuclideanSpace ℝ (Fin m) => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (d (fun x => cfc k (A x)))) (d A)) (fun (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 gamma)) (MeasureTheory.integral gamma)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun a c => (1 + (if min a c < -3 then 0 else if min a c < -2 then 19/100 else if min a c < -1 then 38/100 else 68/100)) / 16 * (1 + (delta a c)^2/30 + (delta a c)^4/1680) * (delta a c)^2)) (fun a c => Real.log (q a) - Real.log (q c))) (fun u v => (43/100)*u^2 + (26/100)*u*v + (68/25)*v^2)) (fun a => deriv f a - 2*(b a)^2 - (80/3)*(l a)^2)) (fun a => deriv f a - (b a)^2 - (40/3)*(l a)^2)) (fun a => k a * (1 + b a))) (deriv b)) (deriv k)`

Statement: For arbitrary smooth k and positive continuous q, positivity of p and the scalar two-endpoint estimate imply the integrated matrix residual bound for any smooth bounded symmetric A and any constant symmetric family X.

Role in the glue of o017: Lifts the scalar estimate through matrix CFC derivatives, transposed-entry pairing, basis invariance, and integration; instantiated with X_r=E[x_r A].

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__two_eigenvalue_matrix_bridge.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof and proposed decomposition of o017

This decomposition follows Proposition 3.6, Section 4.2, and Appendix A of
the supplied paper. It separates three disjoint certificate domains from
the two-endpoint argument and from the matrix functional-calculus bridge.
All decimals in this note stand for exact rationals. Nothing below is a
claim that an analytic child has already been formally proved.

## Scalar definitions

Put q(a)=phi(a)/Phi(-a), t(a)=-log Phi(-a), k=t/q,
b=k', l=b', f=k(1+b), p=f'-b^2-(40/3)l^2, and
e=f'-2b^2-(80/3)l^2. Put alpha=3/40, c=3/2,
s=40/37, beta=7/25, gamma=3/4, Dstar=5/17,
Astar=82/37, eta=s*beta+(42/37)*gamma,
nu=s*beta^2+(45/37)*gamma^2. Define
D=Dstar/p, L=(40/3)l, E=e+gamma*b, K0=D*E, J0=D*c*b.
The scalar quadratic form is Q(u,v)=(43/100)u^2+(26/100)uv+(68/25)v^2.

The certificate C(a) asserts p>0, 0<b<1/2, l>0, the six rows of the
coefficient table in Lemma 4.1, the local quadratic surplus, and the two
rows of its derivative table. The bins are selected by strict upper
cutoffs -3,-2,-1,1/2,4, so a boundary uses the row on its right.
Writing ell for .13,.13,.13,.123,.060,.022 in these bins, the local
surplus says, for every u,v, that the quadratic form in (4.3) is bounded
by Q(u,v)-ell*u^2-.75*v^2. This scalar formulation is exactly the
positive-semidefinite matrix assertion, with no matrix convention needed.
The derivative table uses z=l'/l, hstar=1+3*b+k*z, chi=l/(q-a).

## Certificate domains

1. On [-6,10], construct the eleven degree-14 polynomial pairs from the
rational seeds in Appendix A, certify their ODE residuals and joining
errors, and anchor q at 10 and k at -6 using alternating Mills bounds.
The equations q'=q(q-a) and k'=1-k(q-a) propagate errors stably in
opposite directions. They give uniform errors 1e-8 and 8e-7. Construct
b,l,l' from the full polynomials before quartic truncation. Charge all
discarded coefficients to the enclosure error. Bernstein coefficients on
each half of [-1,1] prove groups G1--G4, hence C(a). The same enclosures
and the logarithm series give the four logarithmic gaps used in Section
4.2: log(q(-1)/q(-2))>1.62, log(q(-1)/q(-3))>4,
log(q(4)/q(-2))>4, and log(q(4)/q(-3))>6.5.

2. On a<=-6, write r=-a and I_j=integral_0^infty v^j exp(-rv-v^2/2).
Gaussian tail integration and the differential identities bound the
errors in k,b,l,l' by .01*r^-2*j!/r^(j+1). Compare I_j with the first two
Taylor terms of exp(-v^2/2). The resulting inverse-power bounds give
p>=1/(7+r^2), the O-row coefficient bounds and derivative bounds. For the
local surplus, bound the three entries of N as in Appendix A; the
leading minor and determinant of Q-N-diag(.13,.75) are positive.

3. On a>=10, put u=a^-2 and theta=log(a*sqrt(2*pi)). Write
k=a/2+C(u,theta)/a using F(u)=integral_0^infty exp(-v-u*v^2/2).
Differentiate under the integral and use the Euler-operator remainder
bounds in Appendix A. They give the explicit B,J,R enclosures and
b=.5-uB, l=J/a^3, l'=-R/a^4. These imply the T-row coefficient and
derivative bounds, p>.493, and the two positive minors for the local
surplus. The exponential change of variable log(a/10) makes every
unbounded-domain remainder estimate an elementary uniform inequality.

These three children cover all real a. The compact child also supplies
the four fixed logarithmic gaps. No tail condition is inferred by sampling.

## Two-endpoint estimate

For any smooth v define v[a,c] by its secant slope when a!=c and v'(a)
when a=c, and Delta v[a,c]=v[a,c]-v'(c). Define
psi[a,c]=Delta f[a,c]-2*b(c)*Delta k[a,c]-(80/3)*l(c)*Delta b[a,c].
At endpoint c, the residuals are
D_c=G*b(c)+Z*Delta k[a,c], L_c=G*l(c)+Z*Delta b[a,c],
M_c=G*e(c)+Z*psi[a,c]+(3/2)*g*b(c).
Let H(a,c,G,g,Z) be the sum of the five endpoint squares with weights
40/37,42/37,27/592,40/3,5/17, with the last square divided by p(c).
The fourth child deduces from C and the four gaps that
(H(a,c,G,g,Z)+H(c,a,G,g,Z))/2
 <= Q(G,g-G/2)+sigma(a,c)*Z^2,
where sigma is precisely the frozen polynomial in the loga
