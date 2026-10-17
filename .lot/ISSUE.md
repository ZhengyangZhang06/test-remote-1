# o032: Entropy.two_eigenvalue_negative_certificate

Type: `(fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (C : ℝ → Prop) => ∀ a : ℝ, a ≤ -6 → C a) (((fun (b : ℝ → ℝ) => (fun (l : ℝ → ℝ) => (fun (f : ℝ → ℝ) => (fun (p : ℝ → ℝ) => (fun (e : ℝ → ℝ) => (fun (Q : ℝ → ℝ → ℝ) => (fun (D : ℝ → ℝ) => (fun (L : ℝ → ℝ) => (fun (E : ℝ → ℝ) => (fun (eta : ℝ) => (fun (nu : ℝ) => (fun (row : ℝ → (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)) => fun a : ℝ => (fun R => (fun z => 0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧ (R.1 ≤ b a ∧ b a ≤ R.2.1 ∧ L a ≤ R.2.2.1 ∧ D a ≤ R.2.2.2.1 ∧ R.2.2.2.2.1 ≤ D a * E a ∧ D a * E a ≤ R.2.2.2.2.2.1 ∧ D a * (3/2) * b a ≤ R.2.2.2.2.2.2.1) ∧ (∀ u v : ℝ, ((82/37)*(b a)^2 - eta*b a + nu/4 + (40/3)*(l a)^2)*u^2 + 2*(nu/2 - eta*b a)*u*v + nu*v^2 + D a*(E a*u + (3/2)*b a*v)^2 + R.2.2.2.2.2.2.2*u^2 + (3/4)*v^2 ≤ Q u v) ∧ (if a < -1 then -(2/25) ≤ z ∧ z ≤ 7/10 ∧ l a / (q a-a) ≤ 7/100 else -(19/40) ≤ z ∧ z ≤ 0 ∧ l a / (q a-a) ≤ 97/1000) ∧ 4/5 ≤ 1+3*b a+k a*z ∧ 1+3*b a+k a*z ≤ 177/100) (deriv l a / l a)) (row a)) (fun a => if a < -3 then (0, 9/100, 3/5, (59/200)*(7+a^2), 37/100, 14/25, 18/25, 13/100) else if a < -2 then (83/1000, 3/20, 101/100, 43/10, 29/100, 23/50, 18/25, 13/100) else if a < -1 then (7/50, 23/100, 119/100, 3, 29/100, 371/1000, 17/25, 13/100) else if a < 1/2 then (11/50, 171/500, 119/100, 43/25, 29/100, 199/500, 61/100, 123/1000) else if a < 4 then (337/1000, 9/20, 83/100, 87/100, 31/100, 2/5, 1/2, 3/50) else (89/200, 1/2, 1/5, 16/25, 8/25, 2/5, 12/25, 11/500))) ((40/37)*(7/25)^2 + (45/37)*(3/4)^2)) ((40/37)*(7/25) + (42/37)*(3/4))) (fun a => e a + (3/4)*b a)) (fun a => (40/3) * l a)) (fun a => (5/17) / p a)) (fun u v => (43/100)*u^2 + (26/100)*u*v + (68/25)*v^2)) (fun a => deriv f a - 2*(b a)^2 - (80/3)*(l a)^2)) (fun a => deriv f a - (b a)^2 - (40/3)*(l a)^2)) (fun a => k a * (1 + b a))) (deriv b)) (deriv k)))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))`

Statement: The coefficient, local surplus and derivative certificates of Lemma 4.1 hold on the full negative tail a<=-6.

Role in the glue of o017: Supplies the certificate below the central interval, using negative Gaussian excess-moment asymptotics.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__two_eigenvalue_negative_certificate.lean

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
