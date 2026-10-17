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
where sigma is precisely the frozen polynomial in the logarithmic
separation, including its right-continuous step coefficient.

Here is the proof of that deduction. For equal endpoints all increments
vanish, so the local surplus suffices. Otherwise order the endpoints.
Complete squares against ell*G^2+.75*(g-G/2)^2 to bound each endpoint by
Q plus Z^2 times the increment norm in (4.10). The derivative of the
increment vector in xi=log q is chi*(1,z,hstar-2*b_j-2*L_j*z).
Use the coefficient and derivative tables to bound this norm, by the
finite affine-box computations of (4.15). Gaussian hazard identities,
including 0<=1-q(q-a)<=(q-a)^2, compare the mean logarithmic distances:
1/2<=u_-<=1/2+delta/12 and u_-^2+u_+^2<=(1+delta^2/36)/2.
Minkowski and averaging reduce the claim to the threshold (4.18).
For lower endpoints in R,U,V,T its constant lower bound suffices. For P
use the 1.62 logarithmic segment and split delta at 4 and 5. For O use
t_j^2<=a^2+2*delta, the improved negative-segment cost, the segment of
length 4 when crossing -1, and Theta_0(delta)>=.25+.00260*delta^2 for
delta>=4. The final T endpoint uses the gap 6.5. These are the exhaustive
cases in Section 4.2. Smoothness of k, continuity and positivity of q
follow from the Gaussian density/CDF identities and are included in this
child's output for the functional-calculus bridge.

## Matrix bridge and final glue

The fifth child is a general bridge: k is any smooth real function and q
is any positive continuous real function. Assume p>0 and the preceding
scalar pair inequality for these functions. Let A be a smooth bounded
symmetric matrix field with L2 derivatives, and let X_r be any constant
symmetric matrices. Put Y=A-sum x_r X_r. No first-chaos or mean-zero
hypothesis is needed for this bridge. Let g_r be any symmetric L2 family.
It yields exactly PB<=QE+sep in the frozen notation.

To prove it, work pointwise in an orthonormal eigenbasis of A. The
finite-dimensional divided-difference derivative formula gives
(partial_r v(A))_ij=v[a_i,a_j]*(Z_r)_ij. The derivative of Y is Z_r-X_r.
Consequently the entries of D,L,M are the three scalar residuals above.
Right multiplication by p(A)^(-1/2) divides the squared M_ij entry by
p(a_j). The entries of G,g,Z are symmetric. Summing over ordered pairs
therefore equals summing the arithmetic means of the two endpoint costs.
Apply the scalar inequality, and use orthogonal invariance of the
Frobenius square and mixed inner product to return Q to fixed coordinates.

Bounded A places all spectra in a fixed compact interval. Smooth scalar
functions and positive p give bounded divided differences and bounded
p^-1/2 there, so every residual is L2 and every energy is integrable.
The separation coefficient is a bounded Borel function on that compact
square. Its finite spectral-projector sum is basis independent, including
within repeated eigenspaces, and is measurable. It is bounded by a
constant times the squared Frobenius norm of Z, hence integrable. Thus
integrate the pointwise inequality and commute finite sums and integrals.
No eigenvector is differentiated or assumed to vary continuously.

Finally use the three certificate children to obtain C on the real line,
apply the fourth child, and pass its smoothness and pair inequality to
the bridge. For the frozen choice X_r=E[x_r A], symmetry follows entrywise
from symmetry of A and equality of the integrands. The bridge conclusion
is the frozen PB bound; p>0 is already a component of C. This proves both
parts of the requested conjunction. All substantial analysis resides in
the children; the Lean glue performs only these substitutions and cases.

## Local validation

All five closed child types elaborate in an otherwise independent file
importing only Mathlib and ChallengeDeps, with autoImplicit disabled.
The frozen-type schema prohibits let-bindings written with :=, so these
are encoded as applied lambdas; the owned Interfaces module provides
readable definitionally equal abbreviations for the glue. The bridge
shares its scalar bindings between hypothesis and conclusion and stays
within the gate's 4000-character bound. lot sync reports no similar
obligations for any of the five children.

The main module builds against the five generated child stubs. Its axiom
audit lists exactly these five child theorems and propext, Classical.choice,
and Quot.sound. Every child is used: the three domains cover R; the secant
child consumes their aggregate; the bridge supplies the integrated bound.
The original frozen theorem statement is unchanged. These are local checks
of interfaces and glue, not proofs of the analytic children or gate acceptance.

lot check returned code 4 with its expected split-mode message: glue
importing proposed child stubs is checked by lot submit split. It synced
the latest lib and again found no similar obligations. No proof-check
acceptance is claimed from that response.
