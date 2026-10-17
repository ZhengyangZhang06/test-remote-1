# Proof of the linear transport limit and proposed cuts

Write E = EuclideanSpace R (Fin m), gamma = stdGaussian E, and
|M|_F^2 = sum_i sum_j (M i j)^2. All matrix energies below are these
explicit Frobenius sums, not the default norm on matrices.

## Finite-dimensional extraction

For real Hermitian coefficients, symmetry gives
sum_r |X_nr|_F^2 = trace(sum_r X_nr * X_nr).
The right side converges to m and is bounded. Thus the whole finite
coefficient array is bounded in a finite-dimensional real space. Extract
a strictly increasing subsequence sigma on which the array converges to
X. Hermitian symmetry is closed and matrix multiplication and finite sums
are continuous, so every X_r is Hermitian and sum_r X_r * X_r = I.
The owned Compactness.lean helper implements this step. Its original
proof was written by x0027 (2912f26, reported 2026-10-17T06:34Z) and
merged into this branch. It uses finite-dimensional compactness and no
unaccepted module. Earlier posts reported the same result in x0007's
EntropyMatrix candidate, but that source/package was unavailable here;
no dependency on that candidate remains.

Replace F_n, A_n, X_n by their sigma subsequences. The residual energies
still tend to zero since a strictly increasing map N -> N tends to infinity.

## Proved-helper step: convergence of the functional-calculus fields

Let L_n(x) = sum_r x_r X_nr, L(x) = sum_r x_r X_r,
J_n(x) = cfc q (A_n(x)), and J(x) = cfc q (L(x)). The assumed Frobenius
contraction on Hermitian matrices makes the map U -> cfc q U continuous
on that closed subspace; no independent regularity assumption on q is
needed. Linear combinations of the X_r are Hermitian, so J is continuous.
The same contraction against zero bounds |cfc q U|_F by |U|_F plus the
fixed finite value |cfc q 0|_F. For J_n, the implemented proof also reads its entries from DF_n on
coordinate basis vectors; the C1 hypothesis makes them continuous
directly. Thus all entries of J_n and J are Gaussian L2 functions.

Gaussian coordinate orthogonality gives
 integral |L_n - L|_F^2 dgamma = sum_r |X_nr - X_r|_F^2 -> 0.
The checked helper uses the sufficient Cauchy-Schwarz bound
 integral |L_n-L|_F^2 <= (integral ||x||^2 dgamma)
                         * sum_r |X_nr-X_r|_F^2;
this requires only the finite Gaussian second moment.
The pointwise inequality
 |J_n - J|_F^2 <= |A_n - L|_F^2
                 <= 2 |A_n - L_n|_F^2 + 2 |L_n - L|_F^2
then proves integral |J_n-J|_F^2 dgamma -> 0. Every energy here is
integrable: each A_n entry is L2 by hypothesis and Gaussian coordinates
have finite second moments. This integrability is essential, since the
Bochner integral convention alone would not measure a nonintegrable
nonnegative residual correctly. This step contains no map convergence,
subsequence extraction, or normalization of X.

## Child 1: a Gaussian derivative-to-function L2 bound

This child asks only for a finite positive Gaussian Poincare constant:
for each m there is C>0 such that every centered C1 map h with
h and Dh in Gaussian L2 satisfies integral ||h||^2 <= C integral ||Dh||^2.
The L2 completeness and centering consequence is proved in the owned
L2Limit.lean helper from x0027 (15b7450, reported 06:31Z). In both child
types the derivative is a continuous linear endomorphism and the norm
is its operator norm. For such a derivative D, |D|_F^2 <= m ||D||^2;
therefore operator-norm L2 convergence implies entrywise/Frobenius L2
convergence. The proved entriesCLM bridge converts the Frobenius
convergence above into operator-norm convergence. Assume C1
maps H_n are centered and in L2(gamma), their derivative matrices J_n
have L2 entries, and J_n converge to an L2 matrix field J. There is a
centered L2 function H with integral ||H_n-H||^2 dgamma -> 0.

For each difference H_n-H_k, the Gaussian Poincare inequality is
 integral ||H_n-H_k||^2 dgamma <= integral |J_n-J_k|_F^2 dgamma.
The right side is at most 2m integral ||J_n-J||^2 plus
2m integral ||J_k-J||^2, and hence tends to zero. The classes of H_n
are Cauchy in L2(gamma; E). Completeness supplies an L2 class and a
strongly measurable representative H. Continuity of the integral on
this probability L2 space preserves its zero mean. The child isolates the substantial Gaussian derivative-to-function
estimate. The completeness consequence is already checked helper
code, and does not impose continuity on J.

The sharp Poincare constant is not needed by this child. A direct
rotation proof gives a sufficient finite constant and avoids developing
the Mehler semigroup. Take independent standard Gaussian vectors x,y and
put z_t = cos(t)x + sin(t)y, w_t = -sin(t)x + cos(t)y for 0 <= t <= pi/2.
For each t, (z_t,w_t) has the same product Gaussian law as (x,y), by
orthogonal invariance. The fundamental theorem of calculus along this
smooth curve gives
 h(y)-h(x) = integral_0^(pi/2) Dh(z_t) w_t dt.
Cauchy-Schwarz in t and Tonelli give
 E||h(y)-h(x)||^2 <= (pi/2)^2 m E||Dh||_op^2,
since z_t and w_t are independent and E||w_t||^2=m. Jensen applied to
the y average, using the zero mean of h, gives
 E||h(x)||^2 <= E||h(y)-h(x)||^2.
Thus the positive nonsharp bound with C_m = 1 + pi^2 m/4 suffices in place
of Poincare: the Cauchy estimate above becomes 2 C_m times the two
Jacobian errors. All joint integrals are justified by nonnegativity
and the L2 derivative hypothesis; along each fixed path the derivative
is continuous. For m=0 the domain and codomain are singletons and the
conclusion is immediate. The pinned Mathlib has orthogonal Gaussian
invariance as ProbabilityTheory.stdGaussian_map and the finite-product
model as ProbabilityTheory.map_pi_eq_stdGaussian. Provers can choose
this elementary finite-constant route, or the usual Gaussian Poincare
inequality and L2 completeness.

## Child 2: a continuous limiting Jacobian has a C1 representative

This cut assumes C1 maps H_n converge to an L2 function H, and their
classical Jacobians converge in Gaussian L2 to a continuous matrix field
J. It concludes that H has an almost-everywhere equal global C1
representative G with derivative matrix J.

On each compact ball, the Gaussian density is continuous and bounded
below by a positive number, so Gaussian L2 convergence implies local
Lebesgue L2 convergence, for both maps and derivative entries. Passing
to the limit in integration by parts against compactly supported smooth
test functions proves that J is the weak derivative of H. Local
mollification now gives smooth H_epsilon with derivatives J_epsilon.
The derivatives converge uniformly on smaller compact balls because J
is continuous, while the functions converge locally in L2. Fix the
additive constant by an average on a ball. Uniform convergence of the
derivatives and convergence of this average imply uniform convergence
of the functions there, yielding a C1 representative with derivative
J. Representatives obtained on overlapping balls agree almost
everywhere and therefore everywhere by continuity and the positive
Lebesgue measure of nonempty balls. They glue to a global C1 map G.
This is independent of Gaussian Poincare, centering, functional
calculus, and matrix normalization.

## Assembly

Apply finite-dimensional extraction and the field-convergence helpers on the subsequence.
The given derivative identity identifies its J_n with the actual
Jacobians. Child 1 and L2Limit.lean produce a centered L2 limit H; Child 2 replaces it by
a C1 representative G. Almost-everywhere equality preserves MemLp,
the zero integral, and every squared-distance integral. Return sigma,
G and X, with the Hermitian and normalization conclusions supplied by
extraction. These steps are exactly the frozen conclusion of o010.

The proposed two new children have disjoint analytic responsibilities:
the Gaussian Poincare inequality and the local C1
representative theorem. The Fields.lean helpers merged from o010 branch
x0027 (1bd15a0, reported 2026-10-17T06:22Z) already prove continuity,
MemLp and coefficient-to-field convergence. The Energy.lean bridge
from the same branch at b9de5a1 (reported 06:25Z) proves convergence
of the actual derivatives in the operator-norm squared L2 energy. All child
types are closed propositions using only Mathlib and ChallengeDeps.
Both types have been compiled in the generated stub context.
The split asks the gate to validate this conditional assembly; the two
new analytic theorems remain proof obligations after the split.
