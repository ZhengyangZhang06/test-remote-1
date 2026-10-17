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
det Cov(W_j)=(det P_j)^2 det C_j. The two logarithmic shifts cancel
exactly in 2H-2m-log det C. Its nonnegative remainder is therefore
bounded by a sequence tending to zero. Separately bounding its two
nonnegative summands proves the required vanishing limits. This child
stops at these approximation data and does not classify any law.
The inequality Entropy.lower_bound is not used as a substitute for the
strict remainder, and no additional unproved normalization or
approximation result is hidden in the glue.

## 2. Gaussian hazard Lipschitz (Lemma 2.1) and proved spectral step

The new scalar child is |q(s)-q(t)|<=|s-t|. Let G be a standard
Gaussian and X_a the conditional law of G-a given G>a. Gaussian
integration by parts gives E X_a = q(a)-a > 0 and
Var X_a = 1-q(a)(q(a)-a) > 0; the latter is strict because this
conditional density is positive on an interval. Differentiating
q=phi/Phi(-a) gives q'=q(q-a), so 0<q'<1 everywhere. The denominator
Phi(-a) is positive, so all differentiation steps are legitimate.
The mean value theorem on the interval between s and t proves the
asserted Lipschitz estimate. This is the analytic scalar
input not covered by the finite-dimensional matrix helper.

The general matrix proof supplied by x0007 is included as the parent's
owned Frobenius.lean, with its original namespace and attribution
(origin/x0007 at c40b876). It builds locally and is checked with the
split; it is not being assumed as an unaccepted library theorem.
The glue applies cfc_entry_square_sum_le to the scalar child, so no
new child restates this matrix calculation. Its proof is exactly
Lemma 6.2: for symmetric M,N, use independent orthonormal eigenbases
u_i,v_k.
The (i,k) mixed matrix entry of q(M)-q(N) is
(q(lambda_i)-q(mu_k)) <u_i,v_k>; the entry of M-N is
(lambda_i-mu_k) <u_i,v_k>. Lemma 2.1 gives 0 < q' < 1.
Squaring the resulting scalar inequality and summing over i,k proves
|q(M)-q(N)|_F^2 <= |M-N|_F^2. Orthogonal invariance of the two sums
is used explicitly. The resulting estimate is passed to the compactness child.

## 3. Gaussian compactness and a linear Jacobian limit

Since sum_r |X_jr|_F^2 = trace(sum_r X_jr^2) -> m, extract a strictly
increasing subsequence along which all coefficient matrices converge
to symmetric X_r. They satisfy sum_r X_r^2 = I. Gaussian coordinate
orthogonality and the vanishing Y_j yield A_j -> A = sum_r x_r X_r
in L2(gamma). Step 2 implies DF_j -> q(A) in L2(gamma).
Gaussian Poincare applied to centered F_j-F_k makes the maps Cauchy
in L2(gamma). Their limit F has the indicated weak Jacobian, including
locally in Lebesgue measure because the Gaussian density is bounded
below on compact sets. The continuous field q(A) gives a C1
representative of F: mollify locally, or integrate the continuous
curl-free field on the simply connected space E; the resulting
primitive differs from the Sobolev limit by a constant. This is the
explicit bridge from the paper's weak Jacobian to the classical
Jacobian used in the frozen interface. It preserves centering,
Gaussian square integrability, and strong L2 convergence of the maps.
The interface states entrywise MemLp 2 for A_j, which in finite
dimension is equivalent to square integrability of its Frobenius norm.
It deliberately uses no Matrix norm instance: the Frobenius norm and
operator norm are not interchangeable in the sharp contraction estimate.
Matrix convergence is the ordinary finite product topology. Existence
of a C1 representative needs only continuity of q(A), which follows
from the assumed Frobenius contraction and linearity of A; the
compactness child is therefore valid for a general scalar function q
satisfying that matrix contraction hypothesis. No conclusion about the
law of F is part of this child.

## 4. Linear-Jacobian rigidity (Lemma 6.1)

For A(x) = sum_r x_r X_r, assume DF = q(A) and sum_r X_r^2 = I.
Commuting distributional derivatives gives (partial_r q(A))e_s =
(partial_s q(A))e_r. The analytic expansion near zero has nonzero
first and second derivatives q'(0)=2/pi and
q''(0)=sqrt(2/pi)(4/pi-1). The constant term therefore gives
X_r e_s = X_s e_r. The linear term, after this cancellation, gives
X_r X_s = X_s X_r. The coefficient algebra on branch x0007 at cc5a312 can be used in
proving this child: signed_coordinate_field combines coefficient
commutation, a common orthonormal eigenbasis, and rotation of the
coefficients. This is x0007's work reported in its 2026-10-17T05:50 post
and 05:51 direct message; the analytic derivation of its two compatibility
hypotheses remains part of this child.

Simultaneously diagonalize the commuting real symmetric coefficients
and rotate both input and output. Coefficient symmetry makes each
rotated coefficient supported on its corresponding diagonal entry;
the square sum makes that entry a sign sigma_i. Integrating gives
U^T F(Uy) = (sigma_i T(sigma_i y_i))_i + w. Independent Gaussian
coordinates are taken by T to independent mean-one exponentials.
The law of F is thus an affine exponential-product density, with
covariance I. The latter conclusion is retained, since it is needed
to control the possibly unbounded normalizers in the next step.

## 5. Return from normalized laws to the original density

The interface permits a strictly increasing subsequence sigma from
Step 3. Apply every convergence statement below along sigma; strict
monotonicity implies sigma(n)->infinity. The strong L2 convergence of
F_sigma(n) to F implies convergence of means and each raw second moment:
use |uv-u'v'| <= |u-u'||v| + |u'||v-v'| and Cauchy--Schwarz, with
bounded L2 norms following from convergence. The maps are centered,
so these raw second moments are their covariances.
By Step 4 its limit is I. The centered law identities give
D_j = P_j C_j P_j^T -> I. Choose c,C0,d,D>0 such that eventually
c I <= C_j <= C0 I and d I <= D_j <= D I. Congruence gives
(d/C0) I <= P_j P_j^T <= (D/c) I. Consequently all singular values
of P_j lie in a fixed compact interval in (0,infinity), bounding both
P_j and P_j^{-1}. Symmetry of P_j is not needed in this argument, so
the frozen interface asks only that P_j be a linear equivalence. Extract a further
subsequence converging to an invertible P. For each bounded continuous
psi, the difference between its integrals under the normalized f_j
and f is bounded by ||psi||_infinity ||f_j-f||_1 plus an integral
against f that tends to zero by dominated convergence. Thus
(P(x-b))_#(f dx) = F_#gamma. If the limiting law is the image of the standard exponential product
under y -> L0 y+a0, then the original law is its image under
 y -> (P^{-1} L0)y + (b+P^{-1}a0).
Thus take L=P^{-1} L0 and a=b+P^{-1}a0. Invertibility is preserved
under composition. Linear change of variables with the absolute
Jacobian and uniqueness of Radon--Nikodym densities give
 f(x)=|det L|^{-1} exp(-sum_i (L^{-1}(x-a))_i)
on the transformed nonnegative orthant, and zero off it, almost
everywhere. Nonnegativity of f makes ENNReal.ofReal injective on the
relevant values when passing from equality of measures to real-valued
densities. This is exactly the parent's formula, including orientation
reversal and arbitrary null-set changes.
This child assumes the normalized limit law and its covariance; it
uses no log-concavity or entropy equality assumption.

## 6. Exact moments and entropy of affine exponential products

Fubini and the gamma integrals integral_0^infinity t^k exp(-t) dt = k!
for k=0,1,2 give mass one, mean (1,...,1), covariance I, and entropy m
for the product density. For x=L y+a, Lebesgue change of variables
with |det L| gives entropy m+log|det L| and covariance determinant
(det L)^2. These identities remain valid for any almost-everywhere
equal density. Since det L is nonzero, log((det L)^2)=2log|det L|;
the parent's reverse implication is elementary real arithmetic.
This child proves the two explicit identities, not the equivalence.

## Glue and independence

The forward implication first applies the three reused theorems in
Assembly.lean and invokes the centering/vanishing-slack child in
Step 1, then uses Steps 2,3,4,5 in that order. The reverse
implication uses Step 6 and the logarithm identity. The six tasks are
separate analytic construction, scalar Gaussian estimate, Sobolev compactness,
local rigidity, affine measure compactness, and integration statements.
Equality and log-concavity are used only by the proved assembly glue
and the reused approximation theorem; the six new children isolate
the remaining specific analytic and integration claims. None restates the
parent equivalence. The JSON binds every object explicitly
using only Mathlib and ChallengeDeps, with no private vocabulary in
child types. The split check validates the interfaces and glue; it
does not prove these pending analytic children.
