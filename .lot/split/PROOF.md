# Proof of both holes and proposed cut

The proof follows the supplied paper, *A sharp entropy bound and the simplex
inequality for isotropic constants*. The four children are the inequality in
Theorem 1.2, its equality classification proved in Section 6, the cone density
and moment calculation (7.1)--(7.5), and the geometric identification of the
exponential-product cone laws with simplices (7.7)--(7.8). The elementary
conversion of the resulting determinant inequality into the stated real-power
constant stays in the root glue. These are independent analytic, integration,
and finite-dimensional geometric tasks, not reformulations of either root hole.

## Density convention and the analytic children

For a nonnegative real function f on E_m = EuclideanSpace R (Fin m), put
b_f = integral x, f(x) * x, C_f(i,j) = integral x,
f(x)(x_i-b_f,i)(x_j-b_f,j), and H_f = -integral x, f(x) log f(x).
The integral is with respect to the standard Euclidean Lebesgue measure.
Here scalar multiplication is used in the vector mean. Require that f is
upper semicontinuous, log f is concave on {f>0}, integral f = 1, and that f,
f times norm(x)^2, and f log f are integrable. ConcaveOn includes convexity
of {f>0}. These hypotheses describe the upper semicontinuous representatives
of the paper's log-concave densities; V=-log f on {f>0}, V=+infinity elsewhere
is proper lower semicontinuous and convex. No special density definition is
assumed by a child: its frozen statement binds these expressions through explicit defining equalities.

Child Entropy.lower_bound asserts m + log(det C_f)/2 <= H_f (Theorem 1.2,
inequality part). Its proof is Sections 2--5, as follows. For smooth uniformly
convex V, Gaussian optimal transport supplies J=D^2 phi with positive upper
and lower bounds. With t(a)=-log Phi(-a), q=t', set A=q^{-1}(J) using symmetric
spectral calculus. Lemma 2.1 gives q'>0, q'<1 and the Gaussian/exponential
transport. Proposition 2.3 chooses a positive definite affine normalization
with E A=0 by a homotopy from the Gaussian; contraction estimates, Gaussian
Poincare and covariance bounds make the zero set compact. Lemma 2.4 permits
the cutoff integrations by parts. Proposition 2.5, obtained by multiplying the
Jacobian equation by k(A)^2, k=t/q, gives
 E tr k(A)^2 >= ||partial A||^2 - ||partial k(A)||^2 + C,
where C is the nonnegative eigenvalue-separation surplus. Its divided
differences and arithmetic/logarithmic mean comparisons must be retained.

Write A=sum x_r X_r+Y, B=sum X_r^2; Y has Gaussian degrees at least two.
The covariance completion (Lemma 3.2) with the Ornstein--Uhlenbeck resolvent
and the log-determinant supporting plane S=(37 I/40+3 B/40)^(-1) express the
signed entropy deficit D=2m+log det C_f-2H_f. The exact expansion in Lemma 3.3
and the commutator square in Lemma 3.4 control noncommuting factors.
Proposition 3.5 absorbs the supporting-plane cost and retains
-(sum omega(lambda_i(B)))/1000; Proposition 3.6 charges the divided-difference
error to the same C above. Their scalar estimates are proved in Section 4
and Appendix A by rational bounds and analytic tail estimates, not sampling.
After cancellation, the remaining quadratic form is
 Q(u,v)=43 u^2/100+26 uv/100+68 v^2/25.
For chaos degree d>=2 put r=1/d. The identity
 1-r-Q(1,r-1/2)-7r/50 = (1-2r)(1+68r)/50 >= 0
proves Theorem 3.1:
 2H_f-2m-log det C_f >= ||Y||^2/500 + sum omega(lambda_i(B))/1000.
In particular the entropy inequality holds in the smooth case. Lemma 5.1
supplies linear coercivity of V. Lemma 5.2 uses Moreau envelopes, mollification
and a quadratic correction to approximate by smooth uniformly convex
potentials, with convergence of entropy, means and covariance. The limiting
covariance is positive definite, since a Lebesgue probability density cannot
be concentrated on a proper affine hyperplane. Passage to the limit proves
the analytic inequality for the stated representatives.

Child Entropy.equality_cases asserts H_f=m+log(det C_f)/2 if and only if f is,
almost everywhere, the density of an invertible affine image of m independent
mean-one exponentials. The density is written explicitly as
 |det L|^(-1) exp(-sum_i (L^(-1)(x-b))_i)
when every coordinate of L^(-1)(x-b) is nonnegative, and zero otherwise.
The linear map L is a real linear equivalence of E_m. This child is Section 6
of the paper, and will share the smooth remainder/approximation infrastructure
from the analytic development above.

For completeness, zero entropy gap and the same approximation make Y_j tend
to zero in Gaussian L2 and B_j tend to I, because omega is nonnegative,
vanishes precisely at 1 and grows to infinity. Extract limits X_r with
sum X_r^2=I. Lemma 6.2 gives convergence q(A_j) to q(sum x_r X_r) in L2;
Gaussian Poincare gives a limiting centered map with this weak Jacobian.
In Lemma 6.1, its mixed-derivative identities at zero, using q'(0) and q''(0)
nonzero, first yield X_r e_s=X_s e_r and then [X_r,X_s]=0. Simultaneous
orthogonal diagonalization and sum X_r^2=I leave signed coordinatewise
exponential transports. Their covariance is I. Covariance convergence now
bounds both affine normalizations and their inverses, so a subsequence
converges to an invertible map and identifies the original equality law.
Conversely the product exponential density has entropy m and covariance I;
linear change of variables adds log|det L| to entropy and twice that number
to the covariance log determinant. This proves the reverse implication too.

## Cone moments and the normalization bridge

Child Cone.moments is Section 7, equations (7.1)--(7.5). We put the height
coordinate first rather than last, a coordinate permutation of determinant
of absolute value one. For K in E_n let
 C_K = {z in E_(n+1) : z_0>=0 and exists x in K,
                              z_(i+1)=z_0 x_i for all i},
and f_K(z)=exp(-z_0)/(n! vol K) on C_K and zero outside. This is a closed
convex cone with nonempty interior, and its height-zero section is {0}.
Compactness and nonempty interior give finite positive vol K. The covariance
of the uniform law on K is positive definite, by the same hyperplane argument.
The cone density is nonnegative and upper semicontinuous, and log f_K is
affine on its convex positive set. Its integrability, second moment and
entropy integrability follow by slicing and the gamma integrals below.

The change of variables y=t x for t>0 has Jacobian t^n. Integration by parts
in integral_0^infinity t^k exp(-t) dt gives k!, including the normalization,
 E T=n+1, E T^2=(n+1)(n+2), Var T=n+1.
Here T is independent of X uniform on K. Thus f_K is the density of (T,TX),
and H_(f_K)=n+1+log(n! vol K). We do not assume centroid K=0 in the child:
write b=centroid K and apply the shear (t,y) -> (t,y-tb), of determinant one.
Its covariance is the block diagonal matrix with entries n+1 and
(n+1)(n+2) covMatrix K. In original coordinates this is equivalently
 Var(T)=n+1, Cov(T,TX)=(n+1)b,
 Cov(TX)=(n+1)(n+2) covMatrix K+(n+1)bb^T.
Taking determinants gives, without a translation hypothesis,
 det C_(f_K)=(n+1)^(n+1)(n+2)^n det(covMatrix K).
This shear is the explicit bridge to the centered calculation in the paper.
The child returns the density hypotheses, these two exact identities, and
the volume/covariance positivity needed for the root's real arithmetic.

## Cone geometry

Child Cone.simplex_iff_product is the remainder of Section 7, particularly
(7.7)--(7.8) and the converse paragraph. It asserts that f_K is an affine
exponential-product density exactly when K is a simplex as defined in
ChallengeDeps. If f_K has the affine product representation, equality of
measures identifies closed supports: C_K=b+L[0,infinity)^(n+1). The support
of f_K is exactly C_K because its interior is dense and its density is
positive there. The cone and the orthant each have only one extreme point,
namely zero; an affine equivalence preserves extreme points, so b=0.
Every column of L has positive height, since it is a nonzero cone point.
Normalize each column by its height. The height-one section is their convex
hull. The normalized columns remain linearly independent; projecting their
height-one affine hyperplane to E_n gives n+1 affinely independent vertices
whose convex hull is K. This is precisely SimplexIsotropic.IsSimplex K.

Conversely take vertices v_0,...,v_n from IsSimplex K. The columns (1,v_i)
are linearly independent and give a linear equivalence L mapping the orthant
onto C_K. Its absolute determinant is n! vol K (subtract the first column,
expand by the height row, and use the simplex volume formula). Since the
height row consists of ones, sum_i (L^(-1)z)_i=z_0. The change-of-variables
density of the exponential product is therefore exactly f_K, including
equality almost everywhere on the boundary. This proves the equivalence.

## Root glue: inequality and both directions of equality

Set a=n!, v=vol K, d=det(covMatrix K), and
 c=(n+1)^(n+1)(n+2)^n. All are strictly positive for n>=1.
The first analytic child applied to the cone identities yields
 log(c d) <= 2 log(a v).
Strict monotonicity of log and log((a v)^2)=2log(a v) give c d <= a^2 v^2.
Divide by c v^2 and raise to the positive power 1/(2n). The identities
 (a^2)^(1/(2n))=a^(1/n),
 ((n+1)^(n+1))^(1/(2n))=(n+1)^((n+1)/(2n)),
 ((n+2)^n)^(1/(2n))=sqrt(n+2)
give exactly theorem_1_1_ineq with the frozen definitions.

Every real-algebra step is reversible because all bases and denominators
are positive and the exponent is positive. Hence equality of isotropic
constants is equivalent to c d=a^2 v^2, which is equivalent to
H_(f_K)=n+1+log(det C_(f_K))/2. Entropy.equality_cases turns this into the
affine exponential-product representation, and Cone.simplex_iff_product
turns that into IsSimplex K. This chain proves both directions of
 theorem_1_1_eq, with every proposed child used by the root.

No root proof is claimed here. The children contain the substantial pending
arguments; the split check validates their frozen interfaces and the glue.
