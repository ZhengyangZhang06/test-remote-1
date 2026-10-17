# Decomposition of o011: linear Jacobian rigidity

We split Lemma 6.1 of the supplied paper at its displayed rigid-map formula.
The first child proves that deterministic formula; the second proves the
last paragraph of the lemma, including the density and centered covariance
required by the frozen parent. They have no dependency on one another.
Only their statements meet in the glue.

Write E = EuclideanSpace R (Fin m), gamma = stdGaussian E,
Phi(t) = cdf (gaussianReal 0 1) t, phi(t) = gaussianPDFReal 0 1 t,
q(t) = phi(t)/Phi(-t), and T(t) = -log(Phi(-t)). These are notation in
this explanation only: the frozen children expand the functions explicitly.

## Child 1: deterministic normal form (Lemma 6.1 through rigid-map)

Assume m >= 1, F is C1, every X_r is real Hermitian, sum_r X_r^2 = I,
and DF(x) = q(A(x)), where A(x) = sum_r x_r X_r. No Gaussian moment
or centering hypothesis is needed in this child. We prove that there are
a linear isometry equivalence Q : E -> E and a vector a such that

    (Q^{-1}(F(Q y) - a))_i = T(y_i)    for every y and i.

First extract the integrability conditions of the Jacobian. The Gaussian
density is real analytic and its cdf is real analytic near zero, with
Phi(0)=1/2. Consequently q is analytic near zero. Its scalar identities give

    q(0) = sqrt(2/pi),
    q'(0) = 2/pi > 0,
    q''(0) = sqrt(2/pi) * (4/pi - 1) > 0.

Positivity in the last identity uses pi < 4. The power series for q,
evaluated by matrix multiplication, converges locally around A=0. On
Hermitian matrices it agrees with the real continuous functional calculus:
diagonalize the matrix and apply the scalar series at each eigenvalue.
The series and its differentiated series converge uniformly on smaller
balls. Thus J(x)=q(A(x)) is analytic near zero and

    J(x) = q(0) I + q'(0) A(x) + q''(0)/2 * A(x)^2 + O(|x|^3),

with differentiated remainder O(|x|^2). Since F is C1 and DF=J, the
analyticity of J upgrades F to C3 locally. Equality of mixed derivatives
therefore gives (partial_r J)e_s = (partial_s J)e_r. Comparing its constant
and linear terms, using the two nonzero scalar derivatives, gives

    X_r e_s = X_s e_r,
    (X_r A(x) + A(x) X_r)e_s = (X_s A(x) + A(x) X_s)e_r.

The first identity says A(x)z=A(z)x, so A(x)e_s=X_s x. Canceling the
terms with leftmost A(x) in the second identity leaves
(X_r X_s - X_s X_r)x=0 near zero. This homogeneous linear identity holds
everywhere, hence all the X_r commute. This is the difficult analytic
compatibility step; merely assuming F is C1 causes no loss of derivatives
because its prescribed Jacobian is analytic locally.

Choose a common orthonormal eigenbasis of the commuting real symmetric
matrices, with orthogonal matrix U. After rotating input and output the
coefficient of y_i is

    Xtilde_i = U^T (sum_r U_ri X_r) U.

It is diagonal; orthogonality gives sum_i Xtilde_i^2=I; and the first
compatibility identity gives Xtilde_i e_j=Xtilde_j e_i. For i != j the two
sides lie in distinct coordinate lines, so both vanish. Thus only the
ith diagonal entry of Xtilde_i can be nonzero, and its square is one.
Write this entry sigma_i, so sigma_i is 1 or -1. It follows that

    U^T A(U y) U = diag(sigma_i y_i),
    D[U^T F(U y)] = diag(q(sigma_i y_i)).

The Gaussian cdf is strictly positive at every finite point. Its derivative
and the evenness of phi give T'=q on all of R. The accepted o009 CDF and
Hazard modules (lib a6f3986fe0) already expose cdf_eq_mass, mass_pos,
hasDerivAt_mass, and hasDerivAt_hazard in namespace
Submission.Obl.Entropy__gaussian_hazard_lipschitz, so the scalar derivative
and positivity steps can reuse those proofs. Therefore the vector
(sigma_i T(sigma_i y_i))_i has precisely this Jacobian. The difference has
zero derivative on the connected space E, hence is a constant w, pointwise:

    U^T F(U y) = (sigma_i T(sigma_i y_i))_i + w.

For the frozen child we absorb the signs into the orthogonal map. Let
S=diag(sigma_i), Q=U S, and a=U w. Substitute y=S z in this last formula.
Since S^2=I it becomes F(Q z)=Q(T(z_i))_i+a, exactly the stated coordinate
formula. This also handles m=1 and every choice of signs. Simultaneous
diagonalization does not require distinct eigenvalues.

The analytic part is not yet proved in lib. Existing original tree work
can shorten its subsequent proof: x0028's o011 branch has
exists_primitive_of_tendstoUniformlyOn_ball (commit f76e73d); x0007's
2026-10-17T05:50Z and 06:12Z posts describe signed_coordinate_field and
linear_field_jacobian_primitive. These reports identify reusable algebra
and integration, not accepted hypotheses. Neither an unaccepted helper
nor its reported conclusion is imported or assumed in our glue.

## Child 2: Gaussian image and moments (last paragraph of Lemma 6.1)

Start independently with a linear isometry equivalence Q, a vector a, and
a map F satisfying the coordinate formula of Child 1. Assume F is in
Gaussian L2 and has Gaussian mean zero, exactly as in the parent. This
child has no matrix field, functional calculus, or derivative hypotheses.
It proves the image-density formula with the specific L=Q.toLinearEquiv
and the same a, and proves that the raw second-moment matrix is I.

Let G have standard Gaussian law in E. Orthogonal invariance says that
Q^{-1}G has independent standard Gaussian coordinates. For a scalar
standard Gaussian Z, the continuous strictly increasing Gaussian cdf
and symmetry imply Phi(-Z) is uniform on (0,1). The transformation
-log maps this to the mean-one exponential distribution: for t>=0,

    P(-log(Phi(-Z)) > t) = P(Phi(-Z) < exp(-t)) = exp(-t).

For t<0 the transformed variable is nonnegative. The scalar map T is
continuous and hence measurable, so applying it separately preserves
independence. Therefore Y=(T((Q^{-1}G)_i))_i has density

    rho(y) = if every y_i >= 0 then exp(-sum_i y_i) else 0

with respect to Euclidean volume. This is the product density: the
PiLp/Euclidean coordinates use the orthonormal standard basis, whose
volume is ordinary product Lebesgue measure. The formula for F gives
F(G)=Q Y+a. Translation and invertible linear change of variables yield

    (F_#gamma)(dx) = |det Q|^{-1} rho(Q^{-1}(x-a)) dx.

All factors are nonnegative, so its Lean measure is volume.withDensity
of ENNReal.ofReal of exactly the real density in the child statement.
We retain |det Q|^{-1} explicitly, although orthogonality makes it one,
to match the parent's affine formula without any normalization change.

For the second conclusion, the elementary integrals of 1, t and t^2
against exp(-t) on [0,infinity) are 1, 1 and 2. These integrations need
not be reproved: during preparation o013 was accepted (gate g00024,
lib 361e6d5610), with import
Submission.Obl.Entropy__affine_exponential_moments.Exponential. In its
namespace Submission.Obl.Entropy__affine_exponential_moments the
accepted helpers integral_expDensity_pow,
integral_productExpDensity_coord_mul, covariance_productExpDensity,
and covariance_affineDensity supply the product and affine moment
calculations. The child reuses these for its remaining Gaussian image
and centered-moment identification. Mathematically, by independence,
E Y_i=1 and E[(Y_i-1)(Y_j-1)]=delta_ij. All these products are integrable;
the scalar exponential moments prove this directly, and the supplied
Gaussian MemLp 2 also controls products of the F coordinates. Thus
E F=Q 1+a. Centering identifies a=-Q 1, and expanding the finite sums gives

    E[F_i F_j] = sum_k Q_ik Q_jk = delta_ij.

This is equality of the entire raw second-moment matrix, not merely its
determinant. It supplies precisely the covariance information used by
o012. No entropy equality assumption enters this child.

## Glue, reuse, and scope

Apply Child 1 to F and X, choose Q and a, and apply Child 2 to the resulting
coordinate formula, the parent's L2 hypothesis, and its zero mean. In the
first conjunct of the parent choose L=Q.toLinearEquiv and a; the density
identity and the second-moment identity are exactly the two conclusions
of Child 2. The glue uses both children and has no further analytic step.

Searches of lib at 91a937e09c, then the accepted o013 helpers at
361e6d5610, and the current obligation board found no accepted
deterministic normal-form or Gaussian exponential-image theorem. The
similarity comparison returned "nothing close" for both children.
The nearest moment obligation o013 starts with an already identified
Lebesgue density and gives entropy and a covariance determinant. It
neither identifies this Gaussian image nor determines the full covariance
matrix, and is not a replacement for Child 2. The scalar Lipschitz task
o009 gives a different first-derivative estimate and does not supply
Child 1's second-order compatibility or Child 2's image measure. The
parent o002 and o011 itself cannot be reused. The two new children isolate
local analytic/algebraic rigidity and a probabilistic change of variables;
neither is a restatement of o011. No new algebra-only or routine glue
child is proposed.
