# Proof and split of first_chaos_absorption (o021)

Write E for integration against the standard Gaussian on R^m. Set
 t(a) = -log Phi(-a), q(a) = phi(a)/Phi(-a), k=t/q,
 b=k', l=b', p=(k(1+b))'-b^2-(40/3)l^2,
 h=k(1+b)-(3/2)k-(80/3)(b-7/25)l.
These are exactly the functions in the frozen statement. All decimals below
are rational numbers, not numerical approximations.

The split has three independent substantial children:

* Entropy.absorption_p_lower_bounds: the three scalar certificates
  p(a) >= 1/(7+a^2) for a<=0, p(a)>=1/4 for a>=0,
  and p(a)>=23/50 for a>=4, restricted to -6<=a<=10.
* Entropy.absorption_h_square_bound: h(a)^2 <= (67/100)^2 p(a)
  for every -6<=a<=10.
* Entropy.absorption_logarithmic_cutoff: the elementary logarithmic
  cost is at most (86/125) times the exact rigidity weight for lambda>=0.

The first two are the restricted Appendix A certificates needed by Section 4.1 of
the supplied paper. Neither is inferred from sampling. They isolate the
remaining analytic obstacle reported by session x0046.

The pure logarithmic bound is described below. It has a locally building
proof reported on another obligation, but that package is not yet in lib
or on an o021 branch. It is therefore a separate, frozen scalar child.
The remaining matrix/minorant work is kept in proved glue.

The conditional matrix absorption theorem is already proved on o021 branch
x0046, commit 884ffc5, and is merged into the owned glue. It is not a new
child. The following proof describes this existing assembly and the
conditional scalar/minorant/logarithm helpers used by the glue.

## Proof routes for the two Gaussian certificates

Use the supplied Appendix A, specifically its group G1; the two-eigenvalue
coefficient, derivative, and surplus tables are not needed here. The
algebraic identities p=b+kl-(40/3)l^2 and
h=k(b-1/2)-(80/3)(b-7/25)l follow from q'=q(q-a), k'=1-k(q-a),
and l=k-q+ab. Owned Functions.lean proves agreement with the frozen
nested-derivative definitions.

The entire a<=-6 case has a locally checked proof in merged
TailCertificate.lean (x0046 commit 0750dff), so it is excluded from the
first two children. This proof uses alternating Mills integral bounds.
Set r=-a>=6, u=r^(-2), J=r*Phi(-r)/phi(r), K=r*k(-r),
Q=q(-r)/r, and L=r^3*l(-r). Integration by parts gives
1-u<=J<=1-u+3u^2 and J>=1-u+3u^2-15u^3.
The Gaussian density estimate phi(r)*r^5<=1/1000 gives
J-u^3/1000<=K<=J and 0<=Q<=u^3/500. The exact identities
b=1-K(1+Q) and u^2*L=K(1+u)-1+(K-1)Q then imply
0<=K<=1+u/100, 0<=L<=21/10, and
u(1-3.01u)<=b<=u(1+u/100). The rational polynomial calculation
in NegativeTail.lean proves both desired p/h inequalities from these
bounds, for all 0<=u<=1/36. Rescaling gives the exact frozen functions.

The entire a>=10 case is also proved in owned PositiveCertificate.lean,
from x0046 commits eea4761, b9a3dbc and ccecd23. Set r=a,
u=r^(-2), J=r*Phi(-r)/phi(r), T=log(r*sqrt(2*pi))-log J.
The same alternating Mills bounds give
1-u+3u^2-15u^3<=J<=1-u+3u^2 and 1-u<=J<=1.
Elementary logarithm inequalities give 3<=T, T/r<=9/25 and
u*(T-3/2)<=1/40. Exact identities express
k=r*J*(1/2+u*T), b=1-(1/(2u)+T)*(1-J), and
l=r*(J/2+1-(1-J)/(2u)+T*((1+u)*J-1)-1/J).
Monotonicity in J and rational polynomial algebra yield
k>=0, b>=47/100, 0<=l<=1/50, k*(1/2-b)<=1/5.
Together with the accepted bound b<1/2 these give p>=23/50 and
-8/25<=h<=0, hence h^2<=(67/100)^2*p. The lower p bounds for
nonnegative a follow as well. Thus neither tail remains in a child.

On [-6,10], use the eleven rational seeds and degree-14 recurrences in
Appendix A. Propagate q'=q(q-a) backward from q(10), and k'=1-k(q-a)
forward from k(-6). Alternating Mills integral expansions prove the two
analytic anchors; the residual and joining estimates prove uniform errors
|q-P|<=10^(-8), |k-K|<=8*10^(-7). All seeds are rational approximations,
not assumed values. Propagate these errors to b,l, truncate to quartics,
and charge discarded coefficients by their absolute coefficient sum.
The Bernstein lower bound on each half of [-1,1] certifies positivity of
p(7+a^2)-1 on negative rows, p-1/4 on positive rows below 4,
p-23/50 above 4, and (67/100)^2*p-h^2 on every row. The G1 margins in
the supplied table are at least 1/1000; closed intervals cover all
endpoints. These exact rational certificates, combined with the analytic
error proof, establish each child. No numerical sampling is a proof.

## Scalar cost and regularity (proved in the glue)

Accepted Submission.Lib.GaussianTransport gives smoothness of t and q,
positivity of q, k'=transportSlope, and 0<transportSlope<1/2.
Consequently k and its derivatives b,l are smooth and p is continuous.
Combine the first child with both proved tails to obtain all three
global lower bounds. These imply p(a)>0 everywhere, by splitting
at a=0. For 0<=b<=1/2 one has (b-7/25)^2 <= (7/25)^2.
Together with the second child and both proved tails this gives

 (40/37)((b-7/25)^2 + (5/96)h^2/p)
 <= (40/37)((7/25)^2 + (5/96)(67/100)^2)
 < 111/1000.

Thus the frozen cost meets the hypothesis of the proved conditional matrix
assembly. Smooth entries of A are continuous. Substitution of p and cost
into that assembly, with the conditional scalar estimates below, proves
the frozen goal. All three children are used.

## Conditional matrix absorption used in the glue

Let X_r=E[x_r A], B=sum_r X_r^2, Y=A-sum_r x_r X_r,
S=((37/40)I+(3/40)B)^(-1), H=-(S-I)(B-I), and
rho=(3/20)I+(1813/4000)S. The X_r and Y are symmetric.
Bounded continuous entries of A are in Gaussian L2. Gaussian coordinate
second moments and the definition of X imply both cross terms vanish,
and hence E[A^2]=B+E[Y^2]. The mean of A is zero by hypothesis.
All p(A) entries are integrable: the spectra of bounded A lie in a compact
interval and continuous functional calculus is bounded there.

Choose a unit eigenvector v_i of B with eigenvalue lambda_i>=0. The
averaged spectral measure of A along this fixed vector has mass one,
first moment zero, and second moment lambda_i+r_i, where
r_i=E[v_i^T Y^2 v_i]>=0. Equivalently, all these statements can be proved
by integrating fixed-basis diagonal entries, with no measurable choice
of eigenvectors of A needed. The sum of the r_i is E tr(Y^2)=N(Y).

For 0<u<=13/100 set n_u=u*sqrt(u)/2 and
 d_u=u^3/(16*(23/50-u)).
The three lower bounds on p imply the quadratic minorant
 p(a)>=u+n_u*a-d_u*a^2.
For a<=0 put x=-sqrt(u)*a. If x>=2 the right side is nonpositive.
For 0<=x<=2 multiply by x^2+7u and use
 1-(1-x/2)(x^2+7u) >= x(x-1)^2/2+(9/200)(2-x)>=0.
For 0<=a<=4, u+2u^(3/2)<=13/100+2(13/100)^(3/2)<1/4.
For a>=4 complete the quadratic square: its maximum is 23/50.

Choose u(lambda)=13/100 at lambda=0, and otherwise
min(13/100,32/(25*sqrt(lambda))). Then lambda*u^2<=(32/25)^2,
and the moment identities yield
 E[v_i^T p(A)v_i] >= (689/1000)u-d_u*r_i.
The scalar eigenvalues of S,H,rho are
 s_lambda=40/(37+3lambda),
 H_lambda=3(lambda-1)^2/(37+3lambda),
 rho_lambda=3/20+(49/100)*37/(37+3lambda).
They satisfy H_lambda*rho_lambda*d_u<=27/1000.
Indeed rho<=16/25; for lambda>=1 use H<=lambda, while for lambda<=1
use H<=3/37. Both reduce to exact rational inequalities and u<=13/100.

The third child is the elementary logarithmic estimate
 s_lambda-1-log(s_lambda) <= (688/1000)H_lambda*rho_lambda*u.
One proves it using F(S)=S(S-1-log S)/(1-S)^2, F(1)=1/2,
F(S)<=4/25+(13/25)S on 0<S<=40/37, and
F(S)/sqrt(S)<=239/500+(7/5)S for S>0.
The first follows from the concave integral representation of F and its
tangent at 7/25, with a rational log certificate. The second follows
from an exact rational logarithm minorant and polynomial positivity
(as in the existing locally proved ScalarLog work reported by x0023).
These yield the two cutoff bounds 89/1000 and 22/(25*sqrt(lambda));
89/1000 < (688/1000)(13/100) and
22/25 < (688/1000)(32/25). Lambda=1 has H=0 and S=1, so both
sides vanish; lambda=0 uses the explicitly specified cutoff.

Combining the logarithmic estimate and averaged minorant gives, for each i,
 s_lambda-1-log(s_lambda)-H_lambda*rho_lambda*E[v_i^T p(A)v_i]
 <= (27/1000)r_i-(1/1000)omega(lambda_i).
Sum over the fixed eigenbasis of B. Trace cyclicity identifies the weighted
p(A) term even though p(A) need not commute with B. Positive definiteness
of S gives log(det S)=sum_i log(s_lambda_i).

Finally c(a)<=111/1000 implies
 tr(Y^2 c(A)) <= (111/1000)tr(Y^2)
by spectral calculus and positivity of Y^2, without any commutation
assumption. Integrating and adding gives coefficient
27/1000+111/1000=69/500 and exactly the frozen omega remainder.
The Y term is integrable in the application (continuous bounded scalar
cost on the spectrum). The general transfer statement does not need
continuity of c: if that trace is not integrable, Lean's integral is zero,
and the same upper bound follows from N(Y)>=0.

## Existing work and scope

Read o021's issue, feedback, branch list, and branch x0046. Submission
g00090 failed a prose-schema check; the duplicate comparison was removed. The 06:25 and 06:37 posts of x0046 identify
precisely the p/h certificates as missing and provide spectral/CFC helpers.
The 06:24 post of x0016 describes locally proved conditional scalar
minorant and first-chaos identities, and the 06:37 post of x0023 describes
locally proved logarithmic estimates. These packages were not available
in accepted lib or on an o021 branch when this glue was finalized.
Moments.lean and ScalarMinorant.lean were therefore written here from
pinned Mathlib and the supplied paper. The logarithmic estimate is the
third child; its existing author can offer the reported proof once the
child is frozen. Accepted GaussianTransport is imported directly.
No new child repeats its smoothness or slope theorems.

## Validation

The three child types are closed propositions using only Mathlib and
ChallengeDeps; generated stubs build with autoImplicit disabled. The full
owned module and every imported owned helper build locally. A transitive
axiom audit of first_chaos_absorption lists exactly the three proposed
child theorems and propext, Classical.choice, Quot.sound. The parent
statement was compared textually with origin/main and is unchanged.
lot check returned code 4 and directed this proposed-child glue to
lot submit split for the gate check. The similarity results are answered in split.json; no gate acceptance
is claimed before submission.

The gate, not the local build, decides acceptance of this split. The
children remain mathematical obligations after a successful glue check.
