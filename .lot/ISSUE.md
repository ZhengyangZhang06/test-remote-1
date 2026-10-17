# o047: Entropy.absorption_logarithmic_cutoff

Type: `∀ z : ℝ, 0 ≤ z → 40 / (37 + 3*z) - 1 - Real.log (40 / (37 + 3*z)) ≤ (86/125) * ((3 * (z - 1)^2 / (37 + 3*z)) * ((3 : ℝ)/20 + ((49 : ℝ)/100)*(37/(37+3*z))) * (if z = 0 then (13 : ℝ)/100 else min ((13 : ℝ)/100) (32/(25*Real.sqrt z))))`

Statement: The elementary logarithmic cost for the affine inverse s=40/(37+3z) is at most (86/125) times the exact rigidity weight, including the cutoff at z=0.

Role in the glue of o021: Supplies the .688 logarithmic bound that is subtracted from the .689 averaged p-minorant, retaining the exact omega/1000 remainder.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__absorption_logarithmic_cutoff.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

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
The B
