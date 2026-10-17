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
mean a uniform average, let x=|delta|/2 and w=x/sinh x (w=1 at x=0).
The two increasing functions D0(1+k') and D0(1-k')=k, where D0=1/d,
give by Chebyshev covariance
bar M >= M1=(bar D0)²-(bar(k'D0))² >= (3/4)(bar D0)².
Since M*lambda^(-m*) increases on the interval, exponential reweighting
and Chebyshev give
B/bar M >= shc((1+m*)x)/(shc(x)shc(m*x))
          >= 1+m*(1-w²),
with m*=m0(min(a,b)). The explicit hyperbolic inequality and positive
Taylor coefficients imply
(3/4)(1+m*)(w^-2-1)
 >= (1+m*)/16*(delta²+delta⁴/30+delta⁶/1680).
Combining these inequalities with the divided-difference identities
proves the scalar conclusion. At a=b, the surplus is zero and the
identity defining M gives equality. This is the third child.

## 4. The matrix spectral comparison

Diagonalize A pointwise and rotate all three indices of
Theta_ijr=partial_r J_ij into the same eigenbasis. The tensor is fully
symmetric because J=D²phi. No eigenvector is differentiated. The
Daleckii--Krein formula gives J_r entries q[a_i,a_j](Z_r)_ij and
K_r entries k[a_i,a_j](Z_r)_ij. The density R is therefore the
symmetric sum with weight Theta_ijr²/(lambda_i lambda_j lambda_r)
and coefficient ((lambda_i+lambda_j)/2) B(a_i,a_j).

Monotonicity and symmetry of B permit replacing that coefficient by
lambda_r B(a_i,a_j), decreasing the full sum. This is the three-index
rearrangement inequality; repeated eigenvalues are allowed. Apply the
scalar secant bound to each pair, multiply by the nonnegative squared
entries, and sum. Orthogonal invariance in the derivative index then
gives the pointwise inequality
sum_r |Z_r|²-sum_r |K_r|²+separation_density <= R.

For measurability, expand m0(min(a,b)) as
(19/100) 1_{a>=-3}1_{b>=-3}
+(19/100) 1_{a>=-2}1_{b>=-2}
+(30/100) 1_{a>=-1}1_{b>=-1}.
Each squared-entry sum weighted by an even power of log q(a)-log q(b)
is expressible using traces, log q(A), and the corresponding spectral
cutoff projections. A cutoff projection is a pointwise limit of
continuous spectral functions, proving these basis-independent sums
measurable without requiring measurable canonical eigenvectors. Weights
vanish at equal eigenvalues. Bounded spectrum bounds the weights, so
the density is dominated by a constant times sum_r |Z_r|². Thus it is integrable; so are the two energies and R.
Integration and finite-sum interchange yield
sum_r ||Z_r||²-sum_r ||K_r||²+Csep <= E R.
This is the fourth child, independent of V and the pushforward equation.

## Assembly and reuse

Use the weak equation and finite energy from the first child in the
second. Combine the second and fourth inequalities by transitivity and
retain the L2 conclusions from the first child. The third child supplies the
scalar hypotheses to the fourth; thus every child is used.

The current library provides the Gaussian hazard derivative and
Lipschitz bound (accepted o009). The newly accepted contributed module
Submission.Lib.GaussianTransport also supplies smooth hazard/inverse
maps, positive derivative and gap bounds, q convexity, and 0<k'<1/2.
Its ScalarMatrixDerivative module treats derivatives at scalar matrices;
the general divided-difference CFC derivative formula still needs proof.
Neither the finite-energy argument nor the scalar M-growth certificate
is already provided.
Searches for transport energy, divided differences and hazard found no
existing obligation that supplies the proposed conclusions.

Session x0044's own o018 code already proves the hyperbolic comparison,
Taylor surplus, abstract symmetric tensor rearrangement, probability
Chebyshev inequality and final scalar coefficient algebra. These are
retained as proved helpers, not made into new obligations. The session is
also publishing them as Submission.Lib.EntropySurplus for descendant use. In
particular the scalar child isolates the remaining M-growth/average
argument and the spectral child isolates the matrix-calculus bridge.

## Frozen interfaces and validation

The names are Entropy.transport_finite_jacobian_energy,
Entropy.transport_integrated_multiplier, Entropy.hazard_secant_surplus,
and Entropy.hessian_spectral_surplus. The scalar statement is quantified
pointwise in a,b; its middle conjunct gives B(a,c)<=B(b,c) for every c
when a<=b. The glue packages this as monotonicity in the first argument.
The explicit diagonal B=k²+2kk'/(q-a) is the derivative of lambda F
with respect to lambda, not the derivative with respect to a.

The owned parent theorem has built locally against all four generated
stubs, including the refinement exporting the weak Jacobian identity.
All similar-obligation matches returned by lot sync have explicit
non-implication reasons in split.json. These checks validate the cut and
glue, not the child proofs; gate submission and review remain authoritative.

The required lot check returned code 4 with the message that glue importing
proposed child stubs is checked by lot submit split. Every owned helper
module also builds locally; no analytic child is asserted proved here.

The final local axiom audit lists exactly the four proposed child theorems
and propext/Classical.choice/Quot.sound for the parent. Helper audits list
only those three allowed axioms. The frozen parent type is unchanged.
