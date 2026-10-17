# Proof and proposed paper-aligned cut for Entropy.lower_bound

This proof follows Sections 2, 3--4 and Appendix A, and Section 5 of the
supplied paper. There are three substantive analytic interfaces: normalized
smooth Gaussian transport (Proposition 2.3 and its prerequisites), the
normalized smooth estimate with its strict remainder (Theorem 3.1), and
convex approximation preserving entropy and covariance (Lemma 5.2).
The final continuity argument belongs in the glue.

For a probability density f on EuclideanSpace R (Fin m), write b(f) for
its vector first moment, C(f) for its centered second-moment matrix, and
H(f) = -integral f log f. These abbreviations will be expanded in every
frozen statement. For a smooth real potential V, uniform convexity means
c_minus * norm(v)^2 <= D(DV)(x)(v)(v) <= c_plus * norm(v)^2 for all x,v,
where c_minus and c_plus are strictly positive. This is the coordinate-free
version of the paper's two Hessian inequalities.

## Approximation: Lemmas 5.1 and 5.2

Set V=-log f on the convex positive set and V=+infinity outside it.
The hypotheses on f give a proper lower semicontinuous convex extended
potential; mass one ensures a full-dimensional effective domain. Lemma 5.1
proves V(x)>=a*norm(x)-b: a finite-volume convex sublevel containing a ball
is bounded, and convexity along rays gives linear coercivity. For each
positive integer j form Q_j(x)=inf_y(V(y)+j*norm(x-y)^2/2), convolve with an
even smooth unit-mass mollifier of radius 1/j, and add norm(x)^2/j.
The minimizer defining Q_j is unique; its monotonicity gives a j-Lipschitz
gradient. Thus the smoothed potential has Hessian between 2/j and j+2/j.
The estimates Q_j>=a*norm(x)-b-a^2/(2j) and
0<=Q_j*mollifier-Q_j<=1/(2j) give convergence and a common exponential
tail. Dominated convergence applies to mass, first moments, second moments,
and V_j exp(-V_j). Absorb log Z_j into each potential so exp(-V_j) is
already a probability density. The resulting densities have convergent
L1 distance, means, covariance entries, and entropy.

## Normalized Gaussian transport: Section 2 through Proposition 2.3

Let gamma_m be standard Gaussian measure. Put
q(a)=varphi(a)/Phi(-a) and t(a)=-log Phi(-a).
Lemma 2.1 proves q is a smooth increasing bijection R -> (0,infinity),
0<q'<1, and q''>=0. For any smooth probability potential with positive
bounded Hessian, Brenier transport is a smooth gradient and the two
Caffarelli contraction inequalities bound its Jacobian above and below.
The matrix field A=q^{-1}(D^2 phi) is therefore smooth and bounded.

Proposition 2.3 chooses a positive definite linear change of variables P
for which integral A dgamma_m=0. It deforms the density from Gaussian,
uses transport uniqueness and strict log-determinant concavity to prove
continuity of integral q^{-1}(J), and bounds all zeros in a compact subset
of the positive definite cone using covariance, Jensen and Gaussian
Poincare. The Gaussian endpoint has one zero of nonzero Brouwer degree;
homotopy invariance supplies a zero for the target density. The transformed
potential remains smooth with positive bounded Hessian. Change of variables
gives H(P#f)=H(f)+log|det P| and
log det C(P#f)=log det C(f)+2log|det P|. Their entropy gaps agree.
The transport interface retains P and its pushforward identity, so the
same normalization can be used in the equality analysis.

## Normalized strict remainder: Theorem 3.1

For a normalized transport write X_r=integral x_r A dgamma_m,
Y=A-sum_r x_r X_r, and B=sum_r X_r^2. Theorem 3.1 states
2H-2m-log det C >= integral tr(Y^T Y)/500 + sum_i omega(lambda_i(B))/1000,
with omega the exact nonnegative weight in (3.1). In the frozen interface
tr(Y^T Y) is the sum of squares of all matrix entries; these are equal
without a symmetry assumption. The eigenvalue term is retained for reuse
in Section 6, rather than discarded in the child.

Here is the paper's derivation of that estimate. Lemma 2.4 obtains finite
Jacobian energy from the twice differentiated Monge--Ampere equation using
compact cutoffs. Proposition 2.5 tests that equation with k(A)^2, where
k=t/q, and keeps the nonnegative eigenvalue-separation surplus C_surplus:
integral tr k(A)^2 >= ||partial A||^2-||partial k(A)||^2+C_surplus.
Lemma 3.2 uses the Gaussian chaos resolvent (I+N)^(-1) to complete the
covariance. At the supporting plane S=(37 I/40+3B/40)^(-1), Lemmas 3.3
and 3.4 control all noncommuting factors. Proposition 3.5 absorbs the
supporting-plane cost, retaining -sum omega/1000 and costing 69||Y||^2/500.
Proposition 3.6 bounds the remaining derivative errors by the same surplus
and Q(G,g-G/2), where Q(u,v)=43u^2/100+26uv/100+68v^2/25. Sections 4 and
Appendix A prove these two scalar certificates with rational estimates and
analytic tail bounds; numerical sampling is not a proof. The surpluses
cancel. On degree d>=2, g=G/d and ||G||^2=d||Y||^2. With r=1/d,
1-r-Q(1,r-1/2)-7r/50=(1-2r)(1+68r)/50>=0.
Summing orthogonal chaoses leaves -||Y||^2/500-sum omega/1000 in the
signed deficit, exactly as required.

## Glue and the original hypotheses

Apply approximation to the given f. Apply normalization and the strict
remainder estimate to every smooth approximant. Nonnegativity of the
squared-entry integral and of omega on the eigenvalues of B yields the
ordinary entropy inequality for each approximant. The normalization gap
identity transfers it to the original approximant's coordinates.

The covariance of f is positive definite: a zero quadratic form for a
nonzero direction would force a mass-one Lebesgue density to lie on an
affine hyperplane, which has zero Lebesgue measure. The second-moment
hypothesis supplies the needed integrability. We import the gate-accepted Submission.Lib.EntropyTools (g00008, source
de16fb3 by x0004) for this step: densityCovariance_det_pos is the general
Lebesgue-density result, and entropy_lower_bound_of_tendsto is the scalar
limit bridge. The same library proves rigidityWeight_nonneg with the
paper's specified value at zero.
Entrywise covariance convergence implies determinant convergence, and
continuity of log at the strictly positive limiting determinant implies
log-determinant convergence. Passing to the limit in the scalar
inequalities proves m+log(det C(f))/2<=H(f), which is the frozen goal
following substitution of the supplied defining equalities for b,C,H.

No analytic child is claimed proved here. The gate is asked to validate
these interfaces and the Lean glue, after which the three children can be
worked on independently (the matrix estimate assumes normalization data;
it does not need to reconstruct it).

## Frozen-interface conventions

The proposed Lean names are Entropy.normalized_transport,
Entropy.normalized_remainder, and Entropy.smooth_approximation. All use
only Mathlib and ChallengeDeps. Typed function applications bind local
abbreviations inside each proposition; they beta-reduce to the displayed
mathematics, add no assumption, and refer to no Submission declaration.
This spelling avoids the schema's prohibition on := tokens and keeps
each frozen statement below its 4000-character bound.

Smoothness is ContDiff R ((top : ENat) : WithTop ENat), which means
infinitely differentiable; top at the outer WithTop level means analytic
and is deliberately not used. Matrix-field smoothness and expectations
are entrywise, avoiding any choice of a scoped matrix norm. Standard
Gaussian measure is ProbabilityTheory.stdGaussian on EuclideanSpace;
q is gaussianPDFReal 0 1 a / cdf(gaussianReal 0 1)(-a). The Jacobian's
(i,j) entry is (fderiv R (gradient phi) x (PiLp.single 2 j 1)) i.
The equation cfc q (A x)=J replaces the paper's A=q^{-1}(J);
Lemma 2.1 and symmetric spectral calculus make these equivalent.

For the spectral remainder B=sum_r X_r X_r is only positive semidefinite,
not positive definite (the Gaussian case has A=0 and B=0). The child
provides the proof hB : B.PosSemidef used to index its real eigenvalues.
The cutoff in omega is 13/100 at zero; Lean's default division by zero
would otherwise give the wrong value. The energy is the integral of the
sum of entry squares, exactly tr(Y^T Y)=tr(Y^2) for symmetric Y.

The split has no sibling proof dependencies: the remainder theorem
assumes the normalized transport data and does not invoke the existence
theorem, while approximation is independent of both. Each can itself
be split along the cited paper lemmas as the tree develops. At the last
lot sync, no similar existing obligation was listed for any of the three.

## Validation before submission

All three closed types elaborated against Mathlib and ChallengeDeps, and
lake build Submission.Obl.Entropy__lower_bound passed with generated
child stubs. lot sync reported no similar obligations. lot check was run;
it returned code 4 explaining that glue importing proposed-child stubs
is checked by lot submit split. Thus submission is the gate check for
this split, not a claim that the children or parent have been proved.
