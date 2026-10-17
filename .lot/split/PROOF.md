# Proof of o019 and its two-child decomposition

This cut follows Section 3 of the supplied paper: equation (3.2), the
covariance representation and dual estimate in Lemma 3.2, and the
H1--Hminus1 completion in that lemma. All definitions in the child types
are expanded using only Mathlib and ChallengeDeps. The scalar functions
are exactly q(a)=gaussianPDFReal(0,1,a)/Phi(-a), t(a)=-log Phi(-a), and
k(a)=t(a)/q(a). The direction e_r is PiLp.single 2 r 1, and all matrix
weights act on rows.

Write gamma for standard Gaussian measure, I for integration against it,
F=gradient phi, J=q(A)=DF, k for k(A), and K_r=partial_r k(A). Write
N(H)=I sum_ij H_ij^2 and W(P,H)=I trace(H^transpose P H). Covariance always
uses the Bochner mean in the frozen statement.

## Entropy identity: proved helper, not a child

The owned files GaussianDensity, Injective, ChangeVariables, Spectral and
Entropy were merged from o019 branch x0045, commits a86b31e and b7cacb9.
Their proofs have been read and built locally. They are checked with this
split, so this step does not require an unproved obligation.

Every q(a) is positive. Functional calculus makes J positive definite.
Along the line from x to y the scalar product of F with y-x has strictly
positive derivative when x differs from y. Hence F is injective. The
change-of-variables theorem for an injective C1 map gives the Jacobian
formula on its image. Combining it with F_*gamma=f dy gives
  |det DF(x)| f(F(x)) = gaussianDensity(x)
almost everywhere. For a merely a.e. measurable f, take a nonnegative
measurable representative and transfer equality using absolute continuity
and the pushforward. No smoothness of f and no surjectivity of F is used.

The integrability of f log f transports to log f composed with F.
Subtracting the known Gaussian log density shows log det J is integrable.
The scalar identity
  log q(a) = -a^2/2 - log(2*pi)/2 + t(a)
and the Hermitian spectral theorem give
  log det J = -sum_ij A_ij^2/2 - m log(2*pi)/2 + trace t(A).
Bounded continuous A has Gaussian L2 entries. Integrating the identity
therefore also establishes integrability of trace t(A), and gives
  2m + 2 integral(f log f) = N(A) - 2 I(trace t(A)) + m.                 (1)
This is equation (3.2) with the common log covariance determinant removed.

## Child cfc: C1 bounded matrix functional calculus

Entropy.c1_bounded_matrix_calculus isolates the regularity used in the
spectral calculus of Sections 2--3. For every C1 real g and bounded C1
Hermitian field A, it asserts that g(A) has C1 bounded entries. No higher
regularity, derivative L2 bound, or energy inequality is requested.
The C1 upgrade of weak testing below is proved, so C1 is sufficient here.

Here is the matrix-calculus proof. Fix a Hermitian base matrix A, with
spectral projectors P_i and eigenvalues lambda_i. The exact difference
identity
  g(B)-g(A) = sum_i P_i (B-A) cfc(g[lambda_i, .])(B)
uses continuous divided differences, including g'(lambda_i) at repeated
eigenvalues. Continuity of CFC yields the Frechet derivative
  Dg(A)[H] = sum_ij g[lambda_i,lambda_j] P_i H P_j.
To see that this derivative is continuous, approximate g' uniformly by
polynomials on a compact interval containing all nearby spectra, and
integrate the approximating polynomials to approximate g. The Frobenius
operator norm of the derivative error is bounded by the scalar derivative
error, using orthogonality of the spectral blocks. Thus the derivative is
a locally uniform limit of polynomial matrix derivatives. Composition
with the C1 field A proves the C1 assertion. A global entry bound R for A
puts every spectrum in [-mR,mR]. The spectral theorem bounds the operator
norm of g(A) by max_{[-mR,mR]} |g|, also bounding its entries.

x0063 has reported a locally checked implementation of this C1 calculus
in MatrixCFCDifferentiation (235fa5d, post at 06:59Z), but that package is
not yet in accepted lib. The child has been reduced to match this existing
candidate rather than asking for unneeded C-infinity calculus. Its prover
can use the shared package once accepted. No current frozen obligation
implies this statement; final sync reports no close match.

The accepted GaussianTransport scalar calculus proves q,t,k smooth, hence
C1. Applying this child to q and k gives Gaussian L2 entries of J and k,
and C1 scalar entries of k. The hypothesis of o019 already supplies L2
entries of K. Differentiating k_ij=k_ji makes K_r symmetric. Functional
calculus gives kJ=Jk=t(A). Thus t(A) has integrable entries, as a product
of L2 entries. Every entry of
  E = 2t(A) - k^2 - sum_r K_r^2
is integrable. These last deductions are proved in Regularity and
Completion, not deferred to another child.

## Child covariance: Gaussian covariance variational estimate

Entropy.gaussian_covariance_variational is the first identity and dual
estimate of Lemma 3.2, before its completion by k. Its map F is an arbitrary
C1 map, not necessarily a gradient. Its assumptions give an L2 Jacobian J,
a probability density f with finite second moment, and F_*gamma=f dy.
The pushforward identifies its mean and covariance with the explicit
integrals of f and puts F in Gaussian L2. Together with the derivative
assumption this puts F in Gaussian H1.

Decompose F into Hermite chaoses. Differentiation lowers degree by one;
on degree d, sum_l <partial_l F_i,partial_l F_j>=d <F_i,F_j>.
The resolvent R=(Id+N)^(-1) on the derivative's degree d-1 multiplies by
1/d. Orthogonality and summation prove
  Cov(F_i,F_j) = sum_l <J_i,l, R J_j,l>.
This is the Hminus1 row Gram matrix of J. Hermite completeness and
H1 approximation justify the identity for these C1 H1 maps.

The completed weak-testing helper below supplies the needed noncompact
polynomial tests. Its proof is independent of both new children. Suppose a,b are L2 and the compact-test identity says
  I((a_ij-J_ij) z) = sum_r I(b_r,ij partial_r z).
Its sign is J=a-partial* b. The proved weak-testing helper allows normalized
Hermite polynomial tests h_alpha. Writing subscripts for Hermite
coefficients, their lowering identity gives, for each scalar entry,
  J_alpha = a_alpha - sum_{r: alpha_r>0} sqrt(alpha_r) b_{r,alpha-e_r}.
Cauchy--Schwarz therefore bounds |J_alpha|^2/(1+|alpha|) by
|a_alpha|^2 + sum_{r: alpha_r>0} |b_{r,alpha-e_r}|^2. On summing over
alpha, each coefficient of each b_r occurs exactly once. Parseval gives
the Hminus1 norm estimate ||J||_{-1}^2<=||a||^2+sum_r ||b_r||^2.
Equivalently this is the paper's Cauchy--Schwarz estimate for the dual
H1 pairing. Applying it to rows after multiplication by P^(1/2) gives
  trace(P Cov(F)) <= W(P,a) + sum_r W(P,b_r).                           (2)
This is the child's conclusion. It contains no entropy, t, k, or
covariance-completion remainder. It is strictly smaller than o019.

## Weak testing: proved helpers, not a child

Owned WeakTesting.lean and WeakC1.lean (x0045 commits 5cabe57 and f970897)
prove the pairing justification in Lemma 3.2. They have been read and built
locally and are checked with the split. For scalar L2 H,v_r, an identity
I(H z)=sum_r I(v_r partial_r z) on compact smooth tests extends to every
C1 test z whose value and coordinate derivatives are L2.

First let z have compact support and be C1. Convolve with normalized smooth
bumps with shrinking radii, using Lebesgue measure. The convolutions are
smooth and compactly supported; they and their directional derivatives
converge pointwise to z and its derivatives. Their values and derivatives
are bounded by fixed constants, because the corresponding C1 data are
continuous and compactly supported. Since H,v_r are L1 under the finite
Gaussian measure, dominated convergence extends the identity to z.

For general C1 H1 z, choose smooth cutoffs chi_R equal to one on the ball
of radius R, with compact support, values in [0,1], and derivative bound
C/R. Apply the compact C1 identity to chi_R z. Its derivative is
chi_R partial_r z+(partial_r chi_R)z. The cutoff tends to one and its
derivative to zero. The pairing integrands are dominated by integrable
products |H z|, |v_r partial_r z|, and a constant times |v_r z|;
Cauchy--Schwarz supplies their integrability. Dominated convergence proves
the full identity. The helper is valid for any finite Borel measure in
finite dimension, not just Gaussian measure. No CFC or covariance lemma
is used in this proof.

## Checked algebra completing the proof

Apply (2) with a=k+u and b=v-K. The frozen weak Div assumption is exactly
Div(a-J,b). Apply the proved weak-testing helper entrywise to
H=u-(J-k), v-K, with tests k_ij, and sum with coefficients of P. This gives
  <u,k>_P - <J,k>_P + W(P,k)
    = sum_r <v_r,K_r>_P - sum_r W(P,K_r).                               (3)

Symmetry of P makes the weighted pairing symmetric. Expanding the two
squares on the right of (2), then using (3), yields
  W(P,k+u) + sum_r W(P,v_r-K_r)
    = 2<J,k>_P-W(P,k)-sum_r W(P,K_r)+W(P,u)+sum_r W(P,v_r).
Cyclicity of trace, symmetry of J,k,K, and kJ=t(A) identify its first
three terms with I trace(P E). Consequently
  trace(P C) <= I trace(P E)+W(P,u)+sum_r W(P,v_r).                      (4)
Pairing.lean and Completion.lean prove these finite-sum, integral, and
matrix identities, including all required integrability and factor order.

The accepted EntropyTools densityCovariance_posDef shows C positive
definite from nonnegativity, total mass one, and the finite second moment.
The log-determinant supporting plane gives
  log det C + m <= trace(P C) - log det P.
Also
  I trace E = 2 I trace t(A)-N(k)-sum_r N(K_r),
  I trace((P-I)E)=I trace(P E)-I trace E.
Combining these with (1) and (4), by linear arithmetic, gives exactly
  2m+log det C+2 integral(f log f)
    <= N(A)-N(k)-sum_r N(K_r)+I trace((P-I)E)
       +W(P,u)+sum_r W(P,v_r)-log det P,
the frozen conclusion of o019.

## Existing obligations and provenance

Searches of current lib and obligations found no theorem implying either
new interface. EntropyTools supplies covariance positivity; MatrixEntropy
supplies the supporting plane. The initial weak-testing similarity matches
became irrelevant once its complete proof was merged and its child removed.
The covariance estimate needs the resolvent cancellation by degree, which
the accepted ordinary Gaussian Poincare estimate alone does not provide.
The independent cutoff helper can be made available to the covariance child
through its shared-library package, or proved in that child's own submodule;
its proof uses only Mathlib and has no dependency on o019 or either child.

The x0045 post at 2026-10-17T06:26Z suggested the variational formulation;
its signs were independently checked against Lemma 3.2. Its message at
06:48:47Z supplied the completed entropy helper files, which were merged
and checked, eliminating the initially planned entropy child. Reports
from x0044 (06:33Z) and x0048 (06:30Z) identified the shared smooth-CFC and
weak-testing APIs. No external Lean code or network references were used.

Its messages at 06:55:44Z and 06:57:55Z supplied the complete cutoff proof
5cabe57, eliminating the proposed weak-testing child. Its 07:00Z message
and f970897 then supplied compact C1 mollification, lowering the matrix
calculus child to C1 as well. The x0063 post at 06:59Z identifies the
locally proved but not yet accepted shared C1 matrix-calculus candidate.

Local builds validate interfaces and glue against the proposed child
stubs. They do not prove those children. Only the gate decides acceptance.

## Final validation before submission

The full parent module and all owned helpers build locally. The axiom audit
of transport_covariance_completion lists exactly the two proposed child
theorems and propext, Classical.choice, Quot.sound. The entropy and weak-testing helpers' audits list only the standard
three axioms. The frozen parent statement is byte-for-byte unchanged. No sorry, admit, new axiom, or unsafe proof mechanism
occurs in the owned sources. Both child propositions elaborate with the
required imports and autoImplicit off. Both children are independent;
cutoff testing, C1 mollification and entropy have complete proofs in the
checked helper files.

lot check returned code 4, reporting that proposed child stubs are checked
by lot submit split. Thus this is a split submission, not a claim that the
analytic children or the parent have already been accepted by the gate.
