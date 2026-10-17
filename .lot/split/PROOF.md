# Paper proof of normalized_remainder (o006)

This cut follows Theorem 3.1 of the supplied paper, with the analytic inputs
of Lemma 2.4 and Proposition 2.5 and the estimates of Sections 3--4.
All definitions below will be expanded in the closed child propositions;
no new definition is assumed as an axiom.

Write gamma for standard Gaussian measure and E for its expectation.
Set t(a)=-log Phi(-a), q(a)=varphi(a)/Phi(-a), k=t/q,
b=k', l=b', f=k(1+b), alpha=3/40, s=40/37, beta=7/25,
c=3/2, gamma0=3/4, epsilon=3/20, kappa=49/100,
p=f'-b^2-l^2/alpha, e=f'-2b^2-2l^2/alpha,
and h0=f-ck-2(b-beta)l/alpha.

The hypotheses give a smooth convex gradient transport with bounded
symmetric A, J=q(A), and E A=0. Since q is positive and continuous,
bounded A bounds J above and away from zero. The pushforward identity
and change of variables give the density equation. Lemma 2.4 justifies
its differentiated versions by compact cutoffs and gives Gaussian H1
regularity of A and k(A). Entropy change of variables and
log q(a)=-a^2/2-log(2*pi)/2+t(a) give
D=2m+log det C-2H=E tr(A^2-2t(A))+log det C+m.

Put X_r=E(x_r A), Y=A-sum_r x_r X_r, B=sum_r X_r^2,
Z_r=partial_r A, G_r=partial_r Y, g_r=partial_r N^{-1}Y,
and V0=||G||^2-||Y||^2. The X_r are symmetric, so B is positive
semidefinite; it is not assumed positive definite. The zero mean and
first-chaos subtraction put Y in Gaussian chaoses of degree at least two.
Thus partial* g=Y. Covariance completion (Lemma 3.2) gives
C=W+E(2t-k^2-sum_r K_r^2), K_r=partial_r k(A),
where W is the H^{-1} row Gram matrix of U=q-(Id+N)k. For any
representation U=u-partial* v its weighted trace is at most
||u||_S^2+||v||_S^2. Proposition 2.5 supplies the eigenvalue separation
surplus Csep in E tr k^2 >= ||Z||^2-||K||^2+Csep.

Let S=((37/40)I+(3/40)B)^{-1}, T=S-I, Hmat=-T(B-I),
and rho=(3/20)I+(49/100)(37/40)S. The log-determinant supporting
plane and covariance completion imply equation (3.10), the paper's
reduction of D to -V0-Csep plus matrix terms.

Use D_r=K_r-X_r b and L_r=partial_r b-X_r l. The identity
q-k=ab-l gives U=Yb+sum X_r L_r+(B-I)l-partial* D.
Lemma 3.3 expands the covariance bound with all factor orders retained.
Lemma 3.4 controls the commutator and its compensating quadratic term
by (1+s/8)||D-gamma0*g||^2. Block Cauchy--Schwarz bounds the
remaining S square, and weighted completion reserves -E tr(Hmat rho p).
The resulting scalar absorption expression is
Rabs=tr(T-log S)-E tr(Hmat rho p(A))
 +s E tr(Y^2 ((b-beta)^2+alpha*h0^2/(4(1-epsilon-kappa)p))(A)).
The other terms are the derivative residual squares in (3.23).

Proposition 3.5 proves
Rabs <= (69/500)||Y||^2 - (1/1000) sum_i omega(lambda_i(B)).
It uses the averaged spectral measure of A along each B eigenvector,
whose first two moments are 0 and lambda_i+E||Y v_i||^2, and a
quadratic minorant of p. The logarithmic supporting-plane cost is
absorbed while keeping exactly omega, including its cutoff 13/100 at
lambda=0. No simultaneous diagonalization of A and B is used.

Proposition 3.6 bounds the remaining derivative residual squares,
entrywise in an eigenbasis of A and averaged over transposed entries,
by sum Q(G,g-G/2)+Csep, where
Q(u,v)=(43/100)u^2+(26/100)uv+(68/25)v^2.
The separation surplus cancels. On chaos degree d>=2, g=G/d and
||G||^2=d||Y||^2. The exact scalar factorization already proved in
Submission.Lib.EntropyTools.Remainder gives
sum Q(G,g-G/2) <= V0-(7/50)||Y||^2.
Therefore D <= ((69/500)-(7/50))||Y||^2-Omega/1000
= -||Y||^2/500-Omega/1000, proving the frozen conclusion.

The six interfaces below cover these paper steps. The Lean glue combines
them by definitional substitution and ordered-ring arithmetic. No analytic
child is claimed proved by this submission.

## Final six-child interfaces

The final cut separates the two-eigenvalue certificate from matrix algebra:

1. `Entropy.transport_energy_surplus` is Lemma 2.4 and Proposition 2.5.
   It gives entrywise L2 derivatives Z=partial A and K=partial k(A),
   and ||Z||^2-||K||^2+Csep <= ||k(A)||^2. It does not assume E A=0.
2. `Entropy.transport_covariance_completion` is the entropy identity and
   Lemma 3.2, followed by the log-determinant supporting plane. For every
   positive definite P and square-integrable u,v satisfying
   u-partial* v=q(A)-k(A)-partial* K weakly, it gives
   D <= ||A||^2-||k(A)||^2-||K||^2
      + E tr((P-I)(2t-k^2-sum K_r^2))
      + ||u||_P^2+sum ||v_r||_P^2-log det P.
   It works for any nonnegative probability density with finite second
   moment and entropy, supplied with the smooth bounded-Jacobian transport.
3. `Entropy.gaussian_chaos_resolvent` constructs a symmetric L2 family g
   with partial* g=Y and
   ||A||^2-||Z||^2+Qenergy <= -(7/50)||Y||^2.
   Its proof uses the existing EntropyTools scalar polynomial, plus the
   Gaussian spectral decomposition and first-chaos identities. The weak
   divergence is tested entrywise against all smooth compactly supported
   real functions; its sign is E(Y z)=sum E(g_r partial_r z).
4. `Entropy.integrated_two_eigenvalue` is Proposition 3.6, integrated
   in a pointwise eigenbasis. It proves p>0 and PB <= Qenergy+Csep.
   The basis is the canonical unitary eigenbasis of the symmetric A(x).
   Eigenvalues appear only in the basis-invariant separation sum, and no
   eigenvector is differentiated. The m0 cutoff uses the right-hand
   interval at each endpoint, exactly as in (2.8).
5. `Entropy.noncommuting_remainder_assembly` is Lemmas 3.3--3.4 and
   the block and weighted completions. Given p>0 and the g from step 3,
   it constructs L2 u,v satisfying the weak identity in step 2 and gives
   E tr((S-I)(2t-k^2-sum K_r^2))
      +||u||_S^2+sum ||v_r||_S^2-log det S <= Rabs+PB.
   This theorem assumes p>0 explicitly and lists the pair-estimate child
   as its sibling dependency. It contains no scalar certificate estimate.
6. `Entropy.first_chaos_absorption` is Proposition 3.5, namely
   Rabs <= (69/500)||Y||^2-Omega/1000.
   It uses only bounded smooth symmetric mean-zero A, not the transport.

Here the derivative budget PB is the sum over r of
(40/37)||D_r-(7/25)g_r||^2+(42/37)||D_r-(3/4)g_r||^2
+(27/592)||g_r||^2+(40/3)||L_r||^2+(5/17)||M_r p(A)^(-1/2)||^2.
The coefficients are respectively s, 1+s/8, gamma0^2(s-1),
1/alpha and 1/(4(1-epsilon)); these are exact rational simplifications.
The fixed-coordinate formula for M_r is
partial_r f(A)-X_r f'(A)-2D_r b(A)-(80/3)L_r l(A)
 +(3/2)g_r b(A), equivalent to (3.18) by the divided-difference formula.
The absorption cost uses (5/96)h0^2/p=alpha*h0^2/(4(1-epsilon-kappa)p)
and rho=(3/20)I+(1813/4000)S. These identities explain every rational
simplification made in the frozen child statements.

The glue supplies hB from firstGram_posSemidef and S>0 from dualS_posDef,
both proved helpers from x0016. It applies the six children and eliminates
PB, Csep, ||k(A)||^2, ||K||^2, ||Z||^2, and Qenergy by linear arithmetic.
This is exactly the cancellation in the paper, with no implicit
integrability lemma or spectral construction in the glue.

## Validation

All six closed propositions elaborate using only Mathlib and ChallengeDeps
with autoImplicit disabled. lot sync generated their stubs and reported no
similar obligations. The parent module and every owned helper build locally
against these stubs. These checks validate the proposed interfaces and glue;
they do not prove the analytic children. The gate is the authority for the
split and for eventual acceptance of the parent.

The final local axiom audit of normalized_remainder lists exactly the six
proposed child theorems and propext/Classical.choice/Quot.sound. lot check
returned code 4: glue importing proposed child stubs is checked by
lot submit split. Thus no gate proof acceptance is claimed.
