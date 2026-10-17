# Proof of o020 from two analytic inputs and proved matrix estimates

Use the exact scalar functions t,q,k,b=k',l=b',f=k(1+b),p,h,cost and
matrix fields X,Y,B,S,D,L,M from the frozen theorem. Write E for standard
Gaussian expectation and set
alpha=3/40, s=40/37, beta=7/25, gamma0=3/4,
T=S-I, H=-T(B-I), rho=(3/20)I+(1813/4000)S.
Define
v_r=D_r-beta*g_r, w_r=D_r-gamma0*g_r,
F=Y(b(A)-beta I)+sum X_r L_r, u=F+(B-I)l(A).
The witnesses and derivative residuals need not be symmetric.

Both pointwise matrix estimates are now proved in the owned helper
modules incorporated from x0048. The two new children isolate the
remaining analytic arguments. The second takes the regularity conclusion
of the first as an explicit hypothesis, so its proof can proceed without
reproving matrix functional-calculus regularity.

1. Regularity, weak witnesses, and integrability.

Smooth bounded Hermitian A has spectrum in a fixed compact interval.
For every smooth scalar function f, the entries of cfc f (A(x)) are C1
and uniformly bounded, and all their coordinate derivatives are in
Gaussian L2. One proves this from the finite-dimensional functional
calculus derivative formula, compact bounds for its divided differences,
and the entrywise L2 derivatives of A. Only C1 regularity is asserted
for the matrix field; no eigenvector is differentiated. This general
regularity statement is passed explicitly to the second child.

The scalar functions k,b,l,f,p,h are smooth. Since p is positive, its
inverse square root is smooth and bounded on the common spectral
interval. The residuals D,L,M and all products used below are therefore
L2 or products of two L2 fields. Gaussian coordinates are L2, so Y is L2.
The X_r and Y(x) are symmetric. These facts give L2 u and L2 v_r, and
integrability of the full expanded integrand and the full budget
integrand below. Individual product integrability also justifies all
finite-sum integral identities.

Differentiating t'=q and k=t/q gives q-k=a*b-l. Entrywise Gaussian
product-rule integration by parts, tested against compactly supported
smooth scalar functions, gives
q(A)-k(A)=Yb(A)+sum X_r L_r+(B-I)l(A)-partial*D+partial*K.
Subtract beta*partial*g=beta*Y to obtain
Div(u-(q(A)-k(A)),v-K), exactly with the frozen sign.

Let
  Core = -tr(Hp)+tr(T(Yh+sum X_r M_r))+tr(F^t S F)
         +sum tr(v_r^t S v_r)+(9/16)tr(T sum g_r^2),
  Comm = -tr(T b B b-T B b b)
         -2tr((T b-b T) sum X_r w_r)-tr(T sum w_r^t w_r),
  Right = -tr(H rho p)+tr(Y^2 cost)
          +sum_r [(40/37)||v_r||_F^2+(42/37)||w_r||_F^2
                   +(27/592)||g_r||_F^2+(40/3)||L_r||_F^2
                   +(5/17)||M_r p^(-1/2)||_F^2],
where all scalar functions in these displays are evaluated at A.
The first child asserts integrability of Core+Comm and Right. It also
records the elementary consequence of the individual integrability:
E Right=-E tr(H rho p(A))+E tr(Y^2 cost(A))+PB.
It asserts no inequality between these integrands and no trace expansion.

2. Exact integrated noncommuting expansion.

Assume the C1, boundedness and Gaussian L2 derivative interface supplied
by the first child. Compact-test Div(Y,g) extends to the entries of
k(A) by cutoffs and smooth approximation in Gaussian H1. Cauchy--Schwarz
makes the cutoff and approximation errors tend to zero. Consequently,
E tr(TYk(A))=sum E tr(Tg_r K_r)=sum E tr(TK_r g_r).
Gaussian integration by parts for f(A) is justified in the same way.

The scalar identity a*f-f'=2*t-k^2-b^2-1 follows from q-k=a*b-l and
b=1-k(q-a). Expand the u square using
S(B-I)=-alpha^(-1)T and (B-I)S(B-I)=alpha^(-1)H.
Expand K_r^2 using both
K_r=X_r b(A)+D_r=b(A)X_r+D_r^t.
Move b only by cyclicity and by introducing [T,b], keeping every factor
order. The terms in B-I combine to -tr(Hp) and the compensator
-tr(T b B b-T B b b). The remaining terms are Yh+sum X_r M_r
and (3/2)tr(TYk(A)). Apply the preceding weak integration identity and
complete the square D_r-(3/4)g_r. This proves exactly

  E tr(T E2)+W(S,u)+sum W(S,v_r) = tr T+E(Core+Comm).

The accepted MatrixEntropy Expansion module proves the elementary trace
identities used here. This child proves the integrated identity, without
an estimate on Core or Comm and without choosing new witnesses.

3. Proved pointwise estimates and final glue.

CommutatorInvariant.lean proves
Comm <= (42/37) sum_r ||w_r||_F^2.
It diagonalizes S and retains the compensating quadratic term. The
paired-entry coefficient reduces to
v(1-u)/(v+1/8)+u(1-v)/(u+1/8)<=1 for u,v>=0.
The Gram identity and orthogonal conjugation then give the invariant
bound. Zero eigenvalues of B cause no division by B.

Pointwise.lean proves the bound for Core by all terms of Right except
the w square. It uses the accepted MatrixEntropy block bound and weighted
completion. B is positive semidefinite; hence S is positive definite,
S<=sI, T<=(s-1)I, and T^2=alpha H S. The v and g squares have coefficients
s and (9/16)(s-1)=27/592. The block bound controls F by
s||Y(b-beta)||_F^2+(40/3)sum||L_r||_F^2.
Weighted completion with a=Yh(A), P=p(A) controls the linear T term by
tr(H(I-rho)p(A))+s*(5/96)||Yh(A)p(A)^(-1/2)||_F^2
 +(5/17)sum||M_r p(A)^(-1/2)||_F^2.
CFCProducts.lean supplies the finite-spectral identities that combine
the two Y squares into tr(Y^2 cost(A)). The reserve becomes
-tr(H rho p). This works for singular H and does not require p(A) or Y
to commute with S.

Add the two pointwise estimates to get Core+Comm<=Right. Integrate using
the integrability from the first child, substitute the exact identity
from the second and the budget normalization from the first, and subtract
log det S. The result is precisely R+PB. The explicit u,v and their weak
identity from the first child prove the frozen conclusion.

The glue uses both children, both proved pointwise helpers, one
integral_mono, and linear arithmetic. No analytic inequality is hidden
in the glue. All definitions in the two child types are expanded using
only Mathlib and ChallengeDeps.

## Gate feedback addressed

The earlier submission stopped at schema validation. Comparisons with
other obligations are kept only in the split.json distinct field. This
revision also incorporates the newly completed pointwise weighted proof,
so it creates no obligation for already proved matrix algebra.

## Validation

Both revised closed child propositions elaborate with only Mathlib and
ChallengeDeps and autoImplicit disabled. The assembly builds against their
stubs, and its frozen theorem type is byte-identical to the original.
The main axiom audit contains exactly the two proposed analytic children
and propext, Classical.choice and Quot.sound. Both incorporated pointwise
matrix estimates use only the three standard axioms.

The main glue is committed at 30126a7. lot check returned code 4, directing
proposed-stub glue to lot submit split. Its sync at lib 1b0ba6ef46 reported
no close obligations for either revised child. These local checks do not
claim gate acceptance; the resubmission requests that validation.
