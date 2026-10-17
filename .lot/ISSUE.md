# o041: Entropy.gaussian_weak_remainder_witnesses

Type: `∀ m:ℕ, 1 ≤ m → ∀ A:(EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA:∀ x, (A x).IsHermitian, (fun (tr:Matrix (Fin m) (Fin m) ℝ → ℝ)=> (fun c=> (fun γ=> (fun I=> (fun L2=> (fun d=> (fun Z=> (fun t=> (fun q=> (fun k=> (fun b=> (fun l=> (fun f0=> (fun p=> (fun h=> (fun cost=> (fun K=> (fun X=> (fun Y=> (fun B=> (fun S=> (fun T=> (fun H=> (fun ρ=> (fun ss=> (fun N=> (fun Div=> (fun ka=> (fun J=> (∀ i j, ContDiff ℝ ((⊤:ENat):WithTop ENat) (fun x=>A x i j)) → (∃ R:ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x=>A x i j)=0) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → (∀ a, 0 < p a) → ∀ g:Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), (∀ r x, (g r x).IsHermitian) → (∀ r, L2 (g r)) → Div Y g → (fun Dr=> (fun Lr=> (fun Mr=> (fun v=> (fun w=> (fun F=> (fun u=> (fun Core=> (fun Comm=> (fun Right=> (fun PB=> (∀ f:ℝ → ℝ, ContDiff ℝ ((⊤:ENat):WithTop ENat) f → (∀ i j, ContDiff ℝ 1 (fun x=>c f x i j)) ∧ (∃ C:ℝ, 0 < C ∧ ∀ x i j, |c f x i j| ≤ C) ∧ (∀ r, L2 (d (fun x=>c f x) r))) ∧ (∀ r, (X r).IsHermitian) ∧ (∀ x, (Y x).IsHermitian) ∧ L2 u ∧ (∀ r, L2 (v r)) ∧ Div (fun x=>u x-(J x-ka x)) (fun r x=>v r x-K r x) ∧ MeasureTheory.Integrable (fun x=>Core x+Comm x) γ ∧ MeasureTheory.Integrable Right γ ∧ I Right=-I (fun x=>tr (H*ρ*c p x))+I (fun x=>tr (Y x*Y x*c cost x))+PB) ((∑ r:Fin m, ( (40/37)*N (v r)+(42/37)*N (w r)+(27/592)*N (g r)+(40/3)*N (Lr r)+(5/17)*N (fun x=>Mr r x*cfc (fun a=>(Real.sqrt (p a))⁻¹) (A x)))))) (fun x=>-tr (H*ρ*c p x)+tr (Y x*Y x*c cost x)+(∑ r:Fin m, ( (40/37:ℝ)*ss (v r x)+(42/37:ℝ)*ss (w r x)+(27/592:ℝ)*ss (g r x)+(40/3:ℝ)*ss (Lr r x)+(5/17:ℝ)*ss (Mr r x*cfc (fun a=>(Real.sqrt (p a))⁻¹) (A x)))))) (fun x=>-tr (T*c b x*B*c b x-T*B*c b x*c b x)-2*tr ((T*c b x-c b x*T)*(∑ r:Fin m, ( X r*w r x)))-tr (T*(∑ r:Fin m, ( (w r x).transpose*w r x))))) (fun x=>-tr (H*c p x)+tr (T*(Y x*c h x+(∑ r:Fin m, ( X r*Mr r x))))+tr ((F x).transpose*S*F x)+(∑ r:Fin m, ( tr ((v r x).transpose*S*v r x)))+(9/16:ℝ)*tr (T*(∑ r:Fin m, ( g r x*g r x))))) (fun x=>F x+(B-1)*c l x)) (fun x=>Y x*(c b x-(7/25:ℝ) • 1)+(∑ r:Fin m, ( X r*Lr r x)))) (fun r x=>Dr r x-(3/4:ℝ) • g r x)) (fun r x=>Dr r x-(7/25:ℝ) • g r x)) (fun r x=>d (fun y=>c f0 y) r x-X r*cfc (deriv f0) (A x)-2 • (Dr r x*c b x)-(80/3:ℝ) • (Lr r x*c l x)+(3/2:ℝ) • (g r x*c b x))) (fun r x=>d (fun y=>c b y) r x-X r*c l x)) (fun r x=>K r x-X r*c b x)) (fun x=>c q x)) (fun x=>c k x)) (fun F v=>∀ i j, ∀ z:(EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤:ENat):WithTop ENat) z → HasCompactSupport z → I (fun x=>F x i j*z x)=(∑ r:Fin m, ( I (fun x=>v r x i j*fderiv ℝ z x (PiLp.single 2 r (1:ℝ))))))) (fun F=>I (fun x=>ss (F x)))) (fun Q=>(∑ i:Fin m, ( (∑ j:Fin m, ( (Q i j)^2)))))) ((3/20:ℝ) • (1:Matrix (Fin m) (Fin m) ℝ)+(1813/4000:ℝ) • S)) (-T*(B-1))) (S-1)) ((((37/40:ℝ) • (1:Matrix (Fin m) (Fin m) ℝ)+(3/40:ℝ) • B)⁻¹))) ((∑ r:Fin m, ( X r*X r)))) (fun x=>A x-(∑ r:Fin m, ( x r • X r)))) (fun r:Fin m=>Matrix.of (fun i j=>I (fun x=>x r*A x i j)))) (d (fun x=>c k x))) (fun a=>(40/37)*((b a-7/25)^2+(5/96)*(h a)^2 / p a))) (fun a=>k a*(1+b a)-(3/2)*k a-(80/3)*(b a-7/25)*l a)) (fun a=>deriv f0 a-(b a)^2-(40/3)*(l a)^2)) (fun a=>k a*(1+b a))) (deriv b)) (deriv k)) (fun a=>t a / q a)) (fun a:ℝ=>ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a:ℝ=>-Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (d A)) (fun (F:(EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) (r:Fin m) (x:EuclideanSpace ℝ (Fin m))=>Matrix.of (fun i j=>fderiv ℝ (fun y=>F y i j) x (PiLp.single 2 r (1:ℝ))))) (fun F=>∀ i j, MeasureTheory.MemLp (fun x=>F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun (f:ℝ → ℝ) x=>cfc f (A x))) (Matrix.trace)`

Statement: Smooth scalar functional calculus of bounded smooth Hermitian A is entrywise C1, bounded and Gaussian H1. Construct the explicit L2 weak covariance witnesses, establish integrability of the expanded/budget integrands, and normalize the budget integral. No expanded trace identity or matrix inequality is asserted.

Role in the glue of o020: Supplies CFC regularity to the exact-expansion child, and provides the explicit witnesses, their L2 and weak divergence properties, integrability for integral_mono and budget normalization.

Depends on: none
Weight: 5
Module: Submission/Obl/Entropy__gaussian_weak_remainder_witnesses.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

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

  E tr(T E2)+W(S,u)+sum W(S,v_r) = tr T+
