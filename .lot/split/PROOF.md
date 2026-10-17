# Proof of the Gaussian resolvent bound (o022)

Write E for expectation under standard Gaussian measure, D_r for coordinate
Frechet differentiation, and ||F||_2^2 for the sum of the scalar entry energies.
Set X_r=E[x_r A], Y=A-sum_r x_r X_r, Z=D A, and G=D Y.

Gaussian coordinate moments and integration by parts give E[Y]=0,
E[x_r Y]=0, and E[D_r A]=X_r. Hence Y is smooth, symmetric, and in H1,
and the orthogonal first-chaos cancellations give

  ||A||_2^2-sum_r ||Z_r||_2^2 = ||Y||_2^2-sum_r ||G_r||_2^2.

The spectral input is the improved Gaussian Poincare inequality:
for a scalar H1 function f orthogonal to constants and coordinates,

  2 E[f^2] <= sum_r E[(D_r f)^2].

One proof expands f in the multivariate normalized Hermite basis. The
coefficient of D_r f at multiindex alpha is sqrt(alpha_r+1) times the
coefficient of f at alpha+e_r. This identity follows by Gaussian integration
by parts, with compact cutoffs and L2 convergence. Parseval then identifies
the derivative energy with sum_alpha |alpha| |f_alpha|^2. The degree-zero
and degree-one coefficients vanish, proving the inequality. The existing
x0047 branch already supplies the scalar/tensor Hermite completeness; the
remaining derivative and Sobolev bridges are substantive.

On the closed Gaussian H1 space orthogonal to constants and coordinates,
use the Dirichlet form as Hilbert inner product. The improved Poincare
inequality makes f a bounded functional on this space. Riesz representation
(or the explicit Hermite multiplier 1/|alpha|) gives a potential u and
v_r=D_r u such that

  E[f z] = sum_r E[v_r D_r z],
  sum_r E[v_r^2] <= E[f^2]/2,
  sum_r E[v_r D_r f] = E[f^2].

For the first identity, extend from the orthogonal H1 space to arbitrary
compact smooth z by subtracting its constant and linear projection. The
removed linear part contributes zero because D u has mean zero. The final
identity is justified by H1 density, using f itself as the test. Equivalently,
the Hermite coefficient construction proves both identities by Parseval.

Apply this scalar construction entrywise to Y, using one representative
for each unordered pair of matrix entries. This gives pointwise symmetric
g_r, entrywise L2, and exactly the frozen weak divergence identity. Summing
the scalar estimates gives, with V=||Y||_2^2, D=sum ||G_r||_2^2,
C=sum E[G_r, g_r], and H=sum ||g_r||_2^2,

  2 V <= D,   C=V,   H<=V/2.

The quadratic in the frozen conclusion expands exactly as

  Q(G,g-G/2) = (49/50)G^2-(123/50)Gg+(68/25)g^2.

All products are integrable by L2 Holder, so finite summation and integration
preserve this identity. Therefore

  V-D+E sum Q = V-D+(49/50)D-(123/50)V+(68/25)H
             <= -D/50-(1/10)V
             <= -(7/50)V.

Combining with the first-chaos cancellation proves the frozen statement.
This route uses the same spectral gap as the paper's degreewise quadratic
factorization, but only requires three scalar energy facts at the assembly
interface. The children will separate first-chaos projection, the sharp
spectral gap, and the scalar inverse/weak-divergence construction; matrix
representatives, integral algebra, and the final rational estimate remain
in proved glue.

## Exact child interfaces and proof boundaries

1. `Entropy.gaussian_first_chaos_h1_projection` takes exactly the original
   bounded smooth centered Hermitian A and entrywise L2 derivatives. It
   gives the regularity, two moment cancellations, symmetry, and the
   value-minus-gradient energy identity for the explicitly defined Y.
   Its substantive analytic point is Gaussian integration by parts at H1
   regularity, not a new spectral theorem. The value-energy cancellation
   uses E[x_r x_s]=delta_rs and E[x_r Y]=0; the derivative cancellation
   uses E[D_r A]=X_r and D_r Y=D_r A-X_r. Boundedness supplies L2 A,
   while all products of L2 functions are integrable.

2. `Entropy.gaussian_second_chaos_gap` is scalar and has no boundedness
   assumption: it takes a smooth f with f and every D_r f in Gaussian L2,
   E[f]=0, and E[x_r f]=0, and gives the sharp factor two. It isolates
   the Hermite coefficient derivative identity/Parseval step. There is
   no weak inverse or matrix quadratic conclusion in this child.

3. `Entropy.gaussian_second_chaos_inverse` has the same scalar inputs.
   It constructs v with the compact-test adjoint identity, mixed energy
   identity, and norm bound listed above. Its sibling dependency is the
   sharp gap. To use Riesz, complete the smooth orthogonal class in the
   Dirichlet norm; the gap embeds that completion into L2 and the closed
   gradient gives its Gaussian H1 interpretation. For the Riesz potential u,
   ||Du||_2^2=E[f u]<=||f||_2||u||_2<=||f||_2||Du||_2/sqrt(2),
   proving the half-energy estimate, including Du=0. The weak derivative
   IBP identity E[D_r u]=E[x_r u]=0 follows by continuity from the smooth
   class. Subtracting the constant and linear projection of a compact
   smooth test z now gives the full frozen test class. Testing the Riesz
   equation with the given smooth f yields E[Du,Df]=E[f^2]. A Hermite
   multiplier construction is an alternative proof of this same interface.

The owned Assembly.lean proves the quadratic expansion and scalar estimate,
including all needed integrability and interchange of finite sums/integrals.
Lifting.lean invokes both scalar children for each Y entry and chooses v
only at the ordered pair (min i j,max i j). Symmetry of Y identifies the
scalar inputs for transposed entries, giving pointwise Hermitian g without
any null-set selection issue. The parent invokes the projection child and
substitutes its energy identity. Thus all three children are used.

## Available work and validation

The existing o022 branch x0047, commit 6d12a1d, has Hermite.lean,
HermiteCompleteness.lean, HermiteTensor.lean, L2Products.lean,
MomentDetermination.lean, and HermiteBasis.lean. Its gaussianHermiteBasis
is indexed by Fin m -> Nat in Gaussian L2, with coefficient integral and
completeness lemmas. These are original workspace proofs and can be reused
by the spectral children; they are not assumed as unproved glue. The x0062
06:41 post on o006 identifies pending Gaussian IBP helpers, and the x0016
06:07/06:24 posts identify first-chaos projection helpers. Child provers
should check their integration status before reimplementing these parts.

All three closed types elaborate in their generated Mathlib/ChallengeDeps
stubs. The parent and both owned glue modules build locally against them.
The similarity check reports nothing close for any of the three children.
These facts check the proposed cut and its glue; the analytic children and
therefore o022 are not claimed proved by this split.

The final local axiom audit lists exactly the three proposed children plus
propext, Classical.choice, and Quot.sound. `lot check` returned code 4 and
instructed that glue importing proposed child stubs is checked by
`lot submit split`; no standalone gate proof acceptance is claimed.
The final sync was at lib 008fe0c59b, with no similar obligations reported.
The newly accepted o025 gives an unspecified finite Gaussian Poincare
constant. It does not supply the sharp factor two after first-chaos removal
or a weak inverse, so it does not discharge either spectral child here.
