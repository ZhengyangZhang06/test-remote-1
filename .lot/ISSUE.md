# o038: Entropy.gaussian_first_chaos_h1_projection

Type: `∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, (∀ x, (A x).IsHermitian) → (fun γ => (fun I => (fun L2 => (fun d => (fun X => (fun Y => (fun N => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (d A r)) → (∀ x, (Y x).IsHermitian) ∧ (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => Y x i j)) ∧ L2 Y ∧ (∀ r, L2 (d Y r)) ∧ (∀ i j, I (fun x => Y x i j) = 0) ∧ (∀ r i j, I (fun x => x r * Y x i j) = 0) ∧ N A - Finset.sum Finset.univ (fun r : Fin m => N (d A r)) = N Y - Finset.sum Finset.univ (fun r : Fin m => N (d Y r))) (fun F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r : Fin m => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))`

Statement: Subtracting the Gaussian first-chaos projection of a bounded smooth centered symmetric matrix field preserves H1 regularity, removes constants and coordinates, and cancels the first-chaos contributions to the value-minus-gradient energy.

Role in the glue of o022: Supplies all hypotheses for the scalar children on each entry of Y and the exact original-to-Y energy cancellation.

Depends on: none
Weight: 3
Module: Submission/Obl/Entropy__gaussian_first_chaos_h1_projection.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

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
  
