import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Data.Nat.Factorial.Basic
import Lake.Toml
import Lake.Util.Message
import Lean

/-!
# Main statement of "A sharp entropy bound and the simplex inequality for isotropic constants"

We formalise the definitions needed to state Theorem 1.1 ("The simplex inequality") of
OpenAI, *A sharp entropy bound and the simplex inequality for isotropic constants*
(October 5, 2026), Section 1 (Introduction).

Paper's definitions (Introduction): for a convex body `K ⊂ ℝⁿ`, meaning a compact convex set
with nonempty interior, write `|K|` for its Lebesgue volume,
`b_K = |K|⁻¹ ∫_K x dx` for its centroid, and
`Σ_K = |K|⁻¹ ∫_K (x - b_K)(x - b_K)ᵀ dx`.
Its isotropic constant is `L_K = (det Σ_K / |K|²)^{1/(2n)}`.

All definitions below are total (they make sense for any set `K`), but they are only
meaningful — and only used in `Challenge.lean` — for convex bodies, where every integrand is
continuous on a compact set of finite positive volume, hence integrable.
-/

set_option autoImplicit false

namespace SimplexIsotropic

open MeasureTheory

/-- A *convex body* in `ℝⁿ` (paper, Introduction): a compact convex set with nonempty
interior. `ℝⁿ` is modelled as `EuclideanSpace ℝ (Fin n)`, whose `volume` is Lebesgue
measure (the unit cube has volume one). -/
structure IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  convex : Convex ℝ K
  isCompact : IsCompact K
  interior_nonempty : (interior K).Nonempty

/-- The Lebesgue volume `|K|` of `K`, as a real number. -/
noncomputable def vol {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  volume.real K

/-- The centroid `b_K = |K|⁻¹ ∫_K x dx` (paper, Introduction). -/
noncomputable def centroid {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  (vol K)⁻¹ • ∫ x in K, x

/-- The covariance matrix `Σ_K = |K|⁻¹ ∫_K (x - b_K)(x - b_K)ᵀ dx` of the uniform
distribution on `K` (paper, Introduction), written entrywise:
`(Σ_K)ᵢⱼ = |K|⁻¹ ∫_K (xᵢ - (b_K)ᵢ) (xⱼ - (b_K)ⱼ) dx`. -/
noncomputable def covMatrix {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (vol K)⁻¹ * ∫ x in K, (x i - centroid K i) * (x j - centroid K j)

/-- The isotropic constant `L_K = (det Σ_K / |K|²)^{1/(2n)}` (paper, equation (1.1)).
The power is the real power `Real.rpow`; for a convex body `det Σ_K > 0`, so the base is
positive. -/
noncomputable def isotropicConstant {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ((covMatrix K).det / vol K ^ 2) ^ ((1 : ℝ) / (2 * n))

/-- `K` is a *simplex* in `ℝⁿ`: the convex hull of `n + 1` affinely independent points
(the vertices `v₀, …, vₙ`; paper, Section 7, "let `K = conv{v₀, …, vₙ}` be a simplex"). -/
def IsSimplex {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
    AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v)

/-- The right-hand side of the simplex inequality (paper, equation (1.2)):
`(n!)^{1/n} / ((n+1)^{(n+1)/(2n)} √(n+2))`. -/
noncomputable def simplexBound (n : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ ((1 : ℝ) / n) /
    (((n : ℝ) + 1) ^ (((n : ℝ) + 1) / (2 * n)) * Real.sqrt ((n : ℝ) + 2))

end SimplexIsotropic
