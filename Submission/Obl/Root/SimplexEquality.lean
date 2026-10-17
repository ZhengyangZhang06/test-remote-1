import Submission.Obl.Root.Reduction
import Submission.Obl.Root.Exponential
import Submission.Obl.Cone__moments
import Submission.Obl.Cone__simplex_iff_product

open SimplexIsotropic MeasureTheory

namespace Submission.Obl.Root

/-- Every simplex attains the dimensional bound, by its exponential-product cone law. -/
theorem simplex_attains_bound (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) (hs : IsSimplex K) :
    isotropicConstant K = simplexBound n := by
  obtain ⟨L, b, he⟩ :=
    (Submission.Cone.simplex_iff_product n hn K hK (coneDensity K) rfl).mpr hs
  have hentropy := DensityAffine.entropy_equality_of_ae_affine_product L b he
  change densityEntropy (coneDensity K) =
    (n + 1 : ℕ) + Real.log (densityCov (coneDensity K)).det / 2 at hentropy
  exact (isotropicConstant_eq_iff_cone_entropy_eq n hn K hK).mpr hentropy

end Submission.Obl.Root
