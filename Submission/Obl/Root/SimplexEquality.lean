import Submission.Obl.Root.ConeReduction
import Submission.Obl.Root.Exponential
import Submission.Obl.Cone__moments
import Submission.Obl.Cone__simplex_iff_product

open SimplexIsotropic MeasureTheory

namespace Submission.Obl.Root

/-- Every simplex attains the dimensional bound, by its exponential-product cone law. -/
theorem simplex_attains_bound (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) (hs : IsSimplex K) :
    isotropicConstant K = simplexBound n := by
  obtain ⟨hv, hd, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, hH, hC⟩ :=
    Submission.Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  obtain ⟨L, b, he⟩ :=
    (Submission.Cone.simplex_iff_product n hn K hK (coneDensity K) rfl).mpr hs
  have hentropy := DensityAffine.entropy_equality_of_ae_affine_product L b he
  change densityEntropy (coneDensity K) =
    (n + 1 : ℕ) + Real.log (densityCov (coneDensity K)).det / 2 at hentropy
  exact (isotropicConstant_eq_iff_det_eq n hn K hv hd.le).mpr
    ((cone_entropy_eq_iff_det_eq n K hv hd hH hC).mp hentropy)

end Submission.Obl.Root
