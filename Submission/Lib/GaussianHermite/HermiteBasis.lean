/- Adapted from: here:o022. Original proofs by session x0047. -/
import Submission.Lib.GaussianHermite.HermiteTensor

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

noncomputable abbrev GaussianL2 (m : ℕ) :=
  Lp ℝ 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))

noncomputable def hermiteEuclidean {m : ℕ} (a : Fin m → ℕ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := hermiteTensor a (WithLp.ofLp x)

theorem measurePreserving_toLp_gaussian (m : ℕ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin m → ℝ))
      (gaussianPi m) (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  ⟨by fun_prop, map_pi_eq_stdGaussian⟩

theorem memLp_hermiteEuclidean {m : ℕ} (a : Fin m → ℕ) :
    MemLp (hermiteEuclidean a) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  (memLp_hermiteTensor a).comp_measurePreserving (measurePreserving_toLp_gaussian m).symm

theorem integral_hermiteEuclidean_mul {m : ℕ} (a b : Fin m → ℕ) :
    (∫ x, hermiteEuclidean a x * hermiteEuclidean b x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = if a = b then 1 else 0 := by
  rw [← (measurePreserving_toLp_gaussian m).integral_comp
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding]
  exact integral_hermiteTensor_mul a b

theorem ae_eq_zero_of_integral_hermiteEuclidean {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (horth : ∀ a, (∫ x, f x * hermiteEuclidean a x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0) :
    f =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin m))] 0 := by
  have h : (f ∘ (MeasurableEquiv.toLp 2 (Fin m → ℝ))) =ᵐ[gaussianPi m] 0 := by
    apply ae_eq_zero_of_integral_hermiteTensor m
      (hf.comp_measurePreserving (measurePreserving_toLp_gaussian m))
    intro a
    have ha := horth a
    rw [← (measurePreserving_toLp_gaussian m).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding] at ha
    exact ha
  have h' := (measurePreserving_toLp_gaussian m).symm.quasiMeasurePreserving.ae h
  filter_upwards [h'] with x hx
  simpa using hx

noncomputable def hermiteL2 {m : ℕ} (a : Fin m → ℕ) : GaussianL2 m :=
  (memLp_hermiteEuclidean a).toLp (hermiteEuclidean a)

theorem hermiteL2_orthonormal (m : ℕ) : Orthonormal ℝ (hermiteL2 (m := m)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro a b
  rw [hermiteL2, hermiteL2, inner_toLp_real]
  exact integral_hermiteEuclidean_mul a b

theorem inner_hermiteL2_right {m : ℕ} (f : GaussianL2 m) (a : Fin m → ℕ) :
    inner ℝ f (hermiteL2 a) =
      ∫ x, f x * hermiteEuclidean a x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_hermiteEuclidean a).coeFn_toLp] with x hx
  simp [hermiteL2, hx, mul_comm]

theorem hermiteL2_orthogonal_eq_bot (m : ℕ) :
    (Submodule.span ℝ (range (hermiteL2 (m := m))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Lp.ext
  have h := ae_eq_zero_of_integral_hermiteEuclidean (Lp.memLp f) (fun a => ?_)
  · exact h.trans (Lp.coeFn_zero _ _ _).symm
  · rw [← inner_hermiteL2_right]
    exact (Submodule.mem_orthogonal' _ _).mp hf _ (Submodule.subset_span (mem_range_self a))

/-- The normalized multivariate Hermite polynomials give the Gaussian Hilbert basis. -/
noncomputable def gaussianHermiteBasis (m : ℕ) : HilbertBasis (Fin m → ℕ) ℝ (GaussianL2 m) :=
  HilbertBasis.mkOfOrthogonalEqBot (hermiteL2_orthonormal m) (hermiteL2_orthogonal_eq_bot m)

@[simp] theorem gaussianHermiteBasis_apply {m : ℕ} (a : Fin m → ℕ) :
    gaussianHermiteBasis m a = hermiteL2 a := by
  simp [gaussianHermiteBasis]

theorem gaussianHermiteBasis_repr {m : ℕ} (f : GaussianL2 m) (a : Fin m → ℕ) :
    (gaussianHermiteBasis m).repr f a =
      ∫ x, f x * hermiteEuclidean a x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [HilbertBasis.repr_apply_apply, gaussianHermiteBasis_apply, real_inner_comm,
    inner_hermiteL2_right]

end Submission.Lib.GaussianHermite
