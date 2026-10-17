/- Adapted from: here:o022. Original proofs by session x0047. -/
import Submission.Lib.GaussianHermite.HermiteDerivative

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

noncomputable def coordinateSplit {m : ℕ} (r : Fin (m+1)) :
    (ℝ × (Fin m → ℝ)) ≃ᵐ EuclideanSpace ℝ (Fin (m+1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) r).symm.trans
    (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ))

@[simp] theorem coordinateSplit_apply {m : ℕ} (r : Fin (m+1)) (t : ℝ) (y : Fin m → ℝ) :
    coordinateSplit r (t,y) = WithLp.toLp 2 (r.insertNth t y) := rfl

theorem measurePreserving_coordinateSplit {m : ℕ} (r : Fin (m+1)) :
    MeasurePreserving (coordinateSplit r) ((gaussianReal 0 1).prod (gaussianPi m))
      (stdGaussian (EuclideanSpace ℝ (Fin (m+1)))) :=
  (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) r).symm.trans
    (measurePreserving_toLp_gaussian (m+1))

theorem hasDerivAt_coordinateSplit {m : ℕ} (r : Fin (m+1)) (y : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => coordinateSplit r (t,y)) (PiLp.single 2 r (1 : ℝ)) t := by
  have h : HasDerivAt (fun t : ℝ => r.insertNth (α := fun _ => ℝ) t y) (Pi.single r (1 : ℝ)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.succAboveCases r ?_ (fun j => ?_) i
    · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
      convert hasDerivAt_id t using 1 <;> rfl
    · simpa [Fin.succAbove_ne] using hasDerivAt_const t (y j)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).symm.hasFDerivAt).comp_hasDerivAt t h

@[simp] theorem hermiteEuclidean_coordinateSplit {m : ℕ} (r : Fin (m+1))
    (a : Fin (m+1) → ℕ) (t : ℝ) (y : Fin m → ℝ) :
    hermiteEuclidean a (coordinateSplit r (t,y)) =
      hermiteFunction (a r) t * hermiteTensor (fun i => a (r.succAbove i)) y := by
  unfold hermiteEuclidean hermiteTensor
  rw [Fin.prod_univ_succAbove _ r]
  simp

noncomputable def raiseIndex {m : ℕ} (a : Fin m → ℕ) (r : Fin m) : Fin m → ℕ :=
  Function.update a r (a r + 1)

@[simp] theorem raiseIndex_self {m : ℕ} (a : Fin m → ℕ) (r : Fin m) :
    raiseIndex a r r = a r + 1 := by simp [raiseIndex]

@[simp] theorem raiseIndex_succAbove {m : ℕ} (a : Fin (m+1) → ℕ) (r : Fin (m+1)) (i : Fin m) :
    raiseIndex a r (r.succAbove i) = a (r.succAbove i) := by simp [raiseIndex, Fin.succAbove_ne]

/-- Gaussian coordinate integration by parts in the Hermite basis. -/
theorem integral_coord_deriv_mul_hermite {m : ℕ} (r : Fin m)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Differentiable ℝ f)
    (hf2 : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hdf2 : MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m)))) (a : Fin m → ℕ) :
    (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) * hermiteEuclidean a x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      Real.sqrt (a r + 1 : ℝ) * ∫ x, f x * hermiteEuclidean (raiseIndex a r) x
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  cases m with
  | zero => exact Fin.elim0 r
  | succ m =>
    let e := coordinateSplit r
    have he := measurePreserving_coordinateSplit r
    let f' := fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))
    have hfprod := hf2.comp_measurePreserving he
    have hdfprod := hdf2.comp_measurePreserving he
    have hleft : Integrable (fun p => f' (e p) * hermiteEuclidean a (e p))
        ((gaussianReal 0 1).prod (gaussianPi m)) :=
      (he.integrable_comp_emb e.measurableEmbedding).mpr
        (hdf2.integrable_mul (memLp_hermiteEuclidean a))
    have hright : Integrable (fun p => f (e p) * hermiteEuclidean (raiseIndex a r) (e p))
        ((gaussianReal 0 1).prod (gaussianPi m)) :=
      (he.integrable_comp_emb e.measurableEmbedding).mpr
        (hf2.integrable_mul (memLp_hermiteEuclidean (raiseIndex a r)))
    rw [← he.integral_comp e.measurableEmbedding, ← he.integral_comp e.measurableEmbedding,
      integral_prod_symm _ hleft, integral_prod_symm _ hright, ← integral_const_mul]
    apply integral_congr_ae
    have hfa : ∀ᵐ y ∂gaussianPi m, MemLp (fun t => f (e (t,y))) 2 (gaussianReal 0 1) := by
      filter_upwards [hfprod.aestronglyMeasurable.prodMk_right, hfprod.integrable_sq.prod_left_ae]
        with y hy hy2
      exact (memLp_two_iff_integrable_sq hy).mpr hy2
    have hdfa : ∀ᵐ y ∂gaussianPi m, MemLp (fun t => f' (e (t,y))) 2 (gaussianReal 0 1) := by
      filter_upwards [hdfprod.aestronglyMeasurable.prodMk_right, hdfprod.integrable_sq.prod_left_ae]
        with y hy hy2
      exact (memLp_two_iff_integrable_sq hy).mpr hy2
    filter_upwards [hfa, hdfa] with y hy hy'
    have hd (t : ℝ) : HasDerivAt (fun t => f (e (t,y))) (f' (e (t,y))) t :=
      (hf (e (t,y))).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_coordinateSplit r y t)
    have h := integral_deriv_mul_hermiteFunction hd hy hy' (a r)
    simp only [e, hermiteEuclidean_coordinateSplit, raiseIndex_self, raiseIndex_succAbove]
    simp only [← mul_assoc, integral_mul_const]
    change (∫ t, f' (e (t,y)) * hermiteFunction (a r) t ∂gaussianReal 0 1) * _ = _
    rw [h]

end Submission.Lib.GaussianHermite
