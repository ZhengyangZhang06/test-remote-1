import Submission.Obl.Entropy__smooth_gaussian_transport.Brenier

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem volume_image_zero_of_lipschitz {m : ℕ} {f : E m → E m} {L : NNReal}
    (hf : LipschitzWith L f) {s : Set (E m)} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  let μ : Measure (E m) := Measure.hausdorffMeasure (Module.finrank ℝ (E m))
  have hμv : μ ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure μ volume
  have hvμ : (volume : Measure (E m)) ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure volume μ
  apply hvμ
  have hμs : μ s = 0 := hμv hs
  have hb := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ (E m) : ℝ)) (by positivity) s
  change μ (f '' s) ≤ (L : ENNReal) ^ (Module.finrank ℝ (E m) : ℝ) * μ s at hb
  simpa only [hμs, mul_zero, nonpos_iff_eq_zero] using hb

/-- The inverse of a Lipschitz homeomorphism of Euclidean space is
differentiable almost everywhere. Singular derivative points have null image
by the equal-dimension Sard lemma, and the remaining exceptional set has null
image by the Lipschitz bound. -/
theorem ae_differentiable_inverse_of_lipschitz {m : ℕ} (e : E m ≃ₜ E m)
    {L : NNReal} (he : LipschitzWith L e) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ e.symm x := by
  let N : Set (E m) := {x | ¬ DifferentiableAt ℝ e x}
  let S : Set (E m) := {x | DifferentiableAt ℝ e x ∧ (fderiv ℝ e x).det = 0}
  have hN : volume N = 0 := by
    exact ae_iff.mp (he.ae_differentiableAt (μ := volume))
  have hNim : volume (e '' N) = 0 := volume_image_zero_of_lipschitz he hN
  have hSim : volume (e '' S) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x (hx : x ∈ S) => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun x hx => hx.2)
  have hgood : ∀ᵐ x ∂volume, x ∉ e '' N ∧ x ∉ e '' S :=
    (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hNim)).and
      (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hSim))
  filter_upwards [hgood] with x hx
  have hd : DifferentiableAt ℝ e (e.symm x) := by
    by_contra hd
    exact hx.1 ⟨e.symm x, hd, e.apply_symm_apply x⟩
  have hdet : (fderiv ℝ e (e.symm x)).det ≠ 0 := by
    intro hdet
    exact hx.2 ⟨e.symm x, ⟨hd, hdet⟩, e.apply_symm_apply x⟩
  let A := (fderiv ℝ e (e.symm x)).toContinuousLinearEquivOfDetNeZero hdet
  have hA : HasFDerivAt e (A : E m →L[ℝ] E m) (e.symm x) := by
    simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hd.hasFDerivAt
  exact (hA.of_local_left_inverse e.symm.continuous.continuousAt
    (Eventually.of_forall e.apply_symm_apply)).differentiableAt

end Submission.Obl.Entropy__smooth_gaussian_transport
