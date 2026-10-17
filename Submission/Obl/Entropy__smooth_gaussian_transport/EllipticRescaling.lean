import Submission.Obl.Entropy__smooth_gaussian_transport.LocalizedSublevel

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def rescaledFunction {m : ℕ} (u : E m → ℝ) (c : E m) (r k : ℝ) (x : E m) : ℝ :=
  k⁻¹ * u (c + r • x)

theorem rescaledFunction_contDiff {m : ℕ} {u : E m → ℝ} {n : WithTop ENat}
    (hu : ContDiff ℝ n u) (c : E m) (r k : ℝ) :
    ContDiff ℝ n (rescaledFunction u c r k) := by
  have hs : ContDiff ℝ n (fun x : E m => r • x) := by
    fun_prop
  exact contDiff_const.mul (hu.comp (contDiff_const.add hs))

theorem rescaledFunction_gradient {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c : E m) (r k : ℝ) (x : E m) :
    gradient (rescaledFunction u c r k) x = (r / k) • gradient u (c + r • x) := by
  have hd : HasFDerivAt (rescaledFunction u c r k)
      ((r / k) • fderiv ℝ u (c + r • x)) x := by
    convert! ((hu (c + r • x)).hasFDerivAt.comp x
      (((hasFDerivAt_id x).const_smul r).const_add c)).const_mul k⁻¹ using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul]
    ring
  simp only [gradient, hd.fderiv, map_smul]

theorem rescaledFunction_gradient_hasFDerivAt {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c : E m) (r k : ℝ) (x : E m)
    (hd : DifferentiableAt ℝ (gradient u) (c + r • x)) :
    HasFDerivAt (gradient (rescaledFunction u c r k))
      ((r ^ 2 / k) • fderiv ℝ (gradient u) (c + r • x)) x := by
  rw [funext (rescaledFunction_gradient hu c r k)]
  convert! (hd.hasFDerivAt.comp x
    (((hasFDerivAt_id x).const_smul r).const_add c)).const_smul (r / k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_smul]
  congr 1
  ring

theorem rescaledFunction_gradient_lipschitz {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {L : NNReal} (hL : LipschitzWith L (gradient u))
    (c : E m) (r k : ℝ) :
    ∃ C : NNReal, LipschitzWith C (gradient (rescaledFunction u c r k)) := by
  have hmap : LipschitzWith ‖r‖₊ (fun x : E m => c + r • x) := by
    simpa only [one_mul, Function.comp_def] using
      (isometry_add_left c).lipschitz.comp (lipschitzWith_smul r)
  refine ⟨‖r / k‖₊ * (L * ‖r‖₊), ?_⟩
  rw [funext (rescaledFunction_gradient hu c r k)]
  exact (lipschitzWith_smul (r / k)).comp (hL.comp hmap)

theorem rescaledFunction_operator {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c : E m) (r k : ℝ) (x : E m)
    (hd : DifferentiableAt ℝ (gradient u) (c + r • x))
    (A : E m →L[ℝ] E m) (b : E m) :
    linearizedTrace A (fderiv ℝ (gradient (rescaledFunction u c r k)) x) -
        inner ℝ (r • b) (gradient (rescaledFunction u c r k) x) =
      (r ^ 2 / k) * (linearizedTrace A (fderiv ℝ (gradient u) (c + r • x)) -
        inner ℝ b (gradient u (c + r • x))) := by
  rw [(rescaledFunction_gradient_hasFDerivAt hu c r k x hd).fderiv,
    linearizedTrace_smul, rescaledFunction_gradient hu,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem ae_affine_dilation {m : ℕ} {P : E m → Prop} (hP : ∀ᵐ x ∂volume, P x)
    (c : E m) {r : ℝ} (hr : r ≠ 0) : ∀ᵐ x ∂volume, P (c + r • x) :=
  ((measurePreserving_add_left volume c).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hr)).ae hP

theorem volume_image_add_left {m : ℕ} (c : E m) (s : Set (E m)) :
    volume ((fun x => c + x) '' s) = volume s := by
  have he : (fun x => c + x) '' s = (fun x => -c + x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, neg_add_cancel_left] using hy
    · intro hx
      refine ⟨-c + x, hx, ?_⟩
      abel
  rw [he, measure_preimage_add]

theorem volume_affine_dilation_image {m : ℕ} (c : E m) {r : ℝ} (hr : 0 ≤ r)
    (s : Set (E m)) :
    volume ((fun x => c + r • x) '' s) = ENNReal.ofReal (r ^ m) * volume s := by
  have he : (fun x : E m => c + r • x) '' s = (fun x => c + x) '' (r • s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨r • x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [he, volume_image_add_left]
  simpa only [E, finrank_euclideanSpace_fin] using
    Measure.addHaar_smul_of_nonneg volume hr s

end Submission.Obl.Entropy__smooth_gaussian_transport
