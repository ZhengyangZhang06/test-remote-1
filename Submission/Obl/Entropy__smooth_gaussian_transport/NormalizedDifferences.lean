import Submission.Obl.Entropy__smooth_gaussian_transport.SecondDifferenceEquation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gradient_const_mul_of_differentiable {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c : ℝ) (x : E m) :
    gradient (fun y => c * u y) x = c • gradient u x := by
  simp only [gradient, (hu x).hasFDerivAt.const_mul c |>.fderiv, map_smul]

theorem linearizedTransport_const_mul {m : ℕ} (V u : E m → ℝ) {w : E m → ℝ}
    (hw : Differentiable ℝ w) {x : E m} (hd : DifferentiableAt ℝ (gradient w) x) (c : ℝ) :
    linearizedTransport V u (fun y => c * w y) x = c * linearizedTransport V u w x := by
  have he := funext (gradient_const_mul_of_differentiable hw c)
  have hder : HasFDerivAt (gradient (fun y => c * w y))
      (c • fderiv ℝ (gradient w) x) x := by
    rw [he]
    exact hd.hasFDerivAt.const_smul c
  rw [linearizedTransport, hder.fderiv, linearizedTrace_smul,
    gradient_const_mul_of_differentiable hw, real_inner_smul_right, linearizedTransport]
  ring

theorem gradient_const_sub_of_differentiable {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c : ℝ) (x : E m) :
    gradient (fun y => c - u y) x = -gradient u x := by
  have hd : HasFDerivAt (fun y => c - u y) (-fderiv ℝ u x) x := by
    convert! (hasFDerivAt_const c x).sub (hu x).hasFDerivAt using 1
    simp only [zero_sub]
  simp only [gradient, hd.fderiv, map_neg]

theorem linearizedTransport_const_sub {m : ℕ} (V u : E m → ℝ) {w : E m → ℝ}
    (hw : Differentiable ℝ w) {x : E m} (hd : DifferentiableAt ℝ (gradient w) x) (c : ℝ) :
    linearizedTransport V u (fun y => c - w y) x = -linearizedTransport V u w x := by
  have he := funext (gradient_const_sub_of_differentiable hw c)
  have hder : HasFDerivAt (gradient (fun y => c - w y))
      (-fderiv ℝ (gradient w) x) x := by
    rw [he]
    exact hd.hasFDerivAt.neg
  simp only [linearizedTransport, hder.fderiv, gradient_const_sub_of_differentiable hw,
    linearizedTrace, operatorMatrix, ContinuousLinearMap.toLinearMap_neg, map_neg,
    Matrix.mul_neg, Matrix.trace_neg, inner_neg_right]
  ring

noncomputable def normalizedSecondDifference {m : ℕ} (u : E m → ℝ) (h x : E m) : ℝ :=
  (2 / ‖h‖ ^ 2) * secondDifference u h x

theorem normalizedSecondDifference_contDiff {m : ℕ} {u : E m → ℝ}
    {n : WithTop ENat} (hu : ContDiff ℝ n u) (h : E m) :
    ContDiff ℝ n (normalizedSecondDifference u h) :=
  contDiff_const.mul (secondDifference_contDiff hu h)

theorem gradient_secondDifference_lipschitz {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : ℝ≥0} (hL : LipschitzWith L (gradient u)) (h : E m) :
    ∃ C : ℝ≥0, LipschitzWith C (gradient (secondDifference u h)) := by
  have hp : LipschitzWith L (fun x => gradient u (x + h)) := by
    simpa only [mul_one, Function.comp_def] using hL.comp (isometry_add_right h).lipschitz
  have hn : LipschitzWith L (fun x => gradient u (x - h)) := by
    simpa only [mul_one, Function.comp_def, sub_eq_add_neg] using
      hL.comp (isometry_add_right (-h)).lipschitz
  have havg := (lipschitzWith_smul (1 / 2 : ℝ)).comp (hp.add hn)
  refine ⟨‖(1 / 2 : ℝ)‖₊ * (L + L) + L, ?_⟩
  rw [funext (gradient_secondDifference hu h)]
  simpa only [Function.comp_def] using havg.sub hL

theorem gradient_normalizedSecondDifference_lipschitz {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : ℝ≥0} (hL : LipschitzWith L (gradient u)) (h : E m) :
    ∃ C : ℝ≥0, LipschitzWith C (gradient (normalizedSecondDifference u h)) := by
  obtain ⟨C, hC⟩ := gradient_secondDifference_lipschitz hu hL h
  have he : gradient (normalizedSecondDifference u h) = fun x =>
      (2 / ‖h‖ ^ 2) • gradient (secondDifference u h) x :=
    funext (gradient_const_mul_of_differentiable
      (secondDifference_contDiff hu h).differentiable_one _)
  refine ⟨‖(2 / ‖h‖ ^ 2 : ℝ)‖₊ * C, ?_⟩
  rw [he]
  simpa only [Function.comp_def] using (lipschitzWith_smul (2 / ‖h‖ ^ 2)).comp hC

/-- Normalization removes the step size from the elliptic forcing bound. -/
theorem brenier_normalized_secondDifference_subsolution {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {h : E m} (hh : h ≠ 0) :
    ContDiff ℝ 1 (normalizedSecondDifference φ h) ∧
      (∀ x, 0 ≤ normalizedSecondDifference φ h x ∧
        normalizedSecondDifference φ h x ≤ 2 / Real.sqrt a) ∧
      (∃ C : ℝ≥0, LipschitzWith C (gradient (normalizedSecondDifference φ h))) ∧
      ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient (normalizedSecondDifference φ h)) x ∧
        -1 ≤ linearizedTransport V φ (normalizedSecondDifference φ h) x := by
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hsq : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
  have hc : 0 < 2 / ‖h‖ ^ 2 := div_pos (by norm_num) hsq
  refine ⟨normalizedSecondDifference_contDiff hC1 h, ?_,
    gradient_normalizedSecondDifference_lipschitz hC1
      (brenier_gradient_lipschitz hm hV ha hH hφ hlaw) h, ?_⟩
  · intro x
    have hlo : 0 ≤ secondDifference φ h x := sub_nonneg.mpr (le_symmetricAverage hφ h x)
    have hhi : secondDifference φ h x ≤ ‖h‖ ^ 2 / Real.sqrt a :=
      brenier_global_second_difference hm hV ha hH hφ hlaw h x
    refine ⟨mul_nonneg hc.le hlo, ?_⟩
    have hb := mul_le_mul_of_nonneg_left hhi hc.le
    change (2 / ‖h‖ ^ 2) * secondDifference φ h x ≤ _
    convert! hb using 1
    field_simp [hsq.ne']
  · have hVc : ConvexOn ℝ univ V := convex_of_hessian_nonneg hV (fun x v =>
      (mul_nonneg ha.le (sq_nonneg _)).trans (hH x v))
    filter_upwards [brenier_ae_linearized_secondDifference hm (hV.of_le (by norm_num))
      hVc hφ hlaw h] with x hx
    have he : gradient (normalizedSecondDifference φ h) = fun y =>
        (2 / ‖h‖ ^ 2) • gradient (secondDifference φ h) y :=
      funext (gradient_const_mul_of_differentiable
        (secondDifference_contDiff hC1 h).differentiable_one _)
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (hx.1.hasFDerivAt.const_smul (2 / ‖h‖ ^ 2 : ℝ)).differentiableAt
    · change -1 ≤ linearizedTransport V φ
        (fun y => (2 / ‖h‖ ^ 2) * secondDifference φ h y) x
      rw [linearizedTransport_const_mul V φ
        (secondDifference_contDiff hC1 h).differentiable_one hx.1]
      have hb := mul_le_mul_of_nonneg_left hx.2 hc.le
      have hcancel : (2 / ‖h‖ ^ 2) * (-‖h‖ ^ 2 / 2) = -1 := by field_simp [hsq.ne']
      rwa [hcancel] at hb

/-- The complement of a normalized second difference is a nonnegative
supersolution to which the contact-measure estimates apply. -/
theorem brenier_secondDifference_complement {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {h : E m} (hh : h ≠ 0) {M : ℝ} (hM : 2 / Real.sqrt a ≤ M) :
    ContDiff ℝ 1 (fun x => M - normalizedSecondDifference φ h x) ∧
      (∀ x, 0 ≤ M - normalizedSecondDifference φ h x) ∧
      (∃ C : ℝ≥0, LipschitzWith C (gradient (fun x => M - normalizedSecondDifference φ h x))) ∧
      ∀ᵐ x ∂volume,
        DifferentiableAt ℝ (gradient (fun x => M - normalizedSecondDifference φ h x)) x ∧
          linearizedTransport V φ (fun x => M - normalizedSecondDifference φ h x) x ≤ 1 := by
  obtain ⟨hq, hqb, ⟨C, hC⟩, hqeq⟩ :=
    brenier_normalized_secondDifference_subsolution hm hV ha hH hφ hlaw hh
  have hg : gradient (fun x => M - normalizedSecondDifference φ h x) =
      fun x => -gradient (normalizedSecondDifference φ h) x :=
    funext (gradient_const_sub_of_differentiable hq.differentiable_one M)
  refine ⟨contDiff_const.sub hq, fun x => sub_nonneg.mpr ((hqb x).2.trans hM), ?_, ?_⟩
  · refine ⟨C, ?_⟩
    rw [hg]
    exact hC.neg
  · filter_upwards [hqeq] with x hx
    refine ⟨?_, ?_⟩
    · rw [hg]
      exact hx.1.neg
    · rw [linearizedTransport_const_sub V φ hq.differentiable_one hx.1]
      linarith [hx.2]

end Submission.Obl.Entropy__smooth_gaussian_transport
