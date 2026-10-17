import Submission.Obl.Entropy__smooth_gaussian_transport.BrenierWeakHarnack

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Weak Harnack is invariant under translation and shrinking space. The
forcing is normalized by any positive amplitude at least the radius squared. -/
theorem exists_scaled_weakHarnack {m : ℕ} (hm : 1 ≤ m) {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (u : E m → ℝ) (L : NNReal) (A : E m → E m →L[ℝ] E m) (b : E m → E m)
        (Ω : Set (E m)), ContDiff ℝ 1 u → LipschitzWith L (gradient u) →
        (∀ z ∈ Ω, 0 ≤ u z) →
        (∀ᵐ z ∂volume, z ∈ Ω → ‖b z‖ ≤ M ∧
          (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
            δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
          linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) →
        (∀ᵐ z ∂volume, z ∈ Ω →
          linearizedTrace (A z) (fderiv ℝ (gradient u) z) -
            inner ℝ (b z) (gradient u z) ≤ 1) →
        ∀ (c : E m) (r k : ℝ), 0 < r → r ≤ 1 → r ^ 2 ≤ k →
          (∀ z ∈ Metric.closedBall (0 : E m) (m + 4), c + r • z ∈ Ω) →
          HasWeakHarnackTail (rescaledFunction u c r k) Q θ := by
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := exists_elliptic_weakHarnack hm hδ hΛ hM
  refine ⟨Q, θ, hQ, hθ, hθ1, ?_⟩
  intro u L A b Ω hu hLip hu0 hcoeff hineq c r k hr hr1 hk hinside
  have hk0 : 0 < k := (sq_pos_of_pos hr).trans_le hk
  obtain ⟨C, hC⟩ := rescaledFunction_gradient_lipschitz hu.differentiable_one hLip c r k
  apply hweak _ C (fun z => A (c + r • z)) (fun z => r • b (c + r • z))
    (rescaledFunction_contDiff hu c r k) hC
  · intro z hz
    exact mul_nonneg (inv_nonneg.mpr hk0.le) (hu0 _ (hinside z hz))
  · filter_upwards [ae_affine_dilation hcoeff c hr.ne'] with z hz
    intro hzi
    obtain ⟨hb, hell, htrace⟩ := hz (hinside z hzi)
    refine ⟨?_, hell, htrace⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      r * ‖b (c + r • z)‖ ≤ r * M := mul_le_mul_of_nonneg_left hb hr.le
      _ ≤ M := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hM
  · filter_upwards [ae_affine_dilation hineq c hr.ne',
      ae_affine_dilation (hLip.ae_differentiableAt (μ := volume)) c hr.ne'] with z hz hd
    intro hzi
    rw [rescaledFunction_operator hu.differentiable_one c r k z hd]
    calc
      _ ≤ (r ^ 2 / k) * 1 := mul_le_mul_of_nonneg_left (hz (hinside z hzi))
        (div_nonneg (sq_nonneg _) hk0.le)
      _ ≤ 1 := by rw [mul_one]; exact (div_le_one hk0).mpr hk

/-- The measure-to-point estimate in physical coordinates. The same constant
works at every center and scale for fixed coefficient bounds. -/
theorem exists_scaled_measure_to_point {m : ℕ} (hm : 1 ≤ m) {δ Λ M σ : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : E m → ℝ) (L : NNReal) (A : E m → E m →L[ℝ] E m) (b : E m → E m)
        (Ω : Set (E m)), ContDiff ℝ 1 u → LipschitzWith L (gradient u) →
        (∀ z ∈ Ω, 0 ≤ u z) →
        (∀ᵐ z ∂volume, z ∈ Ω → ‖b z‖ ≤ M ∧
          (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
            δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
          linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) →
        (∀ᵐ z ∂volume, z ∈ Ω →
          linearizedTrace (A z) (fderiv ℝ (gradient u) z) -
            inner ℝ (b z) (gradient u z) ≤ 1) →
        ∀ (c : E m) (r k t : ℝ), 0 < r → r ≤ 1 → r ^ 2 ≤ k →
          (∀ z ∈ Metric.closedBall (0 : E m) (m + 4), c + r • z ∈ Ω) →
          ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
            volume ({y : Fin m → ℝ | t ≤ u (c + r • WithLp.toLp 2 y)} ∩
              (unitCoordinateBox m : Set (Fin m → ℝ))) →
          ∀ x ∈ closedBoxRegion (unitCoordinateBox m),
            t ≤ C * max k (u (c + r • x)) := by
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := exists_scaled_weakHarnack hm hδ hΛ hM
  obtain ⟨C, hC, hpoint⟩ := weakHarnack_measure_to_point hQ hθ hθ1 hσ
  refine ⟨C, hC, ?_⟩
  intro u L A b Ω hu hLip hu0 hcoeff hineq c r k t hr hr1 hk hinside hmass x hx
  have hk0 : 0 < k := (sq_pos_of_pos hr).trans_le hk
  have htail := hweak u L A b Ω hu hLip hu0 hcoeff hineq c r k hr hr1 hk hinside
  have hm' : ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
      volume ({y : Fin m → ℝ | t / k ≤ rescaledFunction u c r k (WithLp.toLp 2 y)} ∩
        (unitCoordinateBox m : Set (Fin m → ℝ))) := by
    convert! hmass using 2
    ext y
    simp only [rescaledFunction, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hk0]
  have hh := hpoint _ htail (t / k) hm' x hx
  have hb := mul_le_mul_of_nonneg_left hh hk0.le
  have he : k * (C * max 1 (rescaledFunction u c r k x)) =
      C * max k (u (c + r • x)) := by
    rw [mul_left_comm k C, mul_max_of_nonneg _ _ hk0.le, mul_one]
    congr 2
    dsimp only [rescaledFunction]
    rw [← mul_assoc, mul_inv_cancel₀ hk0.ne', one_mul]
  rw [he] at hb
  simpa only [mul_div_cancel₀ t hk0.ne'] using hb

end Submission.Obl.Entropy__smooth_gaussian_transport
