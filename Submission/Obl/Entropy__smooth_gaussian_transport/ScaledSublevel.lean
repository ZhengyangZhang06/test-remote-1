import Submission.Obl.Entropy__smooth_gaussian_transport.EllipticRescaling

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem affine_dilation_image_sublevel {m : ℕ} (u : E m → ℝ) (c : E m)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (T : ℝ) :
    (fun x => c + r • x) '' {x | ‖x‖ < 1 ∧ rescaledFunction u c r k x < T} =
      {x | dist x c < r ∧ u x < T * k} := by
  have hdist (y : E m) : dist (c + r • y) c = r * ‖y‖ := by
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hinv (x : E m) : c + r • (r⁻¹ • (x - c)) = x := by
    rw [smul_inv_smul₀ hr.ne']
    abel
  ext x
  constructor
  · rintro ⟨y, ⟨hy, huv⟩, rfl⟩
    refine ⟨by rw [hdist]; nlinarith, ?_⟩
    have hv : u (c + r • y) / k < T := by
      simpa only [rescaledFunction, div_eq_mul_inv, mul_comm] using huv
    exact (div_lt_iff₀ hk).mp hv
  · rintro ⟨hx, hux⟩
    refine ⟨r⁻¹ • (x - c), ⟨?_, ?_⟩, hinv x⟩
    · have hh := hdist (r⁻¹ • (x - c))
      rw [hinv] at hh
      nlinarith
    · change k⁻¹ * u (c + r • (r⁻¹ • (x - c))) < T
      rw [hinv]
      simpa only [div_eq_mul_inv, mul_comm] using (div_lt_iff₀ hk).mpr hux

/-- The localized sublevel estimate in any ball of radius at most one,
with arbitrary center and level at least one. The constants depend only on
dimension, ellipticity, and the drift bound. -/
theorem exists_scaled_sublevel_constants {m : ℕ} (hm : 1 ≤ m) {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ T η : ℝ, 1 < T ∧ 0 < η ∧
      ∀ (u : E m → ℝ) (L : NNReal) (A : E m → E m →L[ℝ] E m) (b : E m → E m)
        (c : E m) (r k : ℝ), 0 < r → r ≤ 1 → 1 ≤ k →
        ContDiff ℝ 1 u → LipschitzWith L (gradient u) →
        (∀ z, dist z c ≤ 4 * r → 0 ≤ u z) →
        (∀ᵐ z ∂volume, dist z c ≤ 4 * r → ‖b z‖ ≤ M ∧
          (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
            δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
          linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) →
        (∀ᵐ z ∂volume, dist z c ≤ 4 * r →
          linearizedTrace (A z) (fderiv ℝ (gradient u) z) -
            inner ℝ (b z) (gradient u z) ≤ 1) →
        ∀ x, dist x c ≤ 3 * r → u x ≤ k →
          ENNReal.ofReal (η * r ^ m) ≤ volume {z | dist z c < r ∧ u z < T * k} := by
  obtain ⟨T, C, hT, hC, hbase⟩ := exists_localized_sublevel_constants hm hδ hΛ hM
  let v0 : ℝ≥0∞ := volume (Metric.ball (0 : E m) (1 / 8))
  have hv0 : 0 < v0 := Metric.measure_ball_pos volume _ (by norm_num)
  have hvfin : v0 ≠ ⊤ := measure_ball_lt_top.ne
  let η : ℝ := v0.toReal / C
  have hη : 0 < η := div_pos (ENNReal.toReal_pos hv0.ne' hvfin) hC
  have hηeq : ENNReal.ofReal η = v0 / ENNReal.ofReal C := by
    change ENNReal.ofReal (v0.toReal / C) = _
    rw [ENNReal.ofReal_div_of_pos hC, ENNReal.ofReal_toReal hvfin]
  refine ⟨T, η, hT, hη, ?_⟩
  intro u L A b c r k hr hr1 hk hu hLip hu0 hcoeff hineq x hx hux
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  let v := rescaledFunction u c r k
  have hv : ContDiff ℝ 1 v := rescaledFunction_contDiff hu c r k
  obtain ⟨Lv, hLv⟩ := rescaledFunction_gradient_lipschitz hu.differentiable_one hLip c r k
  have hdist (y : E m) : dist (c + r • y) c = r * ‖y‖ := by
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hball (y : E m) (hy : ‖y‖ ≤ 4) : dist (c + r • y) c ≤ 4 * r := by
    rw [hdist]
    nlinarith
  have hv0' : ∀ y, ‖y‖ ≤ 4 → 0 ≤ v y := by
    intro y hy
    exact mul_nonneg (inv_nonneg.mpr hk0.le) (hu0 _ (hball y hy))
  have hcoeff' : ∀ᵐ y ∂volume, ‖y‖ ≤ 4 → ‖r • b (c + r • y)‖ ≤ M ∧
      (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (A (c + r • y)) B) ∧
      linearizedTrace (A (c + r • y)) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ := by
    filter_upwards [ae_affine_dilation hcoeff c hr.ne'] with y hc
    intro hy
    have hh := hc (hball y hy)
    refine ⟨?_, hh.2⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hh.1 hr.le).trans (by nlinarith)
  have hineq' : ∀ᵐ y ∂volume, ‖y‖ ≤ 4 →
      linearizedTrace (A (c + r • y)) (fderiv ℝ (gradient v) y) -
        inner ℝ (r • b (c + r • y)) (gradient v y) ≤ 1 := by
    filter_upwards [ae_affine_dilation hineq c hr.ne',
      ae_affine_dilation (hLip.ae_differentiableAt (μ := volume)) c hr.ne'] with y hi hd
    intro hy
    rw [rescaledFunction_operator hu.differentiable_one c r k y hd]
    have hscale : r ^ 2 / k ≤ 1 := (div_le_one hk0).mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_left (hi (hball y hy)) (by positivity)).trans
      (by simpa only [mul_one] using hscale)
  let y : E m := r⁻¹ • (x - c)
  have hyx : c + r • y = x := by dsimp [y]; rw [smul_inv_smul₀ hr.ne']; abel
  have hy : ‖y‖ ≤ 3 := by
    have hh := hdist y
    rw [hyx] at hh
    nlinarith
  have hvy : v y ≤ 1 := by
    change k⁻¹ * u (c + r • y) ≤ 1
    rw [hyx]
    simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hk0).mpr hux
  have hmeasure := hbase v Lv (fun y => A (c + r • y)) (fun y => r • b (c + r • y))
    hv hLv hv0' hcoeff' hineq' y hy hvy
  have hηmeasure : ENNReal.ofReal η ≤ volume {z | ‖z‖ < 1 ∧ v z < T} := by
    rw [hηeq]
    exact (ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mpr hmeasure
  calc
    ENNReal.ofReal (η * r ^ m) = ENNReal.ofReal (r ^ m) * ENNReal.ofReal η := by
      rw [ENNReal.ofReal_mul hη.le, mul_comm]
    _ ≤ ENNReal.ofReal (r ^ m) * volume {z | ‖z‖ < 1 ∧ v z < T} := by gcongr
    _ = volume ((fun z => c + r • z) '' {z | ‖z‖ < 1 ∧ v z < T}) :=
      (volume_affine_dilation_image c hr.le _).symm
    _ = _ := congrArg volume (affine_dilation_image_sublevel u c hr hk0 T)

end Submission.Obl.Entropy__smooth_gaussian_transport
