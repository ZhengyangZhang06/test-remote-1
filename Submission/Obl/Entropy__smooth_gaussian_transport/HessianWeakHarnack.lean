import Submission.Obl.Entropy__smooth_gaussian_transport.ScaledWeakHarnack
import Submission.Obl.Entropy__smooth_gaussian_transport.WeakHarnackLimit
import Submission.Obl.Entropy__smooth_gaussian_transport.DirectionalLimits

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Weak Harnack for the deficit of an almost-everywhere directional Hessian
from any local essential upper bound. The constants are uniform over centers,
scales, unit directions, and upper bounds within a fixed compact set. -/
theorem brenier_hessian_weakHarnack {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (c : E m) (r : ℝ) (v : E m) (U : ℝ), 0 < r → r ≤ 1 → ‖v‖ = 1 →
        Metric.closedBall c (r * (m + 6)) ⊆ K →
        (∀ᵐ y ∂volume, y ∈ Metric.ball c (r * (m + 6)) →
          inner ℝ ((fderiv ℝ (gradient φ) y) v) v ≤ U) →
        HasAeWeakHarnackTail
          (fun x => (r ^ 2)⁻¹ * (U - inner ℝ ((fderiv ℝ (gradient φ) (c + r • x)) v) v)) Q θ := by
  obtain ⟨δ, Λ, M, hδ, hΛ, hM, hcoeff⟩ :=
    brenier_ae_linearized_bounds hm hV ha hH hφ hlaw hK
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := exists_scaled_weakHarnack hm hδ hΛ.le hM.le
  have hQ' : 1 < 2 * Q := by linarith
  refine ⟨2 * Q, θ, hQ', hθ, hθ1, ?_⟩
  intro c r v U hr hr1 hv hinside hupper
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  let Ω : Set (E m) := Metric.closedBall c (r * (m + 4))
  have hΩK : Ω ⊆ K := by
    intro z hz
    apply hinside
    apply (Metric.mem_closedBall.mp hz).trans
    nlinarith
  have hscaled (z : E m) (hz : z ∈ Metric.closedBall (0 : E m) (m + 4)) : c + r • z ∈ Ω := by
    change dist (c + r • z) c ≤ r * (m + 4)
    rw [dist_eq_norm]
    have he : c + r • z - c = r • z := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  let t : ℕ → ℝ := fun n => r / ((n : ℝ) + 1)
  have htpos (n : ℕ) : 0 < t n := div_pos hr (by positivity)
  have htbound (n : ℕ) : t n ≤ r := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htend : Tendsto t atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := r)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    simpa only [mul_zero, mul_one_div, t] using hh
  have hstep0 (n : ℕ) : t n • v ≠ 0 := by
    intro he
    have hh := congrArg norm he
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos n), hv, mul_one, norm_zero] at hh
    exact (htpos n).ne' hh
  let u : ℕ → E m → ℝ := fun n z => U - normalizedSecondDifference φ (t n • v) z
  have htail (n : ℕ) : HasWeakHarnackTail (rescaledFunction (u n) c r (r ^ 2)) Q θ := by
    obtain ⟨hq, _, ⟨L, hL⟩, hqeq⟩ :=
      brenier_normalized_secondDifference_subsolution hm hV ha hH hφ hlaw (hstep0 n)
    have hu : ContDiff ℝ 1 (u n) := contDiff_const.sub hq
    have hulip : LipschitzWith L (gradient (u n)) := by
      rw [show gradient (u n) = fun z => -gradient (normalizedSecondDifference φ (t n • v)) z from
        funext (gradient_const_sub_of_differentiable hq.differentiable_one U)]
      exact hL.neg
    apply hweak (u n) L (fun z => fderiv ℝ (gradient φ) z)
      (fun z => gradient V (gradient φ z)) Ω hu hulip ?_ ?_ ?_ c r (r ^ 2) hr hr1 le_rfl hscaled
    · intro z hz
      apply sub_nonneg.mpr
      apply normalizedSecondDifference_smul_le_of_ae_bound hC1 hLip Metric.isOpen_ball (convex_ball _ _)
        hv hupper (htpos n).ne'
      · change ‖z - t n • v - c‖ < r * (m + 6)
        have he : z - t n • v - c = (z - c) - t n • v := by abel
        rw [he]
        have hn := norm_sub_le (z - c) (t n • v)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos n), hv, mul_one] at hn
        have hzc : ‖z - c‖ ≤ r * (m + 4) := Metric.mem_closedBall.mp hz
        nlinarith [htbound n]
      · change ‖z + t n • v - c‖ < r * (m + 6)
        have he : z + t n • v - c = (z - c) + t n • v := by abel
        rw [he]
        have hn := norm_add_le (z - c) (t n • v)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos n), hv, mul_one] at hn
        have hzc : ‖z - c‖ ≤ r * (m + 4) := Metric.mem_closedBall.mp hz
        nlinarith [htbound n]
    · filter_upwards [hcoeff] with z hz
      intro hzΩ
      obtain ⟨hb, hell⟩ := hz (hΩK hzΩ)
      refine ⟨hb, fun B hB => (hell B hB).1, ?_⟩
      exact (hell _ (operatorMatrix_id_posSemidef m)).2.trans
        ((mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hΛ.le).trans_eq (mul_one Λ))
    · filter_upwards [hqeq] with z hz
      intro _
      change linearizedTransport V φ (u n) z ≤ 1
      rw [linearizedTransport_const_sub V φ hq.differentiable_one hz.1]
      linarith [hz.2]
  apply ae_weakHarnack_of_ae_tendsto (zero_lt_one.trans hQ) htail
  have hlim := ae_tendsto_normalizedSecondDifference hC1 hLip hv htend
    (Filter.Eventually.of_forall (fun n => (htpos n).ne'))
  filter_upwards [ae_affine_dilation hlim c hr.ne'] with x hx
  have hh := (tendsto_const_nhds (x := (r ^ 2)⁻¹)).mul ((tendsto_const_nhds (x := U)).sub hx)
  exact hh


/-- A substantial set of directional Hessian deficits forces a deficit almost
at every point of the inner cube, up to the radius-squared forcing term. -/
theorem brenier_hessian_measure_to_point {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c : E m) (r : ℝ) (v : E m) (U t : ℝ), 0 < r → r ≤ 1 → ‖v‖ = 1 →
        Metric.closedBall c (r * (m + 6)) ⊆ K →
        (∀ᵐ y ∂volume, y ∈ Metric.ball c (r * (m + 6)) →
          inner ℝ ((fderiv ℝ (gradient φ) y) v) v ≤ U) →
        ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
          volume ({y : Fin m → ℝ | t ≤ U -
            inner ℝ ((fderiv ℝ (gradient φ) (c + r • WithLp.toLp 2 y)) v) v} ∩
              (unitCoordinateBox m : Set (Fin m → ℝ))) →
        ∀ᵐ x ∂volume, x ∈ closedBoxRegion (unitCoordinateBox m) →
          t ≤ C * max (r ^ 2) (U - inner ℝ ((fderiv ℝ (gradient φ) (c + r • x)) v) v) := by
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := brenier_hessian_weakHarnack hm hV ha hH hφ hlaw hK
  obtain ⟨C, hC, hpoint⟩ := ae_weakHarnack_measure_to_point hQ hθ hθ1 hσ
  refine ⟨C, hC, ?_⟩
  intro c r v U t hr hr1 hv hinside hupper hmass
  have hk : 0 < r ^ 2 := sq_pos_of_pos hr
  let w : E m → ℝ := fun x => (r ^ 2)⁻¹ *
    (U - inner ℝ ((fderiv ℝ (gradient φ) (c + r • x)) v) v)
  have htail : HasAeWeakHarnackTail w Q θ := hweak c r v U hr hr1 hv hinside hupper
  have hm' : ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
      volume ({y : Fin m → ℝ | t / r ^ 2 ≤ w (WithLp.toLp 2 y)} ∩
        (unitCoordinateBox m : Set (Fin m → ℝ))) := by
    convert! hmass using 2
    ext y
    simp only [w, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hk]
  filter_upwards [hpoint w htail (t / r ^ 2) hm'] with x hx hxi
  have hb := mul_le_mul_of_nonneg_left (hx hxi) hk.le
  have he : r ^ 2 * (C * max 1 (w x)) = C * max (r ^ 2)
      (U - inner ℝ ((fderiv ℝ (gradient φ) (c + r • x)) v) v) := by
    rw [mul_left_comm (r ^ 2) C, mul_max_of_nonneg _ _ hk.le, mul_one]
    congr 2
    dsimp only [w]
    rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
  rw [he] at hb
  simpa only [mul_div_cancel₀ t hk.ne'] using hb

end Submission.Obl.Entropy__smooth_gaussian_transport
