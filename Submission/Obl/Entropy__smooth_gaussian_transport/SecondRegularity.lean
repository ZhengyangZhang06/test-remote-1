import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOscillation
import Submission.Obl.Entropy__smooth_gaussian_transport.EssentialLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Once differentiability is known everywhere, an essential derivative
bound on an open convex set holds at every point of that set. -/
theorem fderiv_bound_of_ae_bound {m : ℕ} {f : E m → E m} {L : NNReal}
    (hf : LipschitzWith L f) (hd : Differentiable ℝ f)
    {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (A : E m →L[ℝ] E m) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ f z - A‖ ≤ ε)
    {x : E m} (hx : x ∈ Ω) : ‖fderiv ℝ f x - A‖ ≤ ε := by
  have hder : HasFDerivAt (fun z => f z - A z) (fderiv ℝ f x - A) x :=
    (hd x).hasFDerivAt.sub A.hasFDerivAt
  apply hder.le_of_lip' hε
  filter_upwards [hΩ.mem_nhds hx] with y hy
  have hh := linear_remainder_of_ae_fderiv_bound hf hΩ hc A hε hbound hx hy
  have he : (f y - A y) - (f x - A x) = f y - f x - A (y - x) := by rw [map_sub]; abel
  rwa [he]

theorem brenier_gradient_differentiable {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    Differentiable ℝ (gradient φ) := by
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  intro c
  obtain ⟨β, C, hβ, hβ1, hC, hosc⟩ := brenier_ae_hessian_geometric_oscillation hm hV ha hH hφ hlaw
    (isCompact_closedBall c 1)
  let q : ℝ := ((m : ℝ) + 6)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun n : ℕ => C * β ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1)
  obtain ⟨A, hA⟩ := exists_essential_limit_of_oscillation
    (fun z => fderiv ℝ (gradient φ) z) c (fun n => q ^ n) (fun n => C * β ^ n)
    (fun n => pow_pos hq n) (fun n => mul_nonneg hC.le (pow_nonneg hβ.le n)) hpow
    (hosc c le_rfl)
  apply (hasFDerivAt_of_essential_derivative_limit hLip (A := A) ?_).differentiableAt
  intro ε hε
  have ht : Tendsto (fun n : ℕ => 2 * (C * β ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hpow
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨q ^ n, pow_pos hq n, ?_⟩
  filter_upwards [hA n] with z hz
  intro hzb
  exact (hz hzb).trans hn.le

/-- Vanishing essential oscillation, together with the mean value inequality,
upgrades the transport Hessian to a continuous everywhere derivative. -/
theorem brenier_hessian_continuous {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    Continuous (fderiv ℝ (gradient φ)) := by
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hd := brenier_gradient_differentiable hm hV ha hH hφ hlaw
  apply continuous_iff_continuousAt.mpr
  intro c
  obtain ⟨β, C, hβ, hβ1, hC, hosc⟩ := brenier_ae_hessian_geometric_oscillation hm hV ha hH hφ hlaw
    (isCompact_closedBall c 1)
  let q : ℝ := ((m : ℝ) + 6)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun n : ℕ => 2 * C * β ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := 2 * C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
  obtain ⟨z, hz, hzae⟩ := exists_mem_ball_of_ae (hosc c le_rfl n) c (pow_pos hq n)
  have hb : ∀ᵐ y ∂volume, y ∈ Metric.ball c (q ^ n) →
      ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) z‖ ≤ C * β ^ n :=
    hzae.mono (fun y hy => hy hz)
  have hp {y : E m} (hy : y ∈ Metric.ball c (q ^ n)) :
      ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) z‖ ≤ C * β ^ n :=
    fderiv_bound_of_ae_bound hLip hd Metric.isOpen_ball (convex_ball _ _) _
      (mul_nonneg hC.le (pow_nonneg hβ.le n)) hb hy
  have hc := hp (Metric.mem_ball_self (pow_pos hq n))
  filter_upwards [Metric.ball_mem_nhds c (pow_pos hq n)] with y hy
  rw [dist_eq_norm]
  calc
    ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) c‖ ≤
        ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) z‖ +
          ‖fderiv ℝ (gradient φ) z - fderiv ℝ (gradient φ) c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * β ^ n + C * β ^ n := add_le_add (hp hy) (by rwa [norm_sub_rev])
    _ < ε := by linarith

theorem brenier_contDiff_two {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ContDiff ℝ 2 φ := by
  have hd := brenier_gradient_differentiable hm hV ha hH hφ hlaw
  have hcont := brenier_hessian_continuous hm hV ha hH hφ hlaw
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_one_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (gradient φ), hcont, fun x => (hd x).hasFDerivAt⟩
  have hφd := (brenier_contDiff_one hm hV.continuous hφ hlaw).1.differentiable_one
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun x => innerSL ℝ (gradient φ x), (innerSL ℝ).contDiff.comp hg, ?_⟩
  intro x
  convert! (hφd x).hasFDerivAt using 1
  exact toDual_gradient

end Submission.Obl.Entropy__smooth_gaussian_transport
