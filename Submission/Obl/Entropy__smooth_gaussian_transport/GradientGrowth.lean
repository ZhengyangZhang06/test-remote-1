import Submission.Obl.Entropy__smooth_gaussian_transport.ForwardBall
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gaussian_exp_moment_lower_bound {m : ℕ} {T : E m → E m} {k : ℝ}
    (hk : 0 < k) (hT : ∀ x y, 0 ≤ inner ℝ (T x - T y) (x - y))
    (hi : Integrable (fun z => Submission.Lib.EntropyRemainder.gaussianDensity z *
      Real.exp (k * ‖T z‖ ^ 2)) volume) {x : E m} (hx : T x ≠ 0) :
    volume.real (Metric.ball (0 : E m) (1 / 2 : ℝ)) * ((Real.sqrt (2 * Real.pi))⁻¹ ^ m) *
      Real.exp (k * ‖T x‖ ^ 2 / 9 - (‖x‖ + 2) ^ 2 / 2) ≤
      ∫ z, Submission.Lib.EntropyRemainder.gaussianDensity z * Real.exp (k * ‖T z‖ ^ 2) := by
  let c := ((Real.sqrt (2 * Real.pi))⁻¹ ^ m : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let B := Metric.ball (x + ‖T x‖⁻¹ • T x) (1 / 2 : ℝ)
  let L := c * Real.exp (k * ‖T x‖ ^ 2 / 9 - (‖x‖ + 2) ^ 2 / 2)
  have hbound (z : E m) (hz : z ∈ B) :
      L ≤ Submission.Lib.EntropyRemainder.gaussianDensity z * Real.exp (k * ‖T z‖ ^ 2) := by
    have hn := norm_le_three_mul_norm_on_forward_ball hT hx hz
    have hz' := norm_lt_norm_add_two_on_forward_ball hx hz
    have hs : ‖T x‖ ^ 2 ≤ 9 * ‖T z‖ ^ 2 := by
      nlinarith [sq_nonneg (3 * ‖T z‖ - ‖T x‖), norm_nonneg (T x), norm_nonneg (T z)]
    have hks := mul_le_mul_of_nonneg_left hs hk.le
    have hsz : ‖z‖ ^ 2 ≤ (‖x‖ + 2) ^ 2 := by
      nlinarith [norm_nonneg z, norm_nonneg x]
    change c * Real.exp _ ≤ c * Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (k * ‖T z‖ ^ 2)
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc.le
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hmono := setIntegral_mono_on (integrableOn_const hBfin) hi.integrableOn
    measurableSet_ball hbound
  have hnonneg : 0 ≤ᵐ[volume] (fun z => Submission.Lib.EntropyRemainder.gaussianDensity z *
      Real.exp (k * ‖T z‖ ^ 2)) := Eventually.of_forall (fun z =>
    (mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos z) (Real.exp_pos _)).le)
  have hh := hmono.trans (setIntegral_le_integral hi hnonneg)
  rw [setIntegral_const, smul_eq_mul] at hh
  dsimp only [B, L] at hh
  rw [Measure.addHaar_real_ball_center] at hh
  simpa only [c, mul_assoc] using hh

/-- A monotone map with a Gaussian exponential square moment has at most
linear pointwise growth. -/
theorem linear_growth_of_gaussian_exp_moment {m : ℕ} {T : E m → E m} {k : ℝ}
    (hk : 0 < k) (hT : ∀ x y, 0 ≤ inner ℝ (T x - T y) (x - y))
    (hi : Integrable (fun z => Submission.Lib.EntropyRemainder.gaussianDensity z *
      Real.exp (k * ‖T z‖ ^ 2)) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖T x‖ ≤ C * (1 + ‖x‖) := by
  let K := volume.real (Metric.ball (0 : E m) (1 / 2 : ℝ)) *
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ m)
  have hvol : 0 < volume.real (Metric.ball (0 : E m) (1 / 2 : ℝ)) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ (by norm_num)).ne' measure_ball_lt_top.ne
  have hK : 0 < K := by dsimp [K]; positivity
  let I := ∫ z, Submission.Lib.EntropyRemainder.gaussianDensity z * Real.exp (k * ‖T z‖ ^ 2)
  let P := max 1 (I / K)
  have hP : 0 < P := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let D := 9 * (|Real.log P| + 2) / k
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Real.sqrt D, Real.sqrt_pos.mpr hD, fun x => ?_⟩
  by_cases hx : T x = 0
  · rw [hx, norm_zero]
    positivity
  have hlow : K * Real.exp (k * ‖T x‖ ^ 2 / 9 - (‖x‖ + 2) ^ 2 / 2) ≤ I :=
    gaussian_exp_moment_lower_bound hk hT hi hx
  have hexp : Real.exp (k * ‖T x‖ ^ 2 / 9 - (‖x‖ + 2) ^ 2 / 2) ≤ P := by
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hK).mpr
    simpa only [mul_comm] using hlow
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hsq : (1 : ℝ) ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have habs : Real.log P ≤ |Real.log P| * (1 + ‖x‖) ^ 2 :=
    (le_abs_self _).trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsq (abs_nonneg (Real.log P)))
  have hnorm : (‖x‖ + 2) ^ 2 / 2 ≤ 2 * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hbound : k * ‖T x‖ ^ 2 ≤ 9 * (|Real.log P| + 2) * (1 + ‖x‖) ^ 2 := by
    nlinarith only [hlog, habs, hnorm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hD.le]
  apply (mul_le_mul_iff_right₀ hk).mp
  have he : k * (D * (1 + ‖x‖) ^ 2) =
      9 * (|Real.log P| + 2) * (1 + ‖x‖) ^ 2 := by
    dsimp [D]
    field_simp
  rwa [he]

theorem brenier_gradient_linear_growth {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖gradient φ x‖ ≤ C * (1 + ‖x‖) := by
  exact linear_growth_of_gaussian_exp_moment (by positivity : 0 < a / 8)
    (convex_gradient_monotone hφ (brenier_contDiff_one hm hV.continuous hφ hlaw).1.differentiable_one)
    (brenier_integrable_exp_gradient_sq hm hV ha hH hφ hlaw)

end Submission.Obl.Entropy__smooth_gaussian_transport
