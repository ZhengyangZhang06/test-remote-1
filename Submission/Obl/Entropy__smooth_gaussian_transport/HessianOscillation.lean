import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOscillationDecay

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Essential oscillation of the full Hessian tends to zero geometrically
on shrinking balls. This estimate is uniform over interior centers. -/
theorem brenier_ae_hessian_geometric_oscillation {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ c : E m, Metric.closedBall c 1 ⊆ K → ∀ n : ℕ,
        ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
          x ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n) →
          y ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n) →
          ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤ C * β ^ n := by
  obtain ⟨F, _, _, β, M, A, hβ, hβ1, hM, hA, hcomp, hdecay⟩ :=
    brenier_hessian_oscillation_decay hm hV ha hH hφ hlaw hK
  let q : ℝ := ((m : ℝ) + 6)⁻¹
  have hden : 0 < (m : ℝ) + 6 := by positivity
  have hden1 : 1 < (m : ℝ) + 6 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hq : 0 < q := inv_pos.mpr hden
  have hq1 : q < 1 := (inv_lt_one₀ hden).mpr hden1
  let b : ℝ := max β q
  have hb : 0 < b := hβ.trans_le (le_max_left _ _)
  have hb1 : b < 1 := max_lt hβ1 hq1
  refine ⟨b, A * (M + 2), hb, hb1, mul_pos hA (by linarith), ?_⟩
  intro c hc n
  obtain ⟨l, U, hlu, hbounds, hwidth⟩ := hdecay c hc
  have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1.le
  have hinK {x : E m} (hx : x ∈ Metric.ball c (q ^ n)) : x ∈ K :=
    hc ((Metric.ball_subset_closedBall hx).trans hpow)
  filter_upwards [hcomp, hbounds n] with x hx hxb
  filter_upwards [hx, hbounds n] with y hy hyb
  intro hxball hyball
  have hxy := hy (hinK hxball) (hinK hyball)
  have hxB := hxb hxball
  have hyB := hyb hyball
  have hsum : (∑ v ∈ F, max 0
      (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
        inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) ≤ M * β ^ n := by
    apply le_trans _ (hwidth n)
    apply Finset.sum_le_sum
    intro v hv
    apply max_le (sub_nonneg.mpr (hlu n v hv))
    exact sub_le_sub (hyB v hv).2 (hxB v hv).1
  have hd : ‖y - x‖ ≤ 2 * q ^ n := by
    calc
      ‖y - x‖ = dist y x := (dist_eq_norm _ _).symm
      _ ≤ dist y c + dist c x := dist_triangle y c x
      _ ≤ q ^ n + q ^ n := add_le_add (Metric.mem_ball.mp hyball).le
        (by simpa only [dist_comm] using (Metric.mem_ball.mp hxball).le)
      _ = _ := by ring
  have hβpow : β ^ n ≤ b ^ n := pow_le_pow_left₀ hβ.le (le_max_left _ _) n
  have hqpow : q ^ n ≤ b ^ n := pow_le_pow_left₀ hq.le (le_max_right _ _) n
  calc
    _ ≤ A * ((∑ v ∈ F, max 0
        (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
          inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) + ‖y - x‖) := hxy
    _ ≤ A * (M * β ^ n + 2 * q ^ n) := by gcongr
    _ ≤ A * (M * b ^ n + 2 * b ^ n) := by gcongr
    _ = _ := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
