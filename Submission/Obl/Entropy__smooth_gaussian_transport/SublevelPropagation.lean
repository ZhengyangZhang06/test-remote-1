import Submission.Obl.Entropy__smooth_gaussian_transport.ScaledSublevel

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

def HasSublevelMeasure {m : ℕ} (u : E m → ℝ) (Ω : Set (E m)) (T η : ℝ) : Prop :=
  ∀ (c : E m) (r k : ℝ), 0 < r → r ≤ 1 → 1 ≤ k →
    Metric.closedBall c (4 * r) ⊆ Ω →
    ∀ x, dist x c ≤ 3 * r → u x ≤ k →
      ENNReal.ofReal (η * r ^ m) ≤ volume {z | dist z c < r ∧ u z < T * k}

theorem exists_sublevel_measure {m : ℕ} (hm : 1 ≤ m) {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ T η : ℝ, 1 < T ∧ 0 < η ∧
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
        HasSublevelMeasure u Ω T η := by
  obtain ⟨T, η, hT, hη, h⟩ := exists_scaled_sublevel_constants hm hδ hΛ hM
  refine ⟨T, η, hT, hη, ?_⟩
  intro u L A b Ω hu hLip hu0 hcoeff hineq c r k hr hr1 hk hball
  apply h u L A b c r k hr hr1 hk hu hLip
  · exact fun z hz => hu0 z (hball hz)
  · exact hcoeff.mono (fun z hz hzr => hz (hball hzr))
  · exact hineq.mono (fun z hz hzr => hz (hball hzr))

theorem HasSublevelMeasure.exists_low_point {m : ℕ} {u : E m → ℝ} {Ω : Set (E m)}
    {T η : ℝ} (h : HasSublevelMeasure u Ω T η) (hη : 0 < η)
    (c : E m) {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : 1 ≤ k)
    (hball : Metric.closedBall c (4 * r) ⊆ Ω)
    {x : E m} (hx : dist x c ≤ 3 * r) (hux : u x ≤ k) :
    ∃ y, dist y c < r ∧ u y < T * k := by
  have hh := h c r k hr hr1 hk hball x hx hux
  have hp : 0 < volume {z | dist z c < r ∧ u z < T * k} :=
    (ENNReal.ofReal_pos.mpr (mul_pos hη (pow_pos hr _))).trans_le hh
  exact nonempty_of_measure_ne_zero hp.ne'

theorem HasSublevelMeasure.propagate_chain {m : ℕ} {u : E m → ℝ} {Ω : Set (E m)}
    {T η : ℝ} (h : HasSublevelMeasure u Ω T η) (hT : 1 ≤ T) (hη : 0 < η)
    (c : ℕ → E m) {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : 1 ≤ k)
    {x : E m} (hx : dist x (c 0) ≤ r) (hux : u x ≤ k)
    (n : ℕ)
    (hstep : ∀ i < n, dist (c i) (c (i + 1)) ≤ 2 * r)
    (hball : ∀ i ≤ n, Metric.closedBall (c i) (4 * r) ⊆ Ω) :
    ∃ y, dist y (c n) ≤ r ∧ u y ≤ T ^ n * k := by
  induction n with
  | zero => exact ⟨x, hx, by simpa using hux⟩
  | succ n ih =>
    obtain ⟨y, hy, huy⟩ := ih (fun i hi => hstep i (by omega)) (fun i hi => hball i (by omega))
    have hdist : dist y (c (n + 1)) ≤ 3 * r :=
      (dist_triangle y (c n) (c (n + 1))).trans (by linarith [hstep n (by omega)])
    have hlevel : 1 ≤ T ^ n * k := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) hk
    obtain ⟨z, hz, huz⟩ := h.exists_low_point hη (c (n + 1)) hr hr1 hlevel
      (hball _ le_rfl) hdist huy
    refine ⟨z, hz.le, ?_⟩
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using huz.le

/-- Chaining the local estimate extends its point range to any fixed multiple
of the radius. The sublevel constant grows by a fixed power. -/
theorem HasSublevelMeasure.measure_of_segment {m : ℕ} {u : E m → ℝ} {Ω : Set (E m)}
    {T η : ℝ} (h : HasSublevelMeasure u Ω T η) (hT : 1 ≤ T) (hη : 0 < η)
    {x c : E m} {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : 1 ≤ k)
    {N : ℕ} (hN : 0 < N) (hxc : dist x c ≤ 2 * N * r) (hux : u x ≤ k)
    (hregion : ∀ z ∈ segment ℝ x c, Metric.closedBall z (4 * r) ⊆ Ω) :
    ENNReal.ofReal (η * r ^ m) ≤
      volume {z | dist z c < r ∧ u z < T ^ (N + 1) * k} := by
  let path : ℕ → E m := fun i => AffineMap.lineMap x c ((i : ℝ) / N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : path 0 = x := by simp only [path, Nat.cast_zero, zero_div, AffineMap.lineMap_apply_zero]
  have hpN : path N = c := by simp only [path, div_self hN0.ne', AffineMap.lineMap_apply_one]
  have hpseg (i : ℕ) (hi : i ≤ N) : path i ∈ segment ℝ x c := by
    apply lineMap_mem_segment
    exact ⟨by positivity, (div_le_one hN0).mpr (by exact_mod_cast hi)⟩
  have hpstep (i : ℕ) : dist (path i) (path (i + 1)) ≤ 2 * r := by
    rw [dist_comm]
    change dist (AffineMap.lineMap x c (((i + 1 : ℕ) : ℝ) / N))
      (AffineMap.lineMap x c ((i : ℝ) / N)) ≤ _
    rw [dist_lineMap_lineMap, Real.dist_eq]
    have he : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / (N : ℝ) := by push_cast; ring
    rw [he, abs_of_pos (one_div_pos.mpr hN0)]
    have hh : dist x c / N ≤ 2 * r := (div_le_iff₀ hN0).mpr (by nlinarith)
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hh
  obtain ⟨y, hy, huy⟩ := h.propagate_chain hT hη path hr hr1 hk
    (x := x) (by rw [hp0, dist_self]; exact hr.le) hux N (fun i _ => hpstep i)
      (fun i hi => hregion _ (hpseg i hi))
  rw [hpN] at hy
  have hh := h c r (T ^ N * k) hr hr1 (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) hk)
    (hregion c (right_mem_segment ℝ x c)) y (hy.trans (by linarith)) huy
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

end Submission.Obl.Entropy__smooth_gaussian_transport
