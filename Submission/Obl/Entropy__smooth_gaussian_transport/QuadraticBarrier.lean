import Submission.Obl.Entropy__smooth_gaussian_transport.MaximumPrinciple

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def quadraticBarrier {m : ℕ} (a c : ℝ) (x : E m) : ℝ := a / 2 * ‖x‖ ^ 2 + c

theorem quadraticBarrier_contDiff {m : ℕ} (a c : ℝ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (quadraticBarrier (m := m) a c) := by
  exact (contDiff_const.mul (contDiff_id.norm_sq ℝ)).add contDiff_const

theorem quadraticBarrier_convex {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    ConvexOn ℝ univ (quadraticBarrier (m := m) a c) := by
  exact (((convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).smul
    (div_nonneg ha (by norm_num))).add (convexOn_const c convex_univ))

theorem quadraticBarrier_support {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (x : E m) :
    IsSubgradient (quadraticBarrier a c) x (a • x) := by
  intro z
  simp only [quadraticBarrier, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  have he := norm_sub_sq_real z x
  rw [real_inner_comm x z] at he
  nlinarith [mul_nonneg ha (sq_nonneg ‖z - x‖)]

theorem quadraticBarrier_gradient {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (x : E m) :
    gradient (quadraticBarrier a c) x = a • x := by
  apply Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support
    ((quadraticBarrier_contDiff a c).differentiable (by simp) x)
  exact quadraticBarrier_support ha c x

theorem quadraticBarrier_subgradient_iff {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : ℝ)
    (x y : E m) : IsSubgradient (quadraticBarrier a c) x y ↔ y = a • x := by
  constructor
  · intro h
    have he := Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support
      ((quadraticBarrier_contDiff a c).differentiable (by simp) x) h
    rw [quadraticBarrier_gradient ha c] at he
    exact he.symm
  · rintro rfl
    exact quadraticBarrier_support ha c x

theorem quadraticBarrier_conjugateDomain {m : ℕ} {a : ℝ} (ha : 0 < a) (c : ℝ) :
    conjugateDomain (quadraticBarrier (m := m) a c) = univ := by
  apply eq_univ_of_forall
  intro y
  refine ⟨‖y‖ ^ 2 / (2 * a) - c, ?_⟩
  rintro r ⟨x, rfl⟩
  change inner ℝ y x - (a / 2 * ‖x‖ ^ 2 + c) ≤ ‖y‖ ^ 2 / (2 * a) - c
  have h := real_inner_le_norm y x
  have hq : 0 ≤ (a * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have hd : (‖y‖ ^ 2 / (2 * a)) * (2 * a) = ‖y‖ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h ha.le]

theorem quadraticBarrier_subgradientImage {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : ℝ)
    (s : Set (E m)) : subgradientImage (quadraticBarrier a c) s = a • s := by
  ext y
  simp only [subgradientImage, mem_ofPred_eq, quadraticBarrier_subgradient_iff ha c,
    mem_smul_set]
  exact exists_congr fun x => and_congr_right fun _ => eq_comm

theorem quadraticBarrier_alexandrov {m : ℕ} {a : ℝ} (ha : 0 < a) (c : ℝ)
    {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (quadraticBarrier a c) s = ENNReal.ofReal (a ^ m) * volume s := by
  rw [alexandrovMeasure_apply (quadraticBarrier_contDiff a c).continuous
    (quadraticBarrier_conjugateDomain ha c) hs,
    quadraticBarrier_subgradientImage ha.le c, Measure.addHaar_smul_of_nonneg volume ha.le]
  simp only [E, finrank_euclideanSpace_fin]

/-- An upper Alexandrov density bound controls the depth below zero boundary data
by a quadratic barrier. -/
theorem quadratic_lower_barrier {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {R : ℝ} (hR : 0 < R) (hboundary : ∀ z ∈ Metric.sphere (0 : E m) R, 0 ≤ u z)
    {L a : ℝ} (ha : 0 < a) (hLa : L < a ^ m)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ Metric.closedBall (0 : E m) R →
      alexandrovMeasure u s ≤ ENNReal.ofReal L * volume s) :
    ∀ x ∈ Metric.closedBall (0 : E m) R, a / 2 * (‖x‖ ^ 2 - R ^ 2) ≤ u x := by
  have hcomp := comparison_of_strict_mass hu (quadraticBarrier_convex ha.le (-a / 2 * R ^ 2))
    hdom (quadraticBarrier_conjugateDomain ha _) (isCompact_closedBall (0 : E m) R)
  have hbd : ∀ x ∈ frontier (Metric.closedBall (0 : E m) R),
      quadraticBarrier a (-a / 2 * R ^ 2) x ≤ u x := by
    intro x hx
    rw [frontier_closedBall _ hR.ne'] at hx
    have hn : ‖x‖ = R := by simpa using hx
    simpa only [quadraticBarrier, hn, neg_div, neg_mul, add_neg_cancel] using hboundary x hx
  have hstrict (s : Set (E m)) (hs : MeasurableSet s)
      (hsK : s ⊆ Metric.closedBall (0 : E m) R) (hpos : 0 < volume s) :
      alexandrovMeasure u s < alexandrovMeasure (quadraticBarrier a (-a / 2 * R ^ 2)) s := by
    rw [quadraticBarrier_alexandrov ha _ hs]
    apply (hmass s hs hsK).trans_lt
    apply (ENNReal.mul_lt_mul_iff_left hpos.ne'
      ((measure_mono hsK).trans_lt (isCompact_closedBall (0 : E m) R).measure_lt_top).ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos ha _)).mpr hLa
  intro x hx
  have h := hcomp hbd hstrict x hx
  convert! h using 1
  simp only [quadraticBarrier]
  ring

/-- The complementary comparison with a quadratic function uses a lower density bound. -/
theorem quadratic_upper_barrier {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {R : ℝ} (hR : 0 < R) (hboundary : ∀ z ∈ Metric.sphere (0 : E m) R, u z ≤ 0)
    {l a : ℝ} (ha : 0 < a) (hal : a ^ m < l)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ Metric.closedBall (0 : E m) R →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s) :
    ∀ x ∈ Metric.closedBall (0 : E m) R, u x ≤ a / 2 * (‖x‖ ^ 2 - R ^ 2) := by
  have hcomp := comparison_of_strict_mass (quadraticBarrier_convex ha.le (-a / 2 * R ^ 2)) hu
    (quadraticBarrier_conjugateDomain ha _) hdom (isCompact_closedBall (0 : E m) R)
  have hbd : ∀ x ∈ frontier (Metric.closedBall (0 : E m) R),
      u x ≤ quadraticBarrier a (-a / 2 * R ^ 2) x := by
    intro x hx
    rw [frontier_closedBall _ hR.ne'] at hx
    have hn : ‖x‖ = R := by simpa using hx
    simpa only [quadraticBarrier, hn, neg_div, neg_mul, add_neg_cancel] using hboundary x hx
  have hstrict (s : Set (E m)) (hs : MeasurableSet s)
      (hsK : s ⊆ Metric.closedBall (0 : E m) R) (hpos : 0 < volume s) :
      alexandrovMeasure (quadraticBarrier a (-a / 2 * R ^ 2)) s < alexandrovMeasure u s := by
    rw [quadraticBarrier_alexandrov ha _ hs]
    apply lt_of_lt_of_le _ (hmass s hs hsK)
    apply (ENNReal.mul_lt_mul_iff_left hpos.ne'
      ((measure_mono hsK).trans_lt (isCompact_closedBall (0 : E m) R).measure_lt_top).ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff ((pow_pos ha _).trans hal)).mpr hal
  intro x hx
  have h := hcomp hbd hstrict x hx
  convert! h using 1
  simp only [quadraticBarrier]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
