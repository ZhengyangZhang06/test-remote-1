import Submission.Obl.Entropy__smooth_gaussian_transport.MaximumPrinciple

open MeasureTheory Set Filter Function
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A ball of slopes can be moved toward a nearby supporting hyperplane while
remaining inside the polar set. -/
theorem translated_ball_subset_strictPolar {m : ℕ} {K : Set (E m)} {x e : E m}
    {D h d t : ℝ} (hD : 0 < D) (hh : 0 < h) (ht : 0 ≤ t)
    (hK : K ⊆ Metric.closedBall x D)
    (hsupport : ∀ z ∈ K, inner ℝ e (z - x) ≤ d) (htd : t * d ≤ h / 2) :
    Metric.ball (t • e) (h / (2 * D)) ⊆ strictPolar K x h := by
  intro p hp z hz
  have hp' : ‖p - t • e‖ < h / (2 * D) := hp
  have hz' : ‖z - x‖ ≤ D := hK hz
  have hfirst : inner ℝ (p - t • e) (z - x) < h / 2 := by
    apply lt_of_le_of_lt (real_inner_le_norm _ _) (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hz' (norm_nonneg _)) ?_)
    have he : h / (2 * D) * D = h / 2 := by field_simp
    rw [← he]
    exact mul_lt_mul_of_pos_right hp' hD
  have hsecond := mul_le_mul_of_nonneg_left (hsupport z hz) ht
  rw [inner_sub_left, real_inner_smul_left] at hfirst
  linarith

theorem separated_ball_family {m n : ℕ} {e : E m} (he : ‖e‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    Pairwise (Disjoint on (fun i : Fin n => Metric.ball ((2 * r * (i : ℕ)) • e) r)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one]
  have hn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hab : 1 ≤ |((i : ℕ) : ℝ) - (j : ℕ)| := by
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hle : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      nlinarith [neg_le_abs (((i : ℕ) : ℝ) - (j : ℕ))]
    · have hle : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      nlinarith [le_abs_self (((i : ℕ) : ℝ) - (j : ℕ))]
  rw [← mul_sub, abs_mul, abs_of_pos (mul_pos (by norm_num) hr)]
  nlinarith [mul_le_mul_of_nonneg_left hab hr.le]

/-- A finite packing estimate for the polar set. The number of balls grows as
the supporting hyperplane approaches the base point. -/
theorem polar_packing_bound {m : ℕ} {K : Set (E m)} {x e : E m}
    {D h d : ℝ} (hD : 0 < D) (hh : 0 < h) (hd : 0 ≤ d) (he : ‖e‖ = 1)
    (hK : K ⊆ Metric.closedBall x D)
    (hsupport : ∀ z ∈ K, inner ℝ e (z - x) ≤ d)
    (n : ℕ) (hn : 2 * (n : ℝ) * d ≤ D) :
    (n : ℝ≥0∞) * volume (Metric.ball (0 : E m) (h / (2 * D))) ≤
      volume (strictPolar K x h) := by
  let r : ℝ := h / (2 * D)
  have hr : 0 < r := by dsimp [r]; positivity
  let B (i : Fin n) := Metric.ball ((2 * r * (i : ℕ)) • e) r
  have hB (i : Fin n) : B i ⊆ strictPolar K x h := by
    apply translated_ball_subset_strictPolar hD hh (by positivity) hK hsupport
    have hi : ((i : ℕ) : ℝ) ≤ n := by exact_mod_cast i.isLt.le
    calc
      (2 * r * (i : ℕ)) * d = r * (2 * (i : ℕ) * d) := by ring
      _ ≤ r * (2 * n * d) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hd) hr.le
      _ ≤ r * D := mul_le_mul_of_nonneg_left hn hr.le
      _ = h / 2 := by dsimp [r]; field_simp
  have hpair : Pairwise (Disjoint on B) := separated_ball_family he hr
  have hvol : volume (⋃ i, B i) = (n : ℝ≥0∞) * volume (Metric.ball (0 : E m) r) := by
    rw [measure_iUnion hpair (fun _ => Metric.isOpen_ball.measurableSet), tsum_fintype]
    simp only [B, Measure.addHaar_ball_center, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [← hvol]
  exact measure_mono (iUnion_subset hB)

theorem alexandrov_packing_bound {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    {K : Set (E m)} (hK : IsCompact K) (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {x e : E m} (hx : x ∈ K) {D h d : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hdepth : h ≤ -u x) (hd : 0 ≤ d) (he : ‖e‖ = 1)
    (hKD : K ⊆ Metric.closedBall x D)
    (hsupport : ∀ z ∈ K, inner ℝ e (z - x) ≤ d)
    (n : ℕ) (hn : 2 * (n : ℝ) * d ≤ D) :
    (n : ℝ≥0∞) * volume (Metric.ball (0 : E m) (h / (2 * D))) ≤
      alexandrovMeasure u K := by
  apply (polar_packing_bound hD hh hd he hKD hsupport n hn).trans
  apply (measure_mono (fun p hp z hz => (hp z hz).trans_le hdepth)).trans
  exact (alexandrov_polar_bound hu hdom hK hboundary hx).trans
    (measure_mono fun _ hz => hz.1)

/-- Fixed depth and bounded total Alexandrov mass force a positive distance
from every supporting hyperplane, uniformly over compact regions of bounded diameter. -/
theorem uniform_supporting_distance (m : ℕ) {D h : ℝ} (hD : 0 < D) (hh : 0 < h)
    {M : ℝ≥0∞} (hM : M ≠ ∞) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u : E m → ℝ), ConvexOn ℝ univ u →
      conjugateDomain u = univ → ∀ (K : Set (E m)), IsCompact K →
      (∀ z ∈ frontier K, 0 ≤ u z) → alexandrovMeasure u K ≤ M →
      ∀ (x e : E m), x ∈ K → h ≤ -u x → ‖e‖ = 1 →
      K ⊆ Metric.closedBall x D → ∀ d : ℝ, 0 ≤ d →
      (∀ z ∈ K, inner ℝ e (z - x) ≤ d) → δ < d := by
  have hp : 0 < volume (Metric.ball (0 : E m) (h / (2 * D))) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (by positivity))
  obtain ⟨n, hn, hnM⟩ := ENNReal.exists_nat_pos_mul_gt hp.ne' hM
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨D / (2 * n), by positivity, ?_⟩
  intro u hu hdom K hK hb hmass x e hx hdepth he hKD d hd hsupport
  by_contra hnot
  have hnd : 2 * (n : ℝ) * d ≤ D := by
    have hle := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mp (le_of_not_gt hnot)
    nlinarith
  have hpack := alexandrov_packing_bound hu hdom hK hb hx hD hh hdepth hd he hKD hsupport n hnd
  exact (not_lt_of_ge (hpack.trans hmass)) hnM

end Submission.Obl.Entropy__smooth_gaussian_transport
