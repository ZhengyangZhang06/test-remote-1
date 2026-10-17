import Submission.Obl.Entropy__smooth_gaussian_transport.Normalization
import Submission.Obl.Entropy__smooth_gaussian_transport.LinearChange

open MeasureTheory Set Filter Module
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def simplexCenter (m : ℕ) : E m :=
  WithLp.toLp 2 (fun _ => 1 / ((m : ℝ) + 1))

theorem ball_subset_coordinate_simplex {m : ℕ} (hm : 1 ≤ m) :
    Metric.closedBall (simplexCenter m) (1 / ((m : ℝ) * (m + 1))) ⊆
      {y : E m | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} := by
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let c : ℝ := 1 / ((m : ℝ) + 1)
  let r : ℝ := 1 / ((m : ℝ) * (m + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hrc : r ≤ c := by
    dsimp [r, c]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hsum : (m : ℝ) * (c + r) = 1 := by
    dsimp [c, r]
    field_simp
  intro y hy
  have hnorm : ‖y - simplexCenter m‖ ≤ r := hy
  have hcoord (i : Fin m) : |y i - c| ≤ r := by
    exact (PiLp.norm_apply_le (y - simplexCenter m) i).trans hnorm
  constructor
  · intro i
    have h := (abs_le.mp (hcoord i)).1
    linarith
  · calc
      ∑ i, y i ≤ (∑ _ : Fin m, (c + r)) := Finset.sum_le_sum fun i _ => by
        have h := (abs_le.mp (hcoord i)).2
        linarith
      _ = (m : ℝ) * (c + r) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 1 := hsum

theorem coordinate_cube_subset_ball {m : ℕ} :
    {y : E m | ∀ i, |y i| ≤ 1} ⊆
      Metric.closedBall (simplexCenter m) ((m : ℝ) + 1) := by
  have hc : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
  have hcnorm : ‖simplexCenter m‖ ≤ 1 := by
    apply (norm_le_sum_abs_coordinates _).trans
    change (∑ _ : Fin m, |1 / ((m : ℝ) + 1)|) ≤ 1
    simp only [abs_of_nonneg hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one_div]
    exact (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr (by linarith)
  intro y hy
  have hynorm : ‖y‖ ≤ (m : ℝ) := by
    apply (norm_le_sum_abs_coordinates y).trans
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hy i)
  change ‖y - simplexCenter m‖ ≤ (m : ℝ) + 1
  exact (norm_sub_le y (simplexCenter m)).trans (add_le_add hynorm hcnorm)

/-- A compact convex neighborhood admits a linear normalization between two balls
whose radii depend only on the dimension. -/
theorem exists_ball_normalization {m : ℕ} (hm : 1 ≤ m) {K : Set (E m)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : E m)) :
    ∃ L : E m ≃L[ℝ] E m,
      Metric.closedBall (simplexCenter m) (1 / ((m : ℝ) * (m + 1))) ⊆ L '' K ∧
      L '' K ⊆ Metric.closedBall (simplexCenter m) ((m : ℝ) + 1) := by
  obtain ⟨L, hinner, houter⟩ := exists_simplex_cube_normalization hK hc h0
  exact ⟨L, (ball_subset_coordinate_simplex hm).trans hinner,
    houter.trans coordinate_cube_subset_ball⟩

/-- Every compact section containing the origin in its interior can be normalized
with constants independent of the section. -/
theorem section_ball_normalization {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (p : E m) {r : ℝ} (hr : u 0 < r) :
    ∃ L : E m ≃L[ℝ] E m,
      Metric.closedBall (simplexCenter m) (1 / ((m : ℝ) * (m + 1))) ⊆
        L '' {x | u x - inner ℝ p x ≤ r} ∧
      L '' {x | u x - inner ℝ p x ≤ r} ⊆
        Metric.closedBall (simplexCenter m) ((m : ℝ) + 1) := by
  have hc : Continuous (fun x => u x - inner ℝ p x) :=
    hu.locallyLipschitz.continuous.sub (continuous_const.inner continuous_id)
  have hconv : Convex ℝ {x | u x - inner ℝ p x ≤ r} := by
    simpa only [tilt, sub_zero, mem_univ, true_and] using (tilt_convex hu p 0).convex_le r
  have hn : {x | u x - inner ℝ p x ≤ r} ∈ 𝓝 (0 : E m) := by
    apply mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds (by simpa using hr))
    intro x hx
    exact (show u x - inner ℝ p x < r from hx).le
  exact exists_ball_normalization hm
    (isCompact_tilted_sublevel_of_finite_conjugate hu.locallyLipschitz.continuous hdom p r)
    hconv hn

end Submission.Obl.Entropy__smooth_gaussian_transport
