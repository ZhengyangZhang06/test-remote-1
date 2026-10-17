import Submission.Obl.Entropy__smooth_gaussian_transport.ConvexConvergence

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A pointwise bounded family of finite convex functions has a continuous
convex upper envelope. -/
theorem convex_upper_envelope {m : ℕ} {u : ℕ → E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hb : ∀ x, BddAbove (range (fun n => u n x))) :
    ConvexOn ℝ univ (fun x => ⨆ n, u n x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb' hab
  apply ciSup_le
  intro n
  exact ((hu n).2 hx hy ha hb' hab).trans (by
    simp only [smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (hb x) n) ha)
      (mul_le_mul_of_nonneg_left (le_ciSup (hb y) n) hb'))

/-- Pointwise bounded convex sequences are uniformly bounded on each compact
set. The lower bound follows from the midpoint inequality and a bound at zero. -/
theorem convex_sequence_uniform_abs_bound {m : ℕ} {u : ℕ → E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => u n x)))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, ∀ x ∈ K, |u n x| ≤ M := by
  let U : E m → ℝ := fun x => ⨆ n, u n x
  have hU : Continuous U :=
    (convex_upper_envelope hu (fun x => (hb x).bddAbove)).locallyLipschitz.continuous
  obtain ⟨A, hA⟩ := hK.bddAbove_image hU.continuousOn
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hU.comp continuous_neg).continuousOn
  obtain ⟨c, hc⟩ := (hb 0).bddBelow
  refine ⟨|A| + |B| + 2 * |c| + 1, by positivity, ?_⟩
  intro n x hx
  have hxU : u n x ≤ A :=
    (le_ciSup (hb x).bddAbove n).trans (hA (mem_image_of_mem _ hx))
  have hnU : u n (-x) ≤ B :=
    (le_ciSup (hb (-x)).bddAbove n).trans (hB (mem_image_of_mem _ hx))
  have hc0 : c ≤ u n 0 := hc (mem_range_self n)
  have hmid : u n ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x)) ≤
      (1 / 2 : ℝ) • u n x + (1 / 2 : ℝ) • u n (-x) :=
    (hu n).2 (mem_univ x) (mem_univ (-x)) (by norm_num) (by norm_num) (by norm_num)
  have hz : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by simp
  rw [hz] at hmid
  simp only [smul_eq_mul] at hmid
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self A, le_abs_self B, neg_abs_le c,
    abs_nonneg A, abs_nonneg B, abs_nonneg c]

/-- The same Lipschitz constant works for every member of a pointwise bounded
convex sequence on a given compact set. -/
theorem convex_sequence_uniform_lipschitz {m : ℕ} {u : ℕ → E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => u n x)))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ L : NNReal, ∀ n, LipschitzOnWith L (u n) K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨M, hM, hbound⟩ := convex_sequence_uniform_abs_bound hu hb
    (isCompact_closedBall (0 : E m) (R + 2))
  refine ⟨(2 * M).toNNReal, fun n => ?_⟩
  have hball := ((hu n).subset (subset_univ (Metric.ball (0 : E m) (R + 2)))
    (convex_ball _ _)).lipschitzOnWith_of_abs_le (ε := 1) (by norm_num)
    (fun x hx => hbound n x (by exact le_of_lt hx))
  simp only [div_one] at hball
  apply hball.mono
  intro x hx
  simp only [Metric.mem_ball, dist_zero_right]
  linarith [hR x hx]

/-- A pointwise bounded family of convex functions is equicontinuous. -/
theorem convex_sequence_equicontinuous {m : ℕ} {u : ℕ → E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => u n x))) : Equicontinuous u := by
  intro x
  obtain ⟨L, hL⟩ := convex_sequence_uniform_lipschitz hu hb (isCompact_closedBall x 1)
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε / (L + 1)), lt_min (by norm_num) (by positivity), ?_⟩
  intro y hy n
  have hxy : dist y x < 1 := hy.trans_le (min_le_left _ _)
  have hxyε : dist y x < ε / (L + 1) := hy.trans_le (min_le_right _ _)
  have hxb : x ∈ Metric.closedBall x 1 := by simp
  have hyb : y ∈ Metric.closedBall x 1 := hxy.le
  have hdist := (hL n).dist_le_mul y hyb x hxb
  rw [dist_comm (u n x) (u n y)]
  apply hdist.trans_lt
  have hden : (0 : ℝ) < L + 1 := by positivity
  have hmul := (lt_div_iff₀ hden).mp hxyε
  nlinarith [dist_nonneg (x := y) (y := x)]

/-- Pointwise convergence of finite convex functions is uniform on compact
sets. No regularity of the limit is assumed. -/
theorem tendstoUniformlyOn_of_convex_pointwise {m : ℕ} {u : ℕ → E m → ℝ}
    {v : E m → ℝ} (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {K : Set (E m)} (hK : IsCompact K) : TendstoUniformlyOn u v atTop K := by
  have heq := convex_sequence_equicontinuous hu
    (fun x => (hlim x).cauchySeq.isBounded_range)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heqK : Equicontinuous (fun n (x : K) => u n x) :=
    equicontinuous_restrict_iff u |>.mpr (heq.equicontinuousOn K)
  rw [tendstoUniformlyOn_iff_restrict]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (heqK.tendsto_uniformFun_iff_pi atTop (fun x : K => v x)).mpr
  exact tendsto_pi_nhds.mpr (fun x => hlim x)

end Submission.Obl.Entropy__smooth_gaussian_transport
