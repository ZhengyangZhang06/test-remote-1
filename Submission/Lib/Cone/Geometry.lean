/-
Adapted from: here:o003
Cone geometry and homogeneous integration written in session x0005.
-/

import Mathlib
import ChallengeDeps
import Submission.Lib.ConvexBody

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Submission.Lib.Cone

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cone {n : ℕ} (K : Set (E n)) : Set (E (n + 1)) :=
  {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i}

noncomputable def density {n : ℕ} (K : Set (E n)) : E (n + 1) → ℝ :=
  (cone K).indicator (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K))

lemma cone_closed {n : ℕ} {K : Set (E n)} (hK : IsCompact K) : IsClosed (cone K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h1 : IsClosed {p : E (n + 1) × K | 0 ≤ p.1 0} :=
    isClosed_le continuous_const (show Continuous (fun p : E (n + 1) × K => p.1 0) by fun_prop)
  have h2 : IsClosed {p : E (n + 1) × K |
      ∀ i : Fin n, p.1 i.succ = p.1 0 * (p.2 : E n) i} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have h : IsClosed {p : E (n + 1) × K |
      0 ≤ p.1 0 ∧ ∀ i : Fin n, p.1 i.succ = p.1 0 * (p.2 : E n) i} := h1.inter h2
  convert isClosedMap_fst_of_compactSpace _ h using 1
  ext z
  simp only [cone, mem_ofPred_eq, mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  aesop

lemma cone_convex {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K) : Convex ℝ (cone K) := by
  intro z hz w hw a b ha hb hab
  rcases hz with ⟨hz, x, hx, hzx⟩
  rcases hw with ⟨hw, y, hy, hwy⟩
  have ht : 0 ≤ a * z 0 + b * w 0 := add_nonneg (mul_nonneg ha hz) (mul_nonneg hb hw)
  change 0 ≤ a * z 0 + b * w 0 ∧ _
  refine ⟨ht, ?_⟩
  by_cases ht0 : a * z 0 + b * w 0 = 0
  · have haz : a * z 0 = 0 := (add_eq_zero_iff_of_nonneg (mul_nonneg ha hz)
        (mul_nonneg hb hw)).mp ht0 |>.1
    have hbw : b * w 0 = 0 := (add_eq_zero_iff_of_nonneg (mul_nonneg ha hz)
        (mul_nonneg hb hw)).mp ht0 |>.2
    refine ⟨x, hx, fun i => ?_⟩
    change a * z i.succ + b * w i.succ = (a * z 0 + b * w 0) * x i
    rw [hzx, hwy, ← mul_assoc, ← mul_assoc, haz, hbw]
    ring
  · refine ⟨((a * z 0) / (a * z 0 + b * w 0)) • x +
        ((b * w 0) / (a * z 0 + b * w 0)) • y,
      hK hx hy (div_nonneg (mul_nonneg ha hz) ht) (div_nonneg (mul_nonneg hb hw) ht)
        (by rw [← add_div, div_self ht0]), fun i => ?_⟩
    change a * z i.succ + b * w i.succ =
      (a * z 0 + b * w 0) *
        (a * z 0 / (a * z 0 + b * w 0) * x i +
          b * w 0 / (a * z 0 + b * w 0) * y i)
    rw [hzx, hwy]
    field_simp

lemma density_nonneg {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K) :
    ∀ z, 0 ≤ density K z := by
  intro z
  apply Set.indicator_nonneg
  intro _ _
  exact div_nonneg (Real.exp_pos _).le (mul_pos (by positivity)
    (Submission.Lib.ConvexBody.body_vol_pos hK)).le

lemma density_pos_iff {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K)
    (z : E (n + 1)) : 0 < density K z ↔ z ∈ cone K := by
  classical
  by_cases hz : z ∈ cone K
  · simp only [density, Set.indicator_of_mem hz, hz, iff_true]
    exact div_pos (Real.exp_pos _) (mul_pos (by positivity)
      (Submission.Lib.ConvexBody.body_vol_pos hK))
  · simp [density, hz]

lemma log_density {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K)
    {z : E (n + 1)} (hz : z ∈ cone K) :
    Real.log (density K z) = -z 0 - Real.log ((n.factorial : ℝ) * SimplexIsotropic.vol K) := by
  rw [density, Set.indicator_of_mem hz, Real.log_div (Real.exp_ne_zero _)
    (mul_ne_zero (by positivity) (ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK))),
    Real.log_exp]

lemma density_log_concave {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K) :
    ConcaveOn ℝ {z | 0 < density K z} (fun z => Real.log (density K z)) := by
  have hset : {z | 0 < density K z} = cone K := by
    ext z
    exact density_pos_iff hK z
  rw [hset]
  refine ⟨cone_convex hK.convex, ?_⟩
  intro z hz w hw a b ha hb hab
  dsimp only
  rw [log_density hK hz, log_density hK hw,
    log_density hK (cone_convex hK.convex hz hw ha hb hab)]
  change a * (-z 0 - _) + b * (-w 0 - _) ≤ -(a * z 0 + b * w 0) - _
  have hlog := congrArg (fun c : ℝ => c * Real.log ((n.factorial : ℝ) * SimplexIsotropic.vol K)) hab
  nlinarith only [hlog]

lemma density_upperSemicontinuous {n : ℕ} {K : Set (E n)}
    (hK : SimplexIsotropic.IsConvexBody K) : UpperSemicontinuous (density K) := by
  classical
  have hc : Continuous (fun z : E (n + 1) =>
      Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) := by fun_prop
  intro z r hr
  by_cases hz : z ∈ cone K
  · have hr' : Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K) < r := by
      simpa only [density, indicator_of_mem hz] using hr
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hr')] with w hw
    by_cases hwK : w ∈ cone K
    · simpa only [density, indicator_of_mem hwK] using hw
    · simpa only [density, indicator_of_notMem hwK] using
        lt_of_le_of_lt (density_nonneg hK z) hr
  · have hr' : 0 < r := by simpa only [density, indicator_of_notMem hz] using hr
    filter_upwards [(cone_closed hK.isCompact).isOpen_compl.mem_nhds hz] with w hw
    simpa only [density, indicator_of_notMem hw] using hr'

end Submission.Lib.Cone
