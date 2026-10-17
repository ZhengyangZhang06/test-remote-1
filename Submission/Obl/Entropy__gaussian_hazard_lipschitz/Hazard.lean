import Mathlib.Analysis.Calculus.MeanValue
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.CDF

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__gaussian_hazard_lipschitz

noncomputable def hazard (x : ℝ) : ℝ := pdf x / mass (-x)

lemma hasDerivAt_hazard (x : ℝ) :
    HasDerivAt hazard (hazard x * (hazard x - x)) x := by
  have hm : HasDerivAt (fun t => mass (-t)) (-pdf x) x := by
    simpa only [pdf_neg, mul_neg_one] using!
      (hasDerivAt_mass (-x)).comp x (hasDerivAt_neg' x)
  convert! (hasDerivAt_pdf x).div hm (mass_pos (-x)).ne' using 1
  dsimp only [hazard]
  field_simp [(mass_pos (-x)).ne']
  ring

lemma hazard_derivative_bounds (x : ℝ) :
    0 ≤ hazard x * (hazard x - x) ∧ hazard x * (hazard x - x) ≤ 1 := by
  have hmass := mass_pos (-x)
  have hq : 0 < hazard x := div_pos (pdf_pos x) hmass
  have hqm : hazard x * mass (-x) = pdf x := div_mul_cancel₀ _ hmass.ne'
  have hm := mean_le_endpoint (-x)
  rw [pdf_neg] at hm
  have hx : x ≤ hazard x := by
    apply (le_div_iff₀ hmass).mpr
    nlinarith only [hm]
  refine ⟨mul_nonneg hq.le (sub_nonneg.mpr hx), ?_⟩
  have hv := shifted_second_moment_nonneg (-x) (hazard x)
  rw [pdf_neg, ← hqm] at hv
  have hbound : 0 ≤ mass (-x) * (1 - hazard x * (hazard x - x)) := by
    nlinarith only [hv]
  have := nonneg_of_mul_nonneg_right hbound hmass
  linarith

lemma hazard_lipschitz (x y : ℝ) : |hazard x - hazard y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := hazard) (f' := fun t => hazard t * (hazard t - t)) (C := 1)
    (fun t (_ : t ∈ (univ : Set ℝ)) => (hasDerivAt_hazard t).hasDerivWithinAt)
    (fun t _ => ?_) (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ y) (mem_univ x)
  · simpa only [Real.norm_eq_abs, one_mul] using h
  · rw [Real.norm_eq_abs, abs_of_nonneg (hazard_derivative_bounds t).1]
    exact (hazard_derivative_bounds t).2

end Submission.Obl.Entropy__gaussian_hazard_lipschitz
