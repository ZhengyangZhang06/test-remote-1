import Submission.Obl.Entropy__absorption_p_lower_bounds.Checks
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Approximation

namespace Submission.Obl.Entropy__absorption_p_lower_bounds

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

lemma parameter_covers (M : Model) (hr : 0 < M.radius) {a : ℝ}
    (ha : (M.center : ℝ)-M.radius ≤ a) (hb : a ≤ (M.center : ℝ)+M.radius) :
    ∃ x : ℝ, |x| ≤ 1 ∧ M.parameter x = a := by
  have hr' : (0 : ℝ) < M.radius := by exact_mod_cast hr
  refine ⟨(a-(M.center : ℝ))/(M.radius : ℝ), ?_, ?_⟩
  · apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hr').mpr
      linarith
    · apply (div_le_iff₀ hr').mpr
      linarith
  · dsimp [Model.parameter]
    rw [mul_div_cancel₀ _ hr'.ne']
    ring

lemma negative_on_interval (M : Model) (hr : 0 < M.radius)
    (happ : ∀ x : ℝ, |x| ≤ 1 →
      |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8 ∧
      |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7)
    (hcheck : (negativeExpr.enclose M.initial).LowerBound (1/10^6))
    {a : ℝ} (ha : (M.center : ℝ)-M.radius ≤ a) (hb : a ≤ (M.center : ℝ)+M.radius) :
    1/(7+a^2) ≤ p a := by
  obtain ⟨x,hx,he⟩ := parameter_covers M hr ha hb
  obtain ⟨hq,hk⟩ := happ x hx
  simpa only [he] using negative_of_check M hx hq hk hcheck

lemma positive_on_interval (M : Model) (c : ℚ) (hr : 0 < M.radius)
    (happ : ∀ x : ℝ, |x| ≤ 1 →
      |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8 ∧
      |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7)
    (hcheck : ((positiveExpr c).enclose M.initial).LowerBound (1/10^6))
    {a : ℝ} (ha : (M.center : ℝ)-M.radius ≤ a) (hb : a ≤ (M.center : ℝ)+M.radius) :
    (c : ℝ) ≤ p a := by
  obtain ⟨x,hx,he⟩ := parameter_covers M hr ha hb
  obtain ⟨hq,hk⟩ := happ x hx
  simpa only [he] using positive_of_check M c hx hq hk hcheck

lemma negative_bound {a : ℝ} (ha : -6 ≤ a) (hb : a ≤ 0) : 1/(7+a^2) ≤ p a := by
  by_cases h0 : a ≤ -9/2
  · apply negative_on_interval model0 (by norm_num [model0]) approximation_0 negative_check0
    · norm_num [model0]; linarith
    · norm_num [model0]; linarith
  by_cases h1 : a ≤ -3
  · apply negative_on_interval model1 (by norm_num [model1]) approximation_1 negative_check1
    · norm_num [model1]; linarith
    · norm_num [model1]; linarith
  by_cases h2 : a ≤ -2
  · apply negative_on_interval model2 (by norm_num [model2]) approximation_2 negative_check2
    · norm_num [model2]; linarith
    · norm_num [model2]; linarith
  by_cases h3 : a ≤ -1
  · apply negative_on_interval model3 (by norm_num [model3]) approximation_3 negative_check3
    · norm_num [model3]; linarith
    · norm_num [model3]; linarith
  apply negative_on_interval model4 (by norm_num [model4]) approximation_4 negative_check4
  · norm_num [model4]; linarith
  · norm_num [model4]; linarith

lemma large_positive_bound {a : ℝ} (ha : 4 ≤ a) (hb : a ≤ 10) : (23/50 : ℝ) ≤ p a := by
  by_cases h8 : a ≤ 6
  · have h := positive_on_interval model8 (23/50) (by norm_num [model8]) approximation_8
      positive_check8 (a := a) (by norm_num [model8]; linarith) (by norm_num [model8]; linarith)
    norm_num at h
    exact h
  by_cases h9 : a ≤ 8
  · have h := positive_on_interval model9 (23/50) (by norm_num [model9]) approximation_9
      positive_check9 (a := a) (by norm_num [model9]; linarith) (by norm_num [model9]; linarith)
    norm_num at h
    exact h
  have h := positive_on_interval model10 (23/50) (by norm_num [model10]) approximation_10
    positive_check10 (a := a) (by norm_num [model10]; linarith) (by norm_num [model10]; linarith)
  norm_num at h
  exact h

lemma positive_bound {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ 10) : (1/4 : ℝ) ≤ p a := by
  by_cases h5 : a ≤ 1/2
  · have h := positive_on_interval model5 (1/4) (by norm_num [model5]) approximation_5
      positive_check5 (a := a) (by norm_num [model5]; linarith) (by norm_num [model5]; linarith)
    norm_num at h
    exact h
  by_cases h6 : a ≤ 2
  · have h := positive_on_interval model6 (1/4) (by norm_num [model6]) approximation_6
      positive_check6 (a := a) (by norm_num [model6]; linarith) (by norm_num [model6]; linarith)
    norm_num at h
    exact h
  by_cases h7 : a ≤ 4
  · have h := positive_on_interval model7 (1/4) (by norm_num [model7]) approximation_7
      positive_check7 (a := a) (by norm_num [model7]; linarith) (by norm_num [model7]; linarith)
    norm_num at h
    exact h
  linarith [large_positive_bound (a := a) (by linarith) hb]

end Submission.Obl.Entropy__absorption_p_lower_bounds
