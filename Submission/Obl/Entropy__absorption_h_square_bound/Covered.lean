import Submission.Obl.Entropy__absorption_h_square_bound.Checks
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Approximation

namespace Submission.Obl.Entropy__absorption_h_square_bound

open Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- Reparameterize a checked model by its original real interval. -/
theorem square_bound_on_interval (M : Model)
    (hcheck : (squareGap.enclose M.initial).LowerBound 0)
    (happrox : ∀ x : ℝ, |x| ≤ 1 →
      |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8 ∧
      |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7)
    (hr : 0 < (M.radius : ℝ)) (a : ℝ)
    (ha : (M.center : ℝ)-M.radius ≤ a) (hb : a ≤ (M.center : ℝ)+M.radius) :
    (k a*(1+b a)-(3/2)*k a-(80/3)*(b a-7/25)*l a)^2 ≤
      (67/100 : ℝ)^2 * p a := by
  let x : ℝ := (a-M.center)/M.radius
  have hx : |x| ≤ 1 := by
    dsimp [x]
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he : M.parameter x = a := by
    dsimp [Model.parameter, x]
    field_simp
    nlinarith [hr.ne']
  obtain ⟨hq, hk⟩ := happrox x hx
  simpa only [he] using square_bound_of_model M hcheck hx hq hk

/-- The eleven certified intervals cover the required compact range. -/
theorem compact_square_bound (a : ℝ) (ha : -6 ≤ a) (hb : a ≤ 10) :
    (k a*(1+b a)-(3/2)*k a-(80/3)*(b a-7/25)*l a)^2 ≤
      (67/100 : ℝ)^2 * p a := by
  by_cases h0 : a ≤ -9/2
  · apply square_bound_on_interval model0 square_check0 approximation_0
      (by norm_num [model0]) a
    · norm_num [model0]
      linarith
    · norm_num [model0]
      linarith
  by_cases h1 : a ≤ -3
  · apply square_bound_on_interval model1 square_check1 approximation_1
      (by norm_num [model1]) a
    · norm_num [model1]
      linarith
    · norm_num [model1]
      linarith
  by_cases h2 : a ≤ -2
  · apply square_bound_on_interval model2 square_check2 approximation_2
      (by norm_num [model2]) a
    · norm_num [model2]
      linarith
    · norm_num [model2]
      linarith
  by_cases h3 : a ≤ -1
  · apply square_bound_on_interval model3 square_check3 approximation_3
      (by norm_num [model3]) a
    · norm_num [model3]
      linarith
    · norm_num [model3]
      linarith
  by_cases h4 : a ≤ 0
  · apply square_bound_on_interval model4 square_check4 approximation_4
      (by norm_num [model4]) a
    · norm_num [model4]
      linarith
    · norm_num [model4]
      linarith
  by_cases h5 : a ≤ 1/2
  · apply square_bound_on_interval model5 square_check5 approximation_5
      (by norm_num [model5]) a
    · norm_num [model5]
      linarith
    · norm_num [model5]
      linarith
  by_cases h6 : a ≤ 2
  · apply square_bound_on_interval model6 square_check6 approximation_6
      (by norm_num [model6]) a
    · norm_num [model6]
      linarith
    · norm_num [model6]
      linarith
  by_cases h7 : a ≤ 4
  · apply square_bound_on_interval model7 square_check7 approximation_7
      (by norm_num [model7]) a
    · norm_num [model7]
      linarith
    · norm_num [model7]
      linarith
  by_cases h8 : a ≤ 6
  · apply square_bound_on_interval model8 square_check8 approximation_8
      (by norm_num [model8]) a
    · norm_num [model8]
      linarith
    · norm_num [model8]
      linarith
  by_cases h9 : a ≤ 8
  · apply square_bound_on_interval model9 square_check9 approximation_9
      (by norm_num [model9]) a
    · norm_num [model9]
      linarith
    · norm_num [model9]
      linarith
  apply square_bound_on_interval model10 square_check10 approximation_10
    (by norm_num [model10]) a
  · norm_num [model10]
    linarith
  · norm_num [model10]
    linarith

end Submission.Obl.Entropy__absorption_h_square_bound
