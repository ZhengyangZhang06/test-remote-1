import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Certificate
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Checks
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Approximation

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

theorem Model.checked_certificate (M : Model) (R : Bin) (hcheck : M.Check R)
    (hD : 0 < R.dmax ∨ R.negative = true) {x : ℝ} (hx : |x| ≤ 1)
    (hq : |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    (hk : |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7) :
    certificate R (M.parameter x) := by
  apply certificate_of_groups R _ hD
  intro A hA
  have hh := (hcheck A hA).le (A.holds (M.initial_holds hx hq hk) hx) hx
  norm_num at hh
  linarith

theorem certificate_interval0 (a : ℝ) (ha : (-6/1 : ℝ) ≤ a) (hb : a ≤ (-9/2 : ℝ)) :
    certificate binO a := by
  let x : ℝ := (a-(-21/4 : ℝ))/(3/4 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_0 x hx
  have hc := model0.checked_certificate binO check_model0
    (by norm_num [binO]) hx hq hk
  have he : model0.parameter x = a := by
    dsimp [x, Model.parameter, model0]
    ring
  rwa [he] at hc

theorem certificate_interval1 (a : ℝ) (ha : (-9/2 : ℝ) ≤ a) (hb : a ≤ (-3/1 : ℝ)) :
    certificate binO a := by
  let x : ℝ := (a-(-15/4 : ℝ))/(3/4 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_1 x hx
  have hc := model1.checked_certificate binO check_model1
    (by norm_num [binO]) hx hq hk
  have he : model1.parameter x = a := by
    dsimp [x, Model.parameter, model1]
    ring
  rwa [he] at hc

theorem certificate_interval2 (a : ℝ) (ha : (-3/1 : ℝ) ≤ a) (hb : a ≤ (-2/1 : ℝ)) :
    certificate binN a := by
  let x : ℝ := (a-(-5/2 : ℝ))/(1/2 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_2 x hx
  have hc := model2.checked_certificate binN check_model2
    (by norm_num [binN]) hx hq hk
  have he : model2.parameter x = a := by
    dsimp [x, Model.parameter, model2]
    ring
  rwa [he] at hc

theorem certificate_interval3 (a : ℝ) (ha : (-2/1 : ℝ) ≤ a) (hb : a ≤ (-1/1 : ℝ)) :
    certificate binM a := by
  let x : ℝ := (a-(-3/2 : ℝ))/(1/2 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_3 x hx
  have hc := model3.checked_certificate binM check_model3
    (by norm_num [binM]) hx hq hk
  have he : model3.parameter x = a := by
    dsimp [x, Model.parameter, model3]
    ring
  rwa [he] at hc

theorem certificate_interval4 (a : ℝ) (ha : (-1/1 : ℝ) ≤ a) (hb : a ≤ (0/1 : ℝ)) :
    certificate binC a := by
  let x : ℝ := (a-(-1/2 : ℝ))/(1/2 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_4 x hx
  have hc := model4.checked_certificate binC check_model4
    (by norm_num [binC]) hx hq hk
  have he : model4.parameter x = a := by
    dsimp [x, Model.parameter, model4]
    ring
  rwa [he] at hc

theorem certificate_interval5 (a : ℝ) (ha : (0/1 : ℝ) ≤ a) (hb : a ≤ (1/2 : ℝ)) :
    certificate binC a := by
  let x : ℝ := (a-(1/4 : ℝ))/(1/4 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_5 x hx
  have hc := model5.checked_certificate binC check_model5
    (by norm_num [binC]) hx hq hk
  have he : model5.parameter x = a := by
    dsimp [x, Model.parameter, model5]
    ring
  rwa [he] at hc

theorem certificate_interval6 (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (hb : a ≤ (2/1 : ℝ)) :
    certificate binP a := by
  let x : ℝ := (a-(5/4 : ℝ))/(3/4 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_6 x hx
  have hc := model6.checked_certificate binP check_model6
    (by norm_num [binP]) hx hq hk
  have he : model6.parameter x = a := by
    dsimp [x, Model.parameter, model6]
    ring
  rwa [he] at hc

theorem certificate_interval7 (a : ℝ) (ha : (2/1 : ℝ) ≤ a) (hb : a ≤ (4/1 : ℝ)) :
    certificate binP a := by
  let x : ℝ := (a-(3/1 : ℝ))/(1/1 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_7 x hx
  have hc := model7.checked_certificate binP check_model7
    (by norm_num [binP]) hx hq hk
  have he : model7.parameter x = a := by
    dsimp [x, Model.parameter, model7]
    ring
  rwa [he] at hc

theorem certificate_interval8 (a : ℝ) (ha : (4/1 : ℝ) ≤ a) (hb : a ≤ (6/1 : ℝ)) :
    certificate binT a := by
  let x : ℝ := (a-(5/1 : ℝ))/(1/1 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_8 x hx
  have hc := model8.checked_certificate binT check_model8
    (by norm_num [binT]) hx hq hk
  have he : model8.parameter x = a := by
    dsimp [x, Model.parameter, model8]
    ring
  rwa [he] at hc

theorem certificate_interval9 (a : ℝ) (ha : (6/1 : ℝ) ≤ a) (hb : a ≤ (8/1 : ℝ)) :
    certificate binT a := by
  let x : ℝ := (a-(7/1 : ℝ))/(1/1 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_9 x hx
  have hc := model9.checked_certificate binT check_model9
    (by norm_num [binT]) hx hq hk
  have he : model9.parameter x = a := by
    dsimp [x, Model.parameter, model9]
    ring
  rwa [he] at hc

theorem certificate_interval10 (a : ℝ) (ha : (8/1 : ℝ) ≤ a) (hb : a ≤ (10/1 : ℝ)) :
    certificate binT a := by
  let x : ℝ := (a-(9/1 : ℝ))/(1/1 : ℝ)
  have hx : |x| ≤ 1 := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  obtain ⟨hq,hk⟩ := approximation_10 x hx
  have hc := model10.checked_certificate binT check_model10
    (by norm_num [binT]) hx hq hk
  have he : model10.parameter x = a := by
    dsimp [x, Model.parameter, model10]
    ring
  rwa [he] at hc

noncomputable def row (a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  if a < -3 then (0, 9/100, 3/5, (59/200)*(7+a^2), 37/100, 14/25, 18/25, 13/100)
  else if a < -2 then (83/1000, 3/20, 101/100, 43/10, 29/100, 23/50, 18/25, 13/100)
  else if a < -1 then (7/50, 23/100, 119/100, 3, 29/100, 371/1000, 17/25, 13/100)
  else if a < 1/2 then (11/50, 171/500, 119/100, 43/25, 29/100, 199/500, 61/100, 123/1000)
  else if a < 4 then (337/1000, 9/20, 83/100, 87/100, 31/100, 2/5, 1/2, 3/50)
  else (89/200, 1/2, 1/5, 16/25, 8/25, 2/5, 12/25, 11/500)

noncomputable def localCert (a : ℝ) : Prop :=
  let R := row a
  let z := deriv l a/l a
  0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧
  (R.1 ≤ b a ∧ b a ≤ R.2.1 ∧ L a ≤ R.2.2.1 ∧ D a ≤ R.2.2.2.1 ∧
    R.2.2.2.2.1 ≤ D a*E a ∧ D a*E a ≤ R.2.2.2.2.2.1 ∧
    D a*(3/2)*b a ≤ R.2.2.2.2.2.2.1) ∧
  (∀ u v : ℝ, ((82/37)*(b a)^2-eta*b a+nu/4+(40/3)*(l a)^2)*u^2+
    2*(nu/2-eta*b a)*u*v+nu*v^2+D a*(E a*u+(3/2)*b a*v)^2+
    R.2.2.2.2.2.2.2*u^2+(3/4)*v^2 ≤ (43/100)*u^2+(26/100)*u*v+(68/25)*v^2) ∧
  (if a < -1 then -(2/25) ≤ z ∧ z ≤ 7/10 ∧ l a/(q a-a) ≤ 7/100
    else -(19/40) ≤ z ∧ z ≤ 0 ∧ l a/(q a-a) ≤ 97/1000) ∧
  4/5 ≤ 1+3*b a+k a*z ∧ 1+3*b a+k a*z ≤ 177/100

theorem compact_local_certificate (a : ℝ) (ha : -6 ≤ a) (hb : a ≤ 10) : localCert a := by
  by_cases h3 : a < -3
  · have hc : certificate binO a := by
      by_cases h : a < -9/2
      · exact certificate_interval0 a (by linarith) (by linarith)
      · exact certificate_interval1 a (by linarith) (by linarith)
    have h1 : a < -1 := by linarith
    simpa [neg_div, localCert, row, certificate, binO, h3, h1] using hc
  · by_cases h2 : a < -2
    · have hc := certificate_interval2 a (by linarith) (by linarith)
      have h1 : a < -1 := by linarith
      simpa [neg_div, localCert, row, certificate, binN, h3, h2, h1] using hc
    · by_cases h1 : a < -1
      · have hc := certificate_interval3 a (by linarith) (by linarith)
        simpa [neg_div, localCert, row, certificate, binM, h3, h2, h1] using hc
      · by_cases hh : a < 1/2
        · have hh' : a < (2 : ℝ)⁻¹ := by simpa only [one_div] using hh
          have hc : certificate binC a := by
            by_cases h : a < 0
            · exact certificate_interval4 a (by linarith) (by linarith)
            · exact certificate_interval5 a (by linarith) (by linarith)
          simpa [neg_div, localCert, row, certificate, binC, h3, h2, h1, hh, hh'] using hc
        · have hh' : ¬a < (2 : ℝ)⁻¹ := by simpa only [one_div] using hh
          by_cases h4 : a < 4
          · have hc : certificate binP a := by
              by_cases h : a < 2
              · exact certificate_interval6 a (by linarith) (by linarith)
              · exact certificate_interval7 a (by linarith) (by linarith)
            simpa [neg_div, localCert, row, certificate, binP, h3, h2, h1, hh, hh', h4] using hc
          · have hc : certificate binT a := by
              by_cases h6 : a < 6
              · exact certificate_interval8 a (by linarith) (by linarith)
              · by_cases h8 : a < 8
                · exact certificate_interval9 a (by linarith) (by linarith)
                · exact certificate_interval10 a (by linarith) (by linarith)
            simpa [neg_div, localCert, row, certificate, binT, h3, h2, h1, hh, hh', h4] using hc

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
