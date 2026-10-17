import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Enclosures
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Quadratic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

/-- The certificate in its negative-tail row, after differentiating the scalar functions. -/
def NegativeCertificate (a q k b l t : ℝ) : Prop :=
  0 < pValue k b l ∧ 0 < b ∧ b < 1 / 2 ∧ 0 < l ∧
    (0 ≤ b ∧ b ≤ 9 / 100 ∧ (40 / 3) * l ≤ 3 / 5 ∧
      dValue k b l ≤ (59 / 200) * (7 + a ^ 2) ∧
      37 / 100 ≤ dValue k b l * eValue k b l ∧
      dValue k b l * eValue k b l ≤ 14 / 25 ∧
      dValue k b l * (3 / 2) * b ≤ 18 / 25) ∧
    (∀ u v : ℝ,
      ((82 / 37) * b ^ 2 - eta * b + nu / 4 + (40 / 3) * l ^ 2) * u ^ 2 +
      2 * (nu / 2 - eta * b) * u * v + nu * v ^ 2 +
      dValue k b l * (eValue k b l * u + (3 / 2) * b * v) ^ 2 +
      (13 / 100) * u ^ 2 + (3 / 4) * v ^ 2 ≤
      (43 / 100) * u ^ 2 + (26 / 100) * u * v + (68 / 25) * v ^ 2) ∧
    (-(2 / 25) ≤ t / l ∧ t / l ≤ 7 / 10 ∧ l / (q - a) ≤ 7 / 100) ∧
    4 / 5 ≤ 1 + 3 * b + k * (t / l) ∧
    1 + 3 * b + k * (t / l) ≤ 177 / 100

lemma negative_certificate_of_data {r q k b l t : ℝ} (hr : 6 ≤ r) (hq : 0 ≤ q)
    (h : TailData r⁻¹ k b l t) : NegativeCertificate (-r) q k b l t := by
  have hr0 : 0 < r := by linarith
  have hrne := hr0.ne'
  have hc := coefficient_bounds h
  have he := hc.basic
  have hPr : 1 ≤ pValue k b l * (7 + r ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hc.p_tail (sq_nonneg r)
    field_simp at hh
    nlinarith only [hh]
  have hD : dValue k b l ≤ (59 / 200) * (7 + (-r) ^ 2) := by
    calc
      dValue k b l = dValue k b l * 1 := (mul_one _).symm
      _ ≤ dValue k b l * (pValue k b l * (7 + r ^ 2)) :=
        mul_le_mul_of_nonneg_left hPr hc.d_pos.le
      _ = (5 / 17) * (7 + r ^ 2) := by rw [← mul_assoc, hc.dp]
      _ ≤ (59 / 200) * (7 + (-r) ^ 2) := by
        rw [neg_sq]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hz0 : 0 < t / l := div_pos he.t_pos he.l_pos
  have hz : t / l ≤ 61 / 100 := (div_le_iff₀ he.l_pos).2 (by linarith only [he.t_le])
  have hchi : l / (q - -r) ≤ 7 / 100 := by
    apply (div_le_iff₀ (by linarith : 0 < q - -r)).2
    nlinarith only [he.l_le, hr, hq]
  have hk : k ≤ 1 / 6 := h.k_le.trans h.s_le
  have hkz : k * (t / l) ≤ (1 / 6 : ℝ) * (61 / 100) :=
    mul_le_mul hk hz hz0.le (by norm_num)
  refine ⟨hc.p_pos, he.b_pos, by linarith only [he.b_le], he.l_pos,
    ⟨he.b_pos.le, by linarith only [he.b_le], by linarith only [he.l_le], hD,
      by linarith only [hc.de_lower], by linarith only [hc.de_upper],
      by linarith only [hc.db_upper]⟩,
    local_surplus hc, ⟨by linarith only [hz0], by linarith only [hz], hchi⟩, ?_, ?_⟩
  · nlinarith only [he.b_pos, mul_pos h.k_pos hz0]
  · nlinarith only [he.b_le, hkz]

open Submission.Lib.GaussianTransport

lemma negative_certificate {a : ℝ} (ha : a ≤ -6) :
    NegativeCertificate a (gaussianHazard a) (transportRatio a) (transportSlope a)
      (transportCurvature a) (deriv transportCurvature a) := by
  have hr : 6 ≤ -a := by linarith
  simpa only [neg_neg] using negative_certificate_of_data hr
    (gaussianHazard_pos a).le (normalized_enclosures hr)

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
