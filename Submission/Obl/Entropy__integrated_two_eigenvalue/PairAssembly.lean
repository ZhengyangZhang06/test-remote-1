import Submission.Obl.Entropy__integrated_two_eigenvalue.PairAlgebra
import Submission.Obl.Entropy__integrated_two_eigenvalue.Threshold

namespace Submission.Obl.Entropy__integrated_two_eigenvalue

lemma weighted_mean_bound (Pm Pp um up : ℝ)
    (hu : 0 ≤ up) (hum : up ≤ um) :
    Pm*um^2+Pp*up^2 ≤ max Pm ((Pm+Pp)/2)*(um^2+up^2) := by
  let H := max Pm ((Pm+Pp)/2)
  have h1 : Pm ≤ H := le_max_left _ _
  have h2 : (Pm+Pp)/2 ≤ H := le_max_right _ _
  have hsq : up^2 ≤ um^2 := (sq_le_sq₀ hu (hu.trans hum)).mpr hum
  have h3 := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hsq)
  have h4 := mul_nonneg (show 0 ≤ 2*H-Pm-Pp by linarith) (sq_nonneg up)
  change _ ≤ H*(um^2+up^2)
  nlinarith only [h3, h4]

/-- Completing the two endpoint estimates gives exactly the transport separation surplus. -/
lemma pair_cost_bound (Q Cm Cp Z δ m Pm Pp um up : ℝ)
    (hm : 0 ≤ m) (hu : 0 ≤ up) (hum : up ≤ um)
    (hmean : um^2+up^2 ≤ (1/2)*(1+δ^2/36))
    (hCm : Cm ≤ Q+Z^2*(Pm*δ^2*um^2))
    (hCp : Cp ≤ Q+Z^2*(Pp*δ^2*up^2))
    (hthreshold : max Pm ((Pm+Pp)/2) ≤ threshold m δ) :
    (Cm+Cp)/2 ≤ Q+((1+m)/16)*(1+δ^2/30+δ^4/1680)*δ^2*Z^2 := by
  have hw := weighted_mean_bound Pm Pp um up hu hum
  have ht0 : 0 ≤ threshold m δ := le_trans (by positivity) (threshold_lower m δ hm)
  have hw' : Pm*um^2+Pp*up^2 ≤ threshold m δ*((1/2)*(1+δ^2/36)) := by
    calc
      _ ≤ max Pm ((Pm+Pp)/2)*(um^2+up^2) := hw
      _ ≤ threshold m δ*(um^2+up^2) :=
        mul_le_mul_of_nonneg_right hthreshold (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean ht0
  have hz := mul_le_mul_of_nonneg_left hw' (show 0 ≤ Z^2*δ^2/2 by positivity)
  have hd : 1+δ^2/36 ≠ 0 := ne_of_gt (by positivity)
  have he : Z^2*δ^2/2*(threshold m δ*((1/2)*(1+δ^2/36))) =
      ((1+m)/16)*(1+δ^2/30+δ^4/1680)*δ^2*Z^2 := by
    unfold threshold
    field_simp
    <;> ring
  rw [he] at hz
  nlinarith only [hCm, hCp, hz]

end Submission.Obl.Entropy__integrated_two_eigenvalue
