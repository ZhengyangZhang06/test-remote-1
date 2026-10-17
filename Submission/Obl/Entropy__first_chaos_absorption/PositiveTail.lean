import Mathlib

namespace Submission.Obl.Entropy__first_chaos_absorption

/-- Generous scalar bounds suffice for both Proposition 3.5 certificates in
the positive tail; no derivative remainder beyond `b` and `l` is needed. -/
lemma positive_tail_algebra {k b l : ℝ}
    (hk : 0 ≤ k) (hb : 47/100 ≤ b) (hb' : b ≤ 1/2)
    (hl : 0 ≤ l) (hl' : l ≤ 1/50) (hkb : k*(1/2-b) ≤ 1/5) :
    let p := b+k*l-(40/3)*l^2
    let h := k*(b-1/2)-(80/3)*(b-7/25)*l
    23/50 ≤ p ∧ h^2 ≤ (67/100)^2*p := by
  dsimp only
  have hlsq : l^2 ≤ (1/50 : ℝ)^2 := by nlinarith
  have hp : 23/50 ≤ b+k*l-(40/3)*l^2 := by
    nlinarith only [hb, hlsq, mul_nonneg hk hl]
  refine ⟨hp, ?_⟩
  have hklow : -(1/5 : ℝ) ≤ k*(b-1/2) := by nlinarith only [hkb]
  have hkhi : k*(b-1/2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith)
  have hsecond0 : 0 ≤ (80/3 : ℝ)*(b-7/25)*l :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hl
  have hsecond1 : (80/3 : ℝ)*(b-7/25)*l ≤ 3/25 := by
    calc
      _ ≤ (80/3 : ℝ)*(1/2-7/25)*(1/50) := by gcongr
      _ ≤ 3/25 := by norm_num
  have hh0 : -(8/25 : ℝ) ≤ k*(b-1/2)-(80/3)*(b-7/25)*l := by linarith
  have hh1 : k*(b-1/2)-(80/3)*(b-7/25)*l ≤ 0 := by linarith
  have hhsq : (k*(b-1/2)-(80/3)*(b-7/25)*l)^2 ≤ (8/25 : ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh0) (neg_nonneg.mpr hh1)]
  nlinarith only [hhsq, hp]

end Submission.Obl.Entropy__first_chaos_absorption
