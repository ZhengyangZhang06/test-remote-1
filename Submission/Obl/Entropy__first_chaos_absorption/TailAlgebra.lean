import Mathlib

namespace Submission.Obl.Entropy__first_chaos_absorption

/-- Convert alternating Mills bounds and the exponentially small logarithmic
correction to the normalized moment estimates needed by the tail certificate. -/
lemma normalized_tail_moments {u J K Q b L : ℝ}
    (hu : 0 < u) (hu' : u ≤ 1/36)
    (hJ1 : 1-u ≤ J) (hJ2 : J ≤ 1-u+3*u^2)
    (hJ3 : 1-u+3*u^2-15*u^3 ≤ J) (hJ0 : J ≤ 1)
    (hK : 0 ≤ K) (hKlo : J-u^3/1000 ≤ K) (hKhi : K ≤ J)
    (hQ : 0 ≤ Q) (hQhi : Q ≤ u^3/500)
    (hb : b = 1-K*(1+Q))
    (hL : u^2*L = K*(1+u)-1+(K-1)*Q) :
    K ≤ 1+u/100 ∧ 0 ≤ L ∧ L ≤ 21/10 ∧
      u*(1-(301/100)*u) ≤ b ∧ b ≤ u*(1+u/100) := by
  have hK1 : K ≤ 1 := hKhi.trans hJ0
  have hu2 : u^2 ≤ 1/1296 := by nlinarith [sq_nonneg (u-1/36)]
  have hu3 : u^3 ≤ u^2/36 := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu')]
  have hQ2 : Q ≤ u^2/100 := by linarith
  have hKQ : 0 ≤ K*Q := mul_nonneg hK hQ
  have hKQhi : K*Q ≤ Q := by nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hQ]
  have hbLo : u*(1-(301/100)*u) ≤ b := by nlinarith [hJ2, hKhi]
  have hbHi : b ≤ u*(1+u/100) := by nlinarith [hJ1, hKlo]
  have hLHi : L ≤ 21/10 := by
    have hprod := mul_le_mul_of_nonneg_right (hKhi.trans hJ2) (show 0 ≤ 1+u by positivity)
    have hnegative : (K-1)*Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hQ
    have hLmul : u^2*L ≤ (21/10)*u^2 := by nlinarith only [hL, hprod, hnegative, hu3]
    nlinarith only [hLmul, sq_pos_of_pos hu]
  have hLLo : 0 ≤ L := by
    have hKlow : 1-u+3*u^2-16*u^3 ≤ K := by nlinarith [pow_nonneg hu.le 3]
    have hprod := mul_le_mul_of_nonneg_right hKlow (show 0 ≤ 1+u by positivity)
    have hqpart : -Q ≤ (K-1)*Q := by nlinarith only [hKQ]
    have hpoly : 0 ≤ u^2*(2-13*u-16*u^2-1/100) := by
      apply mul_nonneg (sq_nonneg u)
      nlinarith only [hu', hu2]
    have hmul : 0 ≤ u^2*L := by nlinarith only [hprod, hqpart, hL, hQ2, hpoly]
    exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_pos hu)
  exact ⟨by linarith, hLLo, hLHi, hbLo, hbHi⟩

end Submission.Obl.Entropy__first_chaos_absorption
