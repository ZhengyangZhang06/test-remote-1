import Mathlib

namespace Submission.Obl.Entropy__first_chaos_absorption

/-- The elementary negative-tail calculation in Appendix A, in dimensionless
variables u=r⁻², K=r*k, L=r³*l. The analytic Gaussian excess-moment estimates
are explicit hypotheses; the conclusion supplies both required certificates. -/
theorem negative_tail_algebra {u K L b : ℝ}
    (hu : 0 ≤ u) (hu' : u ≤ 1/36)
    (hK : 0 ≤ K) (hK' : K ≤ 1 + u/100)
    (hL : 0 ≤ L) (hL' : L ≤ 2*(1 + u/100))
    (hb : u*(1-(301/100)*u) ≤ b) (hb' : b ≤ u*(1 + u/100)) :
    let p := b + K*L*u^2 - (40/3)*L^2*u^3
    let h := K*(b-1/2) - (80/3)*(b-7/25)*L*u
    u/(1+7*u) ≤ p ∧ u*h^2 ≤ (67/100)^2*p := by
  dsimp only
  have hKcap : K ≤ 1001/1000 := by linarith
  have hLcap : L ≤ 1001/500 := by linarith
  have hb0 : 0 ≤ b := le_trans (mul_nonneg hu (by linarith)) hb
  have hbcap : b ≤ 7/250 := by
    calc
      b ≤ u*(1+u/100) := hb'
      _ ≤ (1/36 : ℝ)*(1+(1/36)/100) := by gcongr
      _ ≤ 7/250 := by norm_num
  have hLoss : (40/3 : ℝ)*L^2*u ≤ 153/100 := by
    calc
      _ ≤ (40/3 : ℝ)*(1001/500)^2*(1/36) := by gcongr
      _ ≤ 153/100 := by norm_num
  have hLoss' := mul_le_mul_of_nonneg_right hLoss (sq_nonneg u)
  have hKL : 0 ≤ K*L*u^2 := mul_nonneg (mul_nonneg hK hL) (sq_nonneg u)
  have hp : u*(1-(227/50)*u) ≤ b + K*L*u^2 - (40/3)*L^2*u^3 := by
    nlinarith only [hb, hLoss', hKL]
  have huu : u^2 ≤ u/36 := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu')]
  have hpcoarse : (4/5)*u ≤ b + K*L*u^2 - (40/3)*L^2*u^3 := by
    nlinarith only [hp, huu, hu]
  constructor
  · have hden : 0 < 1+7*u := by positivity
    apply (div_le_iff₀ hden).mpr
    have hp' := mul_le_mul_of_nonneg_right hp hden.le
    have hPoly : u ≤ u*(1-(227/50)*u)*(1+7*u) := by
      have hz : 0 ≤ (123/50 : ℝ)-(1589/50)*u := by linarith
      have := mul_nonneg (sq_nonneg u) hz
      nlinarith only [this]
    exact hPoly.trans hp'
  · have hPos : 0 ≤ (80/3 : ℝ)*(7/25-b)*L*u :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hL) hu
    have hPosCap : (80/3 : ℝ)*(7/25-b)*L*u ≤ 43/100 := by
      calc
        _ ≤ (80/3 : ℝ)*(7/25)*(1001/500)*(1/36) := by gcongr <;> linarith
        _ ≤ 43/100 := by norm_num
    have hNeg : K*(b-1/2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hK (by linarith)
    have hNegBound : -(501/1000 : ℝ) ≤ K*(b-1/2) := by
      nlinarith only [mul_nonneg hK hb0, hKcap]
    have hhLower : -(501/1000 : ℝ) ≤ K*(b-1/2) - (80/3)*(b-7/25)*L*u := by
      nlinarith only [hNegBound, hPos]
    have hhUpper : K*(b-1/2) - (80/3)*(b-7/25)*L*u ≤ 501/1000 := by
      nlinarith only [hNeg, hPosCap]
    have hhsq : (K*(b-1/2) - (80/3)*(b-7/25)*L*u)^2 ≤ (501/1000 : ℝ)^2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hhUpper) (sub_nonneg.mpr hhLower)]
    have hhMul := mul_le_mul_of_nonneg_left hhsq hu
    nlinarith only [hhMul, hpcoarse, hu]

end Submission.Obl.Entropy__first_chaos_absorption
