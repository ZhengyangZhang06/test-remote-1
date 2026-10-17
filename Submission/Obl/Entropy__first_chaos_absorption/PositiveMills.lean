import Mathlib

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def millsCurvature (u T J : ℝ) : ℝ :=
  J/2+1-(1-J)/(2*u)+T*((1+u)*J-1)-1/J

lemma millsCurvature_mono {u T x y : ℝ} (hu : 0 < u) (hT : 0 ≤ T)
    (hx : 0 < x) (hxy : x ≤ y) : millsCurvature u T x ≤ millsCurvature u T y := by
  have hi := one_div_le_one_div_of_le hx hxy
  have ha := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 1+u by positivity)
  have hb := mul_le_mul_of_nonneg_left ha hT
  have hc := div_le_div_of_nonneg_right hxy (show 0 ≤ 2*u by positivity)
  unfold millsCurvature
  rw [sub_div, sub_div]
  linarith

/-- Direct Mills enclosures give the needed sign and size of the second
transport derivative without differentiating an asymptotic remainder. -/
lemma millsCurvature_bounds {u T J : ℝ} (hu : 0 < u) (hu' : u ≤ 1/100)
    (hT : 3 ≤ T) (hJlo : 1-u+3*u^2-15*u^3 ≤ J)
    (hJhi : J ≤ 1-u+3*u^2) :
    0 ≤ millsCurvature u T J ∧ millsCurvature u T J ≤ (4+3*T)*u^2 := by
  let lo := 1-u+3*u^2-15*u^3
  let hi := 1-u+3*u^2
  have hu2 : u^2 ≤ u := by nlinarith [mul_nonneg hu.le (show 0 ≤ 1-u by linarith)]
  have hu3 : u^3 ≤ u := by
    have hh := mul_le_mul_of_nonneg_right hu2 hu.le
    nlinarith only [hh, hu2]
  have hlo : 0 < lo := by
    have hh : 0 ≤ u^2*(3-15*u) := mul_nonneg (sq_nonneg _) (by linarith)
    dsimp [lo]
    nlinarith only [hh, hu']
  have hhi : 0 < hi := by dsimp [hi]; nlinarith [sq_nonneg u]
  have hJ : 0 < J := hlo.trans_le hJlo
  have hT0 : 0 ≤ T := by linarith
  constructor
  · have hg : 0 ≤ millsCurvature u 3 lo := by
      have hp : 0 ≤ 2-(111/2)*u-(33/2)*u^2-(171/2)*u^3+
          (1035/2)*u^4+675*u^5 := by
        nlinarith only [hu', hu2, hu3, pow_nonneg hu.le 4, pow_nonneg hu.le 5]
      have hid : millsCurvature u 3 lo * lo = u^2 *
          (2-(111/2)*u-(33/2)*u^2-(171/2)*u^3+(1035/2)*u^4+675*u^5) := by
        unfold millsCurvature
        field_simp [hu.ne', hlo.ne']
        dsimp [lo]
        ring
      apply nonneg_of_mul_nonneg_left _ hlo
      rw [hid]
      exact mul_nonneg (sq_nonneg _) hp
    have hcoeff : 0 ≤ (1+u)*lo-1 := by
      have hh : 0 ≤ u^2*(2-12*u-15*u^2) := by
        apply mul_nonneg (sq_nonneg _)
        nlinarith only [hu', hu2]
      convert! hh using 1 <;> dsimp [lo] <;> ring
    have hm : millsCurvature u 3 lo ≤ millsCurvature u T lo := by
      have hh := mul_nonneg (show 0 ≤ T-3 by linarith) hcoeff
      unfold millsCurvature
      nlinarith only [hh]
    exact (hg.trans hm).trans (millsCurvature_mono hu hT0 hlo hJlo)
  · have hg : millsCurvature u T hi ≤ (4+3*T)*u^2 := by
      have hp : 0 ≤ (1/2 : ℝ)-(11/2)*u+(15/2)*u^2 := by
        nlinarith only [hu', sq_nonneg u]
      have hq : 0 ≤ 1-4*u+6*u^2-9*u^3 := by
        nlinarith only [hu', hu3, sq_nonneg u]
      have hid : ((4+3*T)*u^2-millsCurvature u T hi)*hi = u^2 *
          ((1/2)-(11/2)*u+(15/2)*u^2+T*(1-4*u+6*u^2-9*u^3)) := by
        unfold millsCurvature
        field_simp [hu.ne', hhi.ne']
        dsimp [hi]
        ring
      have hh : 0 ≤ ((4+3*T)*u^2-millsCurvature u T hi)*hi := by
        rw [hid]
        exact mul_nonneg (sq_nonneg _) (add_nonneg hp (mul_nonneg hT0 hq))
      have hh' := nonneg_of_mul_nonneg_left hh hhi
      linarith only [hh']
    exact (millsCurvature_mono hu hT0 hJ hJhi).trans hg

end Submission.Obl.Entropy__first_chaos_absorption
