import Submission.Obl.Entropy__gaussian_chaos_resolvent.Coefficients

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

theorem sum_resolvent_inner_eq {m : ℕ} (f z : GaussianL2 m) (D E : Fin m → GaussianL2 m)
    (hf0 : gaussianCoeff f 0 = 0)
    (hD : ∀ r a, gaussianCoeff (D r) a =
      Real.sqrt (a r + 1 : ℝ) * gaussianCoeff f (raiseIndex a r))
    (hE : ∀ r a, gaussianCoeff (E r) a =
      Real.sqrt (a r + 1 : ℝ) * gaussianCoeff z (raiseIndex a r)) :
    (∑ r, inner ℝ (resolventComponent (D r)) (E r)) = inner ℝ f z := by
  let F := fun a => gaussianCoeff f a * gaussianCoeff z a / (chaosDegree a : ℝ)
  have hterm (r : Fin m) (a : Fin m → ℕ) :
      gaussianCoeff (resolventComponent (D r)) a * gaussianCoeff (E r) a =
        (a r + 1 : ℝ) * F (raiseIndex a r) := by
    rw [gaussianCoeff_resolventComponent, hD, hE]
    dsimp only [F]
    rw [chaosDegree_raiseIndex, Nat.cast_add, Nat.cast_one]
    calc
      _ = (Real.sqrt (a r + 1 : ℝ))^2 *
          (gaussianCoeff f (raiseIndex a r) * gaussianCoeff z (raiseIndex a r)) /
            (chaosDegree a + 1 : ℝ) := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring
  have hs (r : Fin m) : Summable (fun a => (a r : ℝ) * F a) := by
    apply (summable_raiseIndex_iff r F).mp
    exact (summable_gaussianCoeff_mul (resolventComponent (D r)) (E r)).congr (hterm r)
  have hr (r : Fin m) : inner ℝ (resolventComponent (D r)) (E r) =
      ∑' a, (a r : ℝ) * F a := by
    rw [← tsum_gaussianCoeff_mul]
    simp_rw [hterm]
    exact tsum_raiseIndex r F
  simp_rw [hr]
  rw [← Summable.tsum_finsetSum (fun r _ => hs r)]
  calc
    _ = ∑' a, gaussianCoeff f a * gaussianCoeff z a := by
      apply tsum_congr
      intro a
      rw [← Finset.sum_mul]
      have hd : (∑ r, (a r : ℝ)) = chaosDegree a := by simp [chaosDegree]
      rw [hd]
      by_cases ha : a = 0
      · subst a
        simp [F, hf0]
      · have hdeg : (chaosDegree a : ℝ) ≠ 0 := by
          exact_mod_cast mt (chaosDegree_eq_zero a).mp ha
        dsimp only [F]
        field_simp
    _ = _ := tsum_gaussianCoeff_mul f z

theorem resolvent_inner_le {m : ℕ} (D : GaussianL2 m) (hD0 : gaussianCoeff D 0 = 0) :
    inner ℝ (resolventComponent D) D ≤ (1/2 : ℝ) * ‖D‖^2 := by
  rw [← tsum_gaussianCoeff_mul, ← tsum_gaussianCoeff_sq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_gaussianCoeff_mul _ _)
    ((summable_gaussianCoeff_sq D).mul_left _)
  intro a
  rw [gaussianCoeff_resolventComponent]
  by_cases ha : a = 0
  · subst a
    simp [hD0]
  · have hdeg : 1 ≤ chaosDegree a := by
      have : chaosDegree a ≠ 0 := mt (chaosDegree_eq_zero a).mp ha
      omega
    have hden : (2:ℝ) ≤ chaosDegree a + 1 := by exact_mod_cast Nat.succ_le_succ hdeg
    have hpos : (0:ℝ) < chaosDegree a + 1 := by positivity
    rw [div_mul_eq_mul_div, ← pow_two]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg (sq_nonneg (gaussianCoeff D a)) (sub_nonneg.mpr hden)]

theorem resolvent_norm_sq_le {m : ℕ} (D : GaussianL2 m) (hD0 : gaussianCoeff D 0 = 0) :
    ‖resolventComponent D‖^2 ≤ (1/2 : ℝ) * inner ℝ (resolventComponent D) D := by
  rw [← tsum_gaussianCoeff_sq, ← tsum_gaussianCoeff_mul, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_gaussianCoeff_sq _)
    ((summable_gaussianCoeff_mul _ _).mul_left _)
  intro a
  rw [gaussianCoeff_resolventComponent]
  by_cases ha : a = 0
  · subst a
    simp [hD0]
  · have hdeg : 1 ≤ chaosDegree a := by
      have : chaosDegree a ≠ 0 := mt (chaosDegree_eq_zero a).mp ha
      omega
    have hden : (2:ℝ) ≤ chaosDegree a + 1 := by exact_mod_cast Nat.succ_le_succ hdeg
    have hpos : (0:ℝ) < chaosDegree a + 1 := by positivity
    have hh := mul_le_mul_of_nonneg_left hden (sq_nonneg (gaussianCoeff D a / (chaosDegree a + 1 : ℝ)))
    field_simp at hh ⊢
    nlinarith

end Submission.Obl.Entropy__gaussian_chaos_resolvent
