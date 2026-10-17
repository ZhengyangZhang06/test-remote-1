import Submission.Lib.EntropyTools.Remainder

namespace Submission.Obl.Entropy__first_chaos_absorption

open Submission.Lib.EntropyTools

noncomputable def minorantSlope (u : ℝ) : ℝ := u * Real.sqrt u / 2
noncomputable def minorantLoss (u : ℝ) : ℝ := u^3 / (16*(23/50-u))

lemma minorantLoss_pos {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13/100) :
    0 < minorantLoss u := by
  unfold minorantLoss
  apply div_pos (pow_pos hu _)
  nlinarith

lemma quadratic_minorant {p : ℝ → ℝ}
    (hpneg : ∀ a, a ≤ 0 → 1/(7+a^2) ≤ p a)
    (hpmid : ∀ a, 0 ≤ a → (1/4 : ℝ) ≤ p a)
    (hphi : ∀ a, 4 ≤ a → (23/50 : ℝ) ≤ p a)
    {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13/100) (a : ℝ) :
    u + minorantSlope u * a - minorantLoss u * a^2 ≤ p a := by
  have hs := Real.sqrt_nonneg u
  have hss := Real.sq_sqrt hu.le
  have hn : 0 ≤ minorantSlope u := by unfold minorantSlope; positivity
  have hd := minorantLoss_pos hu hu'
  by_cases ha : a ≤ 0
  · let x := -Real.sqrt u * a
    have hx : 0 ≤ x := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hs) ha
    have hx2 : x^2 = u*a^2 := by dsimp [x]; rw [mul_pow, neg_sq, hss]
    have hnform : u + minorantSlope u * a = u*(1-x/2) := by
      dsimp [minorantSlope, x]
      ring
    by_cases hxhi : 2 ≤ x
    · have hnon : u + minorantSlope u * a - minorantLoss u * a^2 ≤ 0 := by
        rw [hnform]
        exact sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith))
          (mul_nonneg hd.le (sq_nonneg a)))
      exact le_trans hnon (le_trans (by positivity) (hpneg a ha))
    · have hxlo : x ≤ 2 := le_of_not_ge hxhi
      have hpoly : (1-x/2)*(x^2+7*u) ≤ 1 := by
        have h1 := mul_nonneg hx (sq_nonneg (x-1))
        have h2 := mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hxlo)
        nlinarith
      have hbound : u + minorantSlope u*a ≤ 1/(7+a^2) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 7+a^2)).2
        rw [hnform]
        calc
          u*(1-x/2)*(7+a^2) = (1-x/2)*(x^2+7*u) := by rw [hx2]; ring
          _ ≤ 1 := hpoly
      exact le_trans (sub_le_self _ (mul_nonneg hd.le (sq_nonneg a))) (hbound.trans (hpneg a ha))
  · have ha0 : 0 ≤ a := le_of_not_ge ha
    by_cases ha4 : a ≤ 4
    · have hsbound : Real.sqrt u ≤ 37/100 := by nlinarith
      have hncap : minorantSlope u ≤ (13/100 : ℝ)*(37/100)/2 := by
        unfold minorantSlope
        gcongr
      calc
        _ ≤ u + minorantSlope u*a := sub_le_self _ (mul_nonneg hd.le (sq_nonneg a))
        _ ≤ (13/100 : ℝ) + ((13/100)*(37/100)/2)*4 := by gcongr
        _ ≤ 1/4 := by norm_num
        _ ≤ p a := hpmid a ha0
    · have hden : (0 : ℝ) < 23/50-u := by linarith
      have hn2 : (minorantSlope u)^2 = 4*minorantLoss u*(23/50-u) := by
        have hnSq : (minorantSlope u)^2 = u^3/4 := by
          unfold minorantSlope
          rw [div_pow, mul_pow, hss]
          ring
        have hddef : minorantLoss u * (16*(23/50-u)) = u^3 :=
          div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hden))
        nlinarith only [hnSq, hddef]
      have hbound : u + minorantSlope u*a - minorantLoss u*a^2 ≤ 23/50 := by
        apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 4*minorantLoss u by positivity)).mp
        nlinarith [sq_nonneg (2*minorantLoss u*a-minorantSlope u)]
      exact hbound.trans (hphi a (le_of_not_ge ha4))

lemma rigidityCutoff_le (z : ℝ) : rigidityCutoff z ≤ 13/100 := by
  unfold rigidityCutoff
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma rigidityCutoff_square {z : ℝ} (hz : 0 ≤ z) :
    z * (rigidityCutoff z)^2 ≤ (32/25 : ℝ)^2 := by
  by_cases hz0 : z = 0
  · norm_num [hz0]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hspos := Real.sqrt_pos.mpr hzpos
    have hu : rigidityCutoff z ≤ 32/(25*Real.sqrt z) := by
      simp only [rigidityCutoff, if_neg hz0]
      exact min_le_right _ _
    have hprod : Real.sqrt z * rigidityCutoff z ≤ 32/25 := by
      have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 25) hspos)).mp hu
      nlinarith
    have hsq := sq_le_sq₀ (mul_nonneg hspos.le (rigidityCutoff_pos hz).le) (by norm_num : (0 : ℝ) ≤ 32/25) |>.2 hprod
    rw [mul_pow, Real.sq_sqrt hz] at hsq
    exact hsq

lemma minorantLoss_mul_parameter {z : ℝ} (hz : 0 ≤ z) :
    minorantLoss (rigidityCutoff z) * z ≤ (311/1000)*rigidityCutoff z := by
  let u := rigidityCutoff z
  have hu : 0 < u := rigidityCutoff_pos hz
  have hu' : u ≤ 13/100 := rigidityCutoff_le z
  have hden : 0 < 16*(23/50-u) := by nlinarith
  have hsq : z*u^2 ≤ (32/25 : ℝ)^2 := rigidityCutoff_square hz
  have hmul := mul_le_mul_of_nonneg_left hsq hu.le
  change (u^3/(16*(23/50-u)))*z ≤ (311/1000)*u
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu')]

lemma minorantLoss_le {u : ℝ} (hu : 0 < u) (hu' : u ≤ 13/100) :
    minorantLoss u ≤ 1/1000 := by
  have hden : 0 < 16*(23/50-u) := by nlinarith
  have hcube : u^3 ≤ (13/100 : ℝ)^3 := by gcongr
  unfold minorantLoss
  apply (div_le_iff₀ hden).2
  nlinarith

noncomputable def absorptionH (z : ℝ) : ℝ := 3*(z-1)^2/(37+3*z)
noncomputable def absorptionRho (z : ℝ) : ℝ := 3/20+(49/100)*(37/(37+3*z))

lemma absorptionH_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ absorptionH z := by
  unfold absorptionH
  positivity

lemma absorptionRho_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ absorptionRho z := by
  unfold absorptionRho
  positivity

lemma absorptionRho_le {z : ℝ} (hz : 0 ≤ z) : absorptionRho z ≤ 16/25 := by
  have hden : 0 < 37+3*z := by positivity
  have hfrac : 37/(37+3*z) ≤ (1 : ℝ) := (div_le_one hden).2 (by linarith)
  unfold absorptionRho
  nlinarith

lemma absorptionH_le_parameter {z : ℝ} (hz : 1 ≤ z) : absorptionH z ≤ z := by
  unfold absorptionH
  apply (div_le_iff₀ (by linarith : 0 < 37+3*z)).2
  nlinarith

lemma absorptionH_le_small {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    absorptionH z ≤ 3/37 := by
  unfold absorptionH
  apply (div_le_iff₀ (by positivity : 0 < 37+3*z)).2
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hz')]

lemma weighted_minorantLoss_le {z : ℝ} (hz : 0 ≤ z) :
    absorptionH z * absorptionRho z * minorantLoss (rigidityCutoff z) ≤ 27/1000 := by
  have hu := rigidityCutoff_pos hz
  have hu' := rigidityCutoff_le z
  have hd := minorantLoss_pos hu hu'
  have hH := absorptionH_nonneg hz
  have hR := absorptionRho_nonneg hz
  have hRc := absorptionRho_le hz
  by_cases hz1 : 1 ≤ z
  · have hHc := absorptionH_le_parameter hz1
    have hdz := minorantLoss_mul_parameter hz
    calc
      _ ≤ z * (16/25) * minorantLoss (rigidityCutoff z) := by gcongr
      _ = (16/25) * (minorantLoss (rigidityCutoff z)*z) := by ring
      _ ≤ (16/25) * ((311/1000)*rigidityCutoff z) := by gcongr
      _ ≤ (16/25 : ℝ) * ((311/1000)*(13/100)) := by gcongr
      _ ≤ 27/1000 := by norm_num
  · have hHc := absorptionH_le_small hz (le_of_not_ge hz1)
    have hdc := minorantLoss_le hu hu'
    calc
      _ ≤ (3/37 : ℝ) * (16/25) * (1/1000) := by gcongr
      _ ≤ 27/1000 := by norm_num

end Submission.Obl.Entropy__first_chaos_absorption
