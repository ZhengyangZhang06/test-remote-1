import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Basic

open Set MeasureTheory

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.GaussianTransport

private lemma nonneg_of_nonneg_derivative {F F' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt F (F' x) x) (h0 : 0 ≤ F 0)
    (hp : ∀ x, 0 ≤ x → 0 ≤ F' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F x := by
  have hm : MonotoneOn F (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hp x ((interior_subset hx) : 0 ≤ x))
  exact h0.trans (hm (by simp) hx hx)

/-- The elementary exponential comparison behind the sharp logarithmic mean estimate. -/
lemma exp_mean_polynomial {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x^2-6*x+12)*Real.exp x - (x^2+6*x+12) := by
  have h2 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x^2-2*x+2)*Real.exp x-2 := by
    apply nonneg_of_nonneg_derivative
      (F' := fun y => y^2*Real.exp y) _ (by norm_num) (fun y _ => by positivity) hx
    intro y
    convert! (((((hasDerivAt_id y).pow 2).sub ((hasDerivAt_id y).const_mul 2)).add_const 2).mul
      (Real.hasDerivAt_exp y)).sub_const 2 using 1 <;> dsimp <;> ring
  have h1 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x^2-4*x+6)*Real.exp x-2*x-6 := by
    apply nonneg_of_nonneg_derivative
      (F' := fun y => (y^2-2*y+2)*Real.exp y-2) _ (by norm_num) h2 hx
    intro y
    convert! ((((((hasDerivAt_id y).pow 2).sub ((hasDerivAt_id y).const_mul 4)).add_const 6).mul
      (Real.hasDerivAt_exp y)).sub ((hasDerivAt_id y).const_mul 2)).sub_const 6
      using 1 <;> dsimp <;> ring
  apply nonneg_of_nonneg_derivative
    (F' := fun y => (y^2-4*y+6)*Real.exp y-2*y-6) _ (by norm_num) h1 hx
  intro y
  convert! (((((hasDerivAt_id y).pow 2).sub ((hasDerivAt_id y).const_mul 6)).add_const 12).mul
    (Real.hasDerivAt_exp y)).sub
    ((((hasDerivAt_id y).pow 2).add ((hasDerivAt_id y).const_mul 6)).add_const 12)
    using 1 <;> dsimp <;> ring

lemma integral_log_chord_le {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (∫ t in (0:ℝ)..1, Real.log (x+(y-x)*t)) ≤
      Real.log x + (Real.log y-Real.log x)/2 + (Real.log y-Real.log x)^2/12 := by
  have hy : 0 < y := hx.trans hxy
  have hd : 0 < y-x := sub_pos.mpr hxy
  have hint := intervalIntegral.integral_comp_add_mul Real.log hd.ne' x (a := 0) (b := 1)
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul, integral_log] at hint
  rw [hint, ← div_eq_inv_mul]
  have hδ : 0 ≤ Real.log y-Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy.le)
  have he := exp_mean_polynomial hδ
  rw [Real.exp_sub, Real.exp_log hx, Real.exp_log hy] at he
  have he' := mul_nonneg hx.le he
  field_simp at he'
  rw [div_le_iff₀ hd]
  nlinarith only [he']

noncomputable def meanLog (a c : ℝ) := ∫ t in (0:ℝ)..1, logq (a+(c-a)*t)
noncomputable def lowerMean (a c : ℝ) := (meanLog a c-logq a)/(delta c a)

lemma logq_chord_lower {a c t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    logq a+(logq c-logq a)*t ≤ logq (a+(c-a)*t) := by
  have h := concaveOn_logq.2 (mem_univ a) (mem_univ c)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at h
  convert! h using 1
  · ring
  · congr 1; ring

lemma logq_chord_upper {a c t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    logq (a+(c-a)*t) ≤ Real.log (q a+(q c-q a)*t) := by
  have h := convexOn_gaussianHazard.2 (mem_univ a) (mem_univ c)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at h
  have h' : q (a+(c-a)*t) ≤ q a+(q c-q a)*t := by
    convert! h using 1
    · congr 1; ring
    · ring
  exact Real.log_le_log (gaussianHazard_pos _) h'

lemma meanLog_lower (a c : ℝ) :
    logq a+(logq c-logq a)/2 ≤ meanLog a c := by
  have h := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (μ := volume) (by norm_num)
    (f := fun t => logq a+(logq c-logq a)*t)
    (g := fun t => logq (a+(c-a)*t))
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; exact smooth_logq.continuous.comp (by fun_prop))
    (fun t ht => logq_chord_lower ht)
  rw [intervalIntegral.integral_add
    (f := fun _ => logq a) (g := fun t => (logq c-logq a)*t)
    (continuous_const.intervalIntegrable 0 1)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_id] at h
  simpa [meanLog, div_eq_mul_inv] using h

lemma meanLog_upper {a c : ℝ} (hac : a < c) :
    meanLog a c ≤ logq a+(logq c-logq a)/2+(logq c-logq a)^2/12 := by
  have hpos (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) : 0 < q a+(q c-q a)*t := by
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
    have h := (strictMono_gaussianHazard hac).le
    nlinarith [gaussianHazard_pos a, mul_nonneg (sub_nonneg.mpr h) ht'.1]
  have hi : IntervalIntegrable (fun t => Real.log (q a+(q c-q a)*t)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (ContinuousOn.log (by fun_prop) (fun t ht => (hpos t ht).ne'))
  have h := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (μ := volume) (by norm_num)
    (f := fun t => logq (a+(c-a)*t))
    (g := fun t => Real.log (q a+(q c-q a)*t))
    (by apply Continuous.intervalIntegrable; exact smooth_logq.continuous.comp (by fun_prop)) hi
    (fun t ht => logq_chord_upper ht)
  exact h.trans (integral_log_chord_le (gaussianHazard_pos a) (strictMono_gaussianHazard hac))

lemma lowerMean_bounds {a c : ℝ} (hac : a < c) :
    1/2 ≤ lowerMean a c ∧ lowerMean a c ≤ 1/2+delta c a/12 ∧ lowerMean a c ≤ 1 := by
  have hd : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  have hlo := meanLog_lower a c
  have hhi := meanLog_upper hac
  have hm : meanLog a c ≤ logq c := by
    have h := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (μ := volume) (by norm_num)
      (f := fun t => logq (a+(c-a)*t)) (g := fun _ => logq c)
      (by apply Continuous.intervalIntegrable; exact smooth_logq.continuous.comp (by fun_prop))
      (continuous_const.intervalIntegrable 0 1) (fun t ht => strictMono_logq.monotone (by nlinarith [ht.2]))
    simpa [meanLog] using h
  dsimp only [lowerMean]
  constructor
  · rw [le_div_iff₀ hd]; dsimp only [delta]; linarith
  constructor
  · rw [div_le_iff₀ hd]; dsimp only [delta]; nlinarith only [hhi]
  · rw [div_le_one hd]; dsimp only [delta]; linarith

lemma mean_distance_bound {a c : ℝ} (hac : a < c) :
    0 ≤ 1-lowerMean a c ∧ 1-lowerMean a c ≤ lowerMean a c ∧
    (lowerMean a c)^2+(1-lowerMean a c)^2 ≤ (1/2)*(1+(delta c a)^2/36) := by
  obtain ⟨hl, hu, h1⟩ := lowerMean_bounds hac
  have hd : 0 < delta c a := sub_pos.mpr (strictMono_logq hac)
  refine ⟨by linarith, by linarith, ?_⟩
  have hsq := mul_nonneg (show 0 ≤ delta c a/12-(lowerMean a c-1/2) by linarith)
    (show 0 ≤ delta c a/12+(lowerMean a c-1/2) by linarith)
  nlinarith only [hsq]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
