import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Increment

open Set MeasureTheory
open scoped ContDiff

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.GaussianTransport Submission.Lib.PairEstimate

lemma dd_integral {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) {a c : ℝ} (hac : a < c) :
    dd v c a = ∫ t in (0:ℝ)..1, deriv v (a+(c-a)*t) := by
  rw [intervalIntegral.integral_comp_add_mul (deriv v) (sub_pos.mpr hac).ne']
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hv.differentiable (by simp) x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hv).2.continuous.intervalIntegrable a c)]
  simp [dd, hac.ne', smul_eq_mul, div_eq_inv_mul]

lemma incVec_integral (j : ℝ) {x y w : ℝ → ℝ}
    (hx : Continuous x) (hy : Continuous y) (hw : Continuous w) :
    (∫ t in (0:ℝ)..1, incVec j (x t) (y t) (w t)) =
      incVec j (∫ t in (0:ℝ)..1, x t) (∫ t in (0:ℝ)..1, y t) (∫ t in (0:ℝ)..1, w t) := by
  have hx' := hx.smul (continuous_const (y := baseX j))
  have hy' := hy.smul (continuous_const (y := baseY j))
  have hw' := hw.smul (continuous_const (y := baseW j))
  simp only [incVec]
  rw [intervalIntegral.integral_add (f := fun t => x t • baseX j+y t • baseY j)
      (g := fun t => w t • baseW j) ((hx'.add hy').intervalIntegrable 0 1)
      (hw'.intervalIntegrable 0 1),
    intervalIntegral.integral_add (f := fun t => x t • baseX j) (g := fun t => y t • baseY j)
      (hx'.intervalIntegrable 0 1) (hy'.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_smul_const]

lemma integral_J {a c : ℝ} (j : ℝ) (hac : a < c) :
    (∫ t in (0:ℝ)..1, J j (a+(c-a)*t)) =
      incVec j (dd k c a) (dd b c a)
        (dd f c a-2*b j*dd k c a-(80/3)*l j*dd b c a) := by
  have hb : Continuous (fun t => b (a+(c-a)*t)) := smooth_b.continuous.comp (by fun_prop)
  have hl : Continuous (fun t => l (a+(c-a)*t)) := smooth_l.continuous.comp (by fun_prop)
  have hf : Continuous (fun t => deriv f (a+(c-a)*t)) :=
    (contDiff_infty_iff_deriv.mp smooth_f).2.continuous.comp (by fun_prop)
  change (∫ t in (0:ℝ)..1, incVec j _ _ _) = _
  rw [incVec_integral j hb hl (by fun_prop)]
  have hbi : (∫ t in (0:ℝ)..1, b (a+(c-a)*t)) = dd k c a := (dd_integral smooth_k hac).symm
  have hli : (∫ t in (0:ℝ)..1, l (a+(c-a)*t)) = dd b c a := (dd_integral smooth_b hac).symm
  rw [hbi, hli]
  congr 1
  rw [intervalIntegral.integral_sub (f := fun t => deriv f (a+(c-a)*t)-2*b j*b (a+(c-a)*t))
      (g := fun t => (80/3)*l j*l (a+(c-a)*t))
      ((hf.sub (hb.const_mul _)).intervalIntegrable 0 1) ((hl.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_sub (f := fun t => deriv f (a+(c-a)*t))
      (g := fun t => 2*b j*b (a+(c-a)*t)) (hf.intervalIntegrable 0 1)
      ((hb.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hbi, hli, ← dd_integral smooth_f hac]

lemma increment_integral {a c : ℝ} (hac : a < c) (j : ℝ) :
    (∫ t in (0:ℝ)..1, J j (a+(c-a)*t)-J j j) =
      incVec j (dd k c a-b j) (dd b c a-l j)
        (dd f c a-deriv f j-2*b j*(dd k c a-b j)-(80/3)*l j*(dd b c a-l j)) := by
  rw [intervalIntegral.integral_sub
    (f := fun t => J j (a+(c-a)*t)) (g := fun _ => J j j)
    (((continuous_J j).comp (by fun_prop)).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1), integral_J j hac]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  rw [J, ← incVec_sub]
  congr 1
  ring

lemma secant_norm_lower {a c C : ℝ} (hac : a < c)
    (hbound : ∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤ C*(logq x-logq a)) :
    ‖incVec a (dk c a) (db c a) (psi c a)‖ ≤ C*(meanLog a c-logq a) := by
  dsimp only [psi, dk, db]
  rw [← increment_integral hac a]
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖J a (a+(c-a)*t)-J a a‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0:ℝ)..1, C*(logq (a+(c-a)*t)-logq a) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable
        exact (((continuous_J a).comp (by fun_prop)).sub continuous_const).norm
      · apply Continuous.intervalIntegrable
        exact continuous_const.mul ((smooth_logq.continuous.comp (by fun_prop)).sub continuous_const)
      · intro t ht
        exact hbound _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        (f := fun t => logq (a+(c-a)*t)) (g := fun _ => logq a)
        ((smooth_logq.continuous.comp (by fun_prop)).intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1)]
      simp [meanLog]

lemma secant_norm_upper {a c C : ℝ} (hac : a < c)
    (hbound : ∀ x ∈ Icc a c, ‖J c x-J c c‖ ≤ C*(logq c-logq x)) :
    ‖incVec c (dk a c) (db a c) (psi a c)‖ ≤ C*(logq c-meanLog a c) := by
  have he : incVec c (dk a c) (db a c) (psi a c) =
      ∫ t in (0:ℝ)..1, J c (a+(c-a)*t)-J c c := by
    rw [increment_integral hac c]
    simp only [dk, db, psi, dd_symm k a c, dd_symm b a c, dd_symm f a c]
  rw [he]
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖J c (a+(c-a)*t)-J c c‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0:ℝ)..1, C*(logq c-logq (a+(c-a)*t)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable
        exact (((continuous_J c).comp (by fun_prop)).sub continuous_const).norm
      · apply Continuous.intervalIntegrable
        exact continuous_const.mul (continuous_const.sub (smooth_logq.continuous.comp (by fun_prop)))
      · intro t ht
        exact hbound _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        (f := fun _ => logq c) (g := fun t => logq (a+(c-a)*t))
        (continuous_const.intervalIntegrable 0 1)
        ((smooth_logq.continuous.comp (by fun_prop)).intervalIntegrable 0 1)]
      simp [meanLog]

lemma pair_of_partial_bounds {a c Pm Pp : ℝ} (hac : a < c)
    (hca : Certificate a) (hcc : Certificate c) (hPm : 0 ≤ Pm) (hPp : 0 ≤ Pp)
    (hm : ∀ x ∈ Icc a c, ‖J a x-J a a‖ ≤ Real.sqrt Pm*(logq x-logq a))
    (hp : ∀ x ∈ Icc a c, ‖J c x-J c c‖ ≤ Real.sqrt Pp*(logq c-logq x))
    (ht : max Pm ((Pm+Pp)/2) ≤ threshold (m0 a) (delta c a))
    (G g Z : ℝ) :
    (H a c G g Z+H c a G g Z)/2 ≤ Q G (g-G/2)+sigma a c*Z^2 := by
  have hm' := secant_norm_lower hac hm
  have hp' := secant_norm_upper hac hp
  have hd : delta c a ≠ 0 := (sub_pos.mpr (strictMono_logq hac)).ne'
  have hmeq : meanLog a c-logq a = delta c a*lowerMean a c := by
    dsimp only [lowerMean]; field_simp
  have hpeq : logq c-meanLog a c = delta c a*(1-lowerMean a c) := by
    rw [mul_sub, mul_one, ← hmeq]; unfold delta; ring
  rw [hmeq] at hm'
  rw [hpeq] at hp'
  have hs_m := sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) hm') |>.mpr hm'
  have hs_p := sq_le_sq₀ (norm_nonneg _) (by
    exact le_trans (norm_nonneg _) hp') |>.mpr hp'
  rw [norm_incVec_sq _ _ _ _ hca.1, mul_pow, Real.sq_sqrt hPm, mul_pow] at hs_m
  rw [norm_incVec_sq _ _ _ _ hcc.1, mul_pow, Real.sq_sqrt hPp, mul_pow] at hs_p
  obtain ⟨hu, hum, hmean⟩ := mean_distance_bound hac
  have hCm := (endpoint_le c a G g Z hca).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs_m (sq_nonneg Z)))
  have hCp := (endpoint_le a c G g Z hcc).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs_p (sq_nonneg Z)))
  have h := pair_cost_bound (Q G (g-G/2)) (H c a G g Z) (H a c G g Z)
    Z (delta c a) (m0 a) Pm Pp (lowerMean a c) (1-lowerMean a c)
    (m0_nonneg a) hu hum hmean
    (by nlinarith only [hCm]) (by nlinarith only [hCp]) ht
  dsimp only [sigma]
  rw [min_eq_left hac.le]
  have he : (delta a c)^2=(delta c a)^2 := by unfold delta; ring
  have he4 : (delta a c)^4=(delta c a)^4 := by unfold delta; ring
  rw [he, he4]
  nlinarith only [h]

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
