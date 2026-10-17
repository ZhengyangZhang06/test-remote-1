import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Data
import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.Mollifier

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Metric Set ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

open Submission.Obl.Entropy__continuous_jacobian_of_l2_limit (mollify mollify_hasFDerivAt)

variable {m : ℕ}

noncomputable def smallBump (n : ℕ) : ContDiffBump (0 : E m) where
  rIn := (1/((n:ℝ)+1))/2
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hh : 0 < 1/((n:ℝ)+1) := by positivity
    linarith

lemma smallBump_tendsto : Tendsto (fun n => (smallBump (m:=m) n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma mollify_norm_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (φ : ContDiffBump (0 : E m)) {z : E m → V} {C : ℝ} (hC : ∀ x, ‖z x‖ ≤ C) (x : E m) :
    ‖mollify φ z x‖ ≤ C := by
  change ‖∫ t, φ.normed volume t • z (x-t)‖ ≤ C
  calc
    _ ≤ ∫ t, φ.normed volume t*C := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const C)
      apply ae_of_all
      intro t
      rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg_normed t)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma compact_c1_smooth_approx {z : E m → ℝ} (hz : ContDiff ℝ 1 z) (hzc : HasCompactSupport z) :
    ∃ zs : ℕ → E m → ℝ, (∀ n, ContDiff ℝ ∞ (zs n)) ∧ (∀ n, HasCompactSupport (zs n)) ∧
      (∃ C D : ℝ, (∀ n x, ‖zs n x‖ ≤ C) ∧ (∀ n x, ‖fderiv ℝ (zs n) x‖ ≤ D)) ∧
      (∀ x, Tendsto (fun n => zs n x) atTop (𝓝 (z x))) ∧
      (∀ x, Tendsto (fun n => fderiv ℝ (zs n) x) atTop (𝓝 (fderiv ℝ z x))) := by
  let zs (n : ℕ) := mollify (smallBump n) z
  have hs (n) : ContDiff ℝ ∞ (zs n) :=
    (smallBump n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (smallBump n).contDiff_normed hz.continuous.locallyIntegrable
  have hsc (n) : HasCompactSupport (zs n) :=
    (smallBump n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hzc
  have hder (n x) : fderiv ℝ (zs n) x = mollify (smallBump n) (fderiv ℝ z) x :=
    (mollify_hasFDerivAt (smallBump n) hz x).fderiv
  refine ⟨zs,hs,hsc,?_,?_,?_⟩
  · obtain ⟨C,hC⟩ := hzc.exists_bound_of_continuous hz.continuous
    obtain ⟨D,hD⟩ := (hzc.fderiv (𝕜:=ℝ)).exists_bound_of_continuous (hz.continuous_fderiv one_ne_zero)
    refine ⟨C,D,fun n x => mollify_norm_bound _ hC x,?_⟩
    intro n x
    rw [hder]
    exact mollify_norm_bound _ hD x
  · intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous smallBump_tendsto hz.continuous x
  · intro x
    simp_rw [hder]
    exact ContDiffBump.convolution_tendsto_right_of_continuous smallBump_tendsto
      (hz.continuous_fderiv one_ne_zero) x

lemma weak_test_compact_c1 {μ : Measure (E m)} {q : E m → ℝ} {g : Fin m → E m → ℝ}
    (hq : Integrable q μ) (hg : ∀ r, Integrable (g r) μ)
    (hw : ∀ z : E m → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, q x*z x ∂μ) = ∑ r, ∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ)
    {z : E m → ℝ} (hz : ContDiff ℝ 1 z) (hzc : HasCompactSupport z) :
    (∫ x, q x*z x ∂μ) = ∑ r, ∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ := by
  obtain ⟨zs,hs,hsc,⟨C,D,hC,hD⟩,hv,hd⟩ := compact_c1_smooth_approx hz hzc
  have hlim : Tendsto (fun n => ∫ x, q x*zs n x ∂μ) atTop (𝓝 (∫ x, q x*z x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖q x‖*C)
      (fun n => hq.aestronglyMeasurable.mul (hs n).continuous.aestronglyMeasurable)
      (hq.norm.mul_const C)
      (fun n => ae_of_all _ fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC n x) (norm_nonneg _))
      (ae_of_all _ fun x => tendsto_const_nhds.mul (hv x))
  have hlimd (r : Fin m) : Tendsto (fun n => ∫ x, g r x*fderiv ℝ (zs n) x (PiLp.single 2 r (1:ℝ)) ∂μ)
      atTop (𝓝 (∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ)) := by
    let e : E m := PiLp.single 2 r (1:ℝ)
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g r x‖*(D*‖e‖))
      (fun n => (hg r).aestronglyMeasurable.mul
        (((hs n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
      ((hg r).norm.mul_const _) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => tendsto_const_nhds.mul ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto _ |>.comp (hd x)))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact ((fderiv ℝ (zs n) x).le_opNorm e).trans (mul_le_mul_of_nonneg_right (hD n x) (norm_nonneg e))
  have he (n) := hw (zs n) (hs n) (hsc n)
  exact tendsto_nhds_unique hlim ((tendsto_finsetSum _ fun r _ => hlimd r).congr (fun n => (he n).symm))

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
