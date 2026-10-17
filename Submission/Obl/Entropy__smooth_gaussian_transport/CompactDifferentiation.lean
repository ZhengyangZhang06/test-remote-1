import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianSmoothing

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Convolution NNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A compactly supported continuous factor permits differentiation of a
convolution with any continuously differentiable kernel. -/
theorem compact_convolution_hasFDerivAt {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E m → ℝ} {g : E m → F}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (c : E m) :
    HasFDerivAt (fun x => ∫ y, f y • g (x - y))
      (∫ y, f y • fderiv ℝ g (c - y)) c := by
  have hd := hg.continuous_fderiv one_ne_zero
  let K : Set (E m) := (fun z : E m × E m => z.1 - z.2) ''
    (Metric.closedBall c 1 ×ˢ tsupport f)
  have hK : IsCompact K := ((isCompact_closedBall c 1).prod hfc).image
    (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM, hb⟩ := (hK.image hd).isBounded.exists_pos_norm_le
  have hbound : ∀ y x, x ∈ Metric.ball c 1 →
      ‖f y • fderiv ℝ g (x - y)‖ ≤ |f y| * M := by
    intro y x hx
    by_cases hy : f y = 0
    · simp only [hy, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply hb
    exact ⟨x - y, ⟨(x, y), ⟨Metric.ball_subset_closedBall hx, subset_closure hy⟩, rfl⟩, rfl⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball c 1) (bound := fun y => |f y| * M)
    (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1))
  · filter_upwards [] with x
    exact (hf.smul (hg.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact (hf.smul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hfc.smul_right
  · exact (hf.smul (hd.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall hbound
  · exact (hf.integrable_of_hasCompactSupport hfc).norm.mul_const M
  · filter_upwards [] with y
    intro x hx
    have hdx : HasFDerivAt (fun z : E m => g (z - y)) (fderiv ℝ g (x - y)) x := by
      convert! (hg.differentiable_one (x - y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y) using 1 <;> simp
    exact hdx.const_smul (f y)

/-- Evaluation of the first derivative can be interchanged with the integral. -/
theorem compact_convolution_fderiv_apply {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E m → ℝ} {g : E m → F}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (c v : E m) :
    fderiv ℝ (fun x => ∫ y, f y • g (x - y)) c v =
      ∫ y, f y • fderiv ℝ g (c - y) v := by
  rw [(compact_convolution_hasFDerivAt hf hfc hg c).fderiv]
  have hi : Integrable (fun y => f y • fderiv ℝ g (c - y)) volume :=
    (hf.smul ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hfc.smul_right
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem compact_convolution_iteratedFDeriv {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E m → ℝ} {g : E m → F}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) (n : ℕ) (x : E m) :
    iteratedFDeriv ℝ n (fun x => ∫ y, f y • g (x - y)) x =
      ∫ y, f y • iteratedFDeriv ℝ n g (x - y) := by
  induction n generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have hh : (continuousMultilinearCurryFin0 ℝ (E m) F).symm (∫ y, f y • g (x - y)) =
        ∫ y, (continuousMultilinearCurryFin0 ℝ (E m) F).symm (f y • g (x - y)) := by
      convert! ((continuousMultilinearCurryFin0 ℝ (E m) F).symm.toLinearIsometry.integral_comp_comm
        (fun y => f y • g (x - y))).symm using 1
    rw [hh]
    apply integral_congr_ae
    filter_upwards [] with y
    exact map_smul _ _ _
  | succ n ih =>
    have he : iteratedFDeriv ℝ n (fun x => ∫ y, f y • g (x - y)) =
        fun x => ∫ y, f y • iteratedFDeriv ℝ n g (x - y) := funext ih
    have hgn : ContDiff ℝ 1 (iteratedFDeriv ℝ n g) :=
      hg.iteratedFDeriv_right (by
        exact_mod_cast (le_top : (1 + n : ENat) ≤ ⊤))
    rw [iteratedFDeriv_succ_eq_comp_left, he, Function.comp_apply,
      (compact_convolution_hasFDerivAt hf hfc hgn x).fderiv]
    have hh : (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E m) F).symm
        (∫ y, f y • fderiv ℝ (iteratedFDeriv ℝ n g) (x - y)) =
        ∫ y, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E m) F).symm
          (f y • fderiv ℝ (iteratedFDeriv ℝ n g) (x - y)) := by
      convert! (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
        (E := E m →L[ℝ] E m [×n]→L[ℝ] F) (F := E m [×(n + 1)]→L[ℝ] F)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E m) F).symm.toLinearIsometry
        (fun y => f y • fderiv ℝ (iteratedFDeriv ℝ n g) (x - y))).symm using 1
    rw [hh]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [map_smul]
    rfl

end Submission.Obl.Entropy__smooth_gaussian_transport
