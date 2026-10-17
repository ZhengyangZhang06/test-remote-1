import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.Representative
import Submission.Obl.Entropy__mollified_convex_sequence.Convolution

open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped Topology Convolution

namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace Y]
local notation "E" => EuclideanSpace ℝ (Fin m)

noncomputable def mollify (φ : ContDiffBump (0 : E)) (f : E → Y) : E → Y :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

/-- Approximate identities converge locally uniformly on continuous functions. -/
lemma mollify_tendstoLocallyUniformly {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {f : E → Y} (hf : Continuous f) :
    TendstoLocallyUniformly (fun n => mollify (φ n) f) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have h : Tendsto (fun p : ℕ × E => mollify (φ p.1) f p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hf.aestronglyMeasurable)
      ((hf.tendsto x).comp tendsto_snd) tendsto_snd
  exact (((hf.tendsto x).comp tendsto_snd).prodMk_nhds h).mono_right
    (nhds_le_uniformity _)

/-- Differentiation of a compactly supported convolution of a C1 function. -/
lemma mollify_hasFDerivAt (φ : ContDiffBump (0 : E)) {f : E → Y}
    (hf : ContDiff ℝ 1 f) (x₀ : E) :
    HasFDerivAt (mollify φ f) (mollify φ (fderiv ℝ f) x₀) x₀ := by
  have hc := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ (1 + φ.rOut)).exists_bound_of_continuousOn
    hc.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x₀ 1) (F' := fun x y => φ.normed volume y • fderiv ℝ f (x-y))
    (bound := fun y => φ.normed volume y * C) (ball_mem_nhds _ zero_lt_one)
  · exact Eventually.of_forall fun x =>
      (Submission.Obl.Entropy__mollified_convex_sequence.bump_smul_integrable φ (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact Submission.Obl.Entropy__mollified_convex_sequence.bump_smul_integrable φ (hf.continuous.comp (continuous_const.sub continuous_id))
  · exact (Submission.Obl.Entropy__mollified_convex_sequence.bump_smul_integrable φ (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y x hx
    by_cases hy : φ.normed volume y = 0
    · simp [hy]
    have hyr : ‖y‖ ≤ φ.rOut := by
      have hy' : y ∈ Function.support (φ.normed volume) := hy
      rw [φ.support_normed_eq] at hy'
      exact (mem_ball_zero_iff.mp hy').le
    have hxy : x - y ∈ closedBall x₀ (1 + φ.rOut) := by
      rw [mem_closedBall, dist_eq_norm]
      calc
        ‖x - y - x₀‖ = ‖(x - x₀) - y‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 1 + φ.rOut := add_le_add (mem_ball_iff_norm.mp hx).le hyr
    rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)]
    exact mul_le_mul_of_nonneg_left (hC _ hxy) (φ.nonneg_normed y)
  · exact φ.integrable_normed.mul_const C
  · apply Eventually.of_forall
    intro y x _
    simpa [Function.comp_def, Pi.smul_def, Pi.sub_apply] using (((hf.differentiable one_ne_zero) (x-y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub (hasFDerivAt_const y x))).const_smul (φ.normed volume y)

end Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
