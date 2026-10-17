import Submission.Obl.Entropy__smooth_gaussian_transport.ConjugateConvergence
import Submission.Obl.Entropy__smooth_gaussian_transport.Alexandrov

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Subgradient images of a fixed compact set are uniformly bounded for a
pointwise bounded family of finite convex functions. -/
theorem convex_sequence_uniform_subgradient_bound {m : ℕ} {u : ℕ → E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hb : ∀ x, Bornology.IsBounded (range (fun n => u n x)))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, ∀ x ∈ K, ∀ p, IsSubgradient (u n) x p → ‖p‖ ≤ B := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨M, hM, hbM⟩ := convex_sequence_uniform_abs_bound hu hb
    (isCompact_closedBall (0 : E m) (R + 1))
  refine ⟨2 * M, by positivity, ?_⟩
  intro n x hx p hxp
  by_cases hp : p = 0
  · simp only [hp, norm_zero]
    positivity
  have hnp : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  let e : E m := ‖p‖⁻¹ • p
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnp]
  have hxb : x ∈ Metric.closedBall (0 : E m) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [hR x hx]
  have hzb : x + e ∈ Metric.closedBall (0 : E m) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖x + e‖ ≤ ‖x‖ + ‖e‖ := norm_add_le _ _
      _ ≤ R + 1 := by rw [he]; linarith [hR x hx]
  have hip : inner ℝ p e = ‖p‖ := by
    simp only [e, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hs := hxp (x + e)
  rw [add_sub_cancel_left, hip] at hs
  linarith [(abs_le.mp (hbM n x hxb)).1, (abs_le.mp (hbM n (x + e) hzb)).2]

/-- The Monge–Ampère measures of pointwise convergent superlinear finite
convex potentials converge against every continuous compactly supported test
function. The proof uses conjugate-gradient convergence and a common compact
bound for the subgradient images of the support. -/
theorem tendsto_integral_alexandrov_of_pointwise {m : ℕ}
    {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n)) (hv : ConvexOn ℝ univ v)
    (hdu : ∀ n, conjugateDomain (u n) = univ) (hdv : conjugateDomain v = univ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {f : E m → ℝ} (hf : Continuous f) (hfK : HasCompactSupport f) :
    Tendsto (fun n => ∫ x, f x ∂alexandrovMeasure (u n)) atTop
      (𝓝 (∫ x, f x ∂alexandrovMeasure v)) := by
  have hg (w : E m → ℝ) : Measurable (gradient (finiteConjugate w)) :=
    Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _
  have hc := ae_tendsto_gradient_of_convex_pointwise
    (fun n => finiteConjugate_convex (hdu n)) (finiteConjugate_convex hdv)
    (tendsto_finiteConjugate_of_pointwise hu hv hdu hdv hlim)
  obtain ⟨B, hB, hb⟩ := convex_sequence_uniform_subgradient_bound hu
    (fun x => (hlim x).cauchySeq.isBounded_range) hfK
  obtain ⟨C, hC, hfC⟩ := (hfK.image hf).isBounded.exists_pos_norm_le
  have hfbound (x : E m) : ‖f x‖ ≤ C := by
    by_cases hx : x ∈ tsupport f
    · exact hfC _ (mem_image_of_mem _ hx)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hC.le
  let b : E m → ℝ := (Metric.closedBall (0 : E m) B).indicator (fun _ => C)
  have hbi : Integrable b volume := by
    exact (integrableOn_const (isCompact_closedBall (0 : E m) B).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have hbound (n : ℕ) : ∀ᵐ p ∂volume,
      ‖f (gradient (finiteConjugate (u n)) p)‖ ≤ b p := by
    filter_upwards [Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex
      (finiteConjugate_convex (hdu n)) volume] with p hp
    by_cases hpB : p ∈ Metric.closedBall (0 : E m) B
    · simpa only [b, indicator_of_mem hpB] using hfbound (gradient (finiteConjugate (u n)) p)
    · have hzero : f (gradient (finiteConjugate (u n)) p) = 0 := by
        by_contra hz
        have hxs : gradient (finiteConjugate (u n)) p ∈ tsupport f :=
          subset_closure hz
        have hsup : IsSubgradient (u n) (gradient (finiteConjugate (u n)) p) p :=
          (subgradient_iff_eq_conjugate_gradient (hu n).locallyLipschitz.continuous (hdu n) hp).mpr rfl
        exact hpB (by simpa only [Metric.mem_closedBall, dist_zero_right] using hb n _ hxs p hsup)
      simp only [hzero, norm_zero, b, indicator_of_notMem hpB, le_refl]
  have ht := tendsto_integral_of_dominated_convergence b
    (fun n => (hf.measurable.comp (hg (u n))).aestronglyMeasurable) hbi hbound
    (hc.mono (fun p hp => hf.continuousAt.tendsto.comp hp))
  have hmap (w : E m → ℝ) :
      (∫ x, f x ∂alexandrovMeasure w) = ∫ p, f (gradient (finiteConjugate w) p) :=
    integral_map_of_stronglyMeasurable (hg w) hf.stronglyMeasurable
  simpa only [hmap, Function.comp_def] using ht

end Submission.Obl.Entropy__smooth_gaussian_transport
