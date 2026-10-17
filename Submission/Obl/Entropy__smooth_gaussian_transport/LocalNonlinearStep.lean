import Submission.Obl.Entropy__smooth_gaussian_transport.NonlinearQuotientStep
import Submission.Obl.Entropy__smooth_gaussian_transport.FiniteSmoothExtension

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem local_nonlinear_quotient_regularization {m : ℕ} {f U : E m → ℝ}
    {R : (E m →L[ℝ] ℝ) → ℝ}
    {A : (E m [×2]→L[ℝ] ℝ) → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hH : UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 f))
    (x : E m) (hU : ContDiffAt ℝ 2 U x) (hR : ContDiffAt ℝ 2 R (fderiv ℝ f x))
    (hA : ContDiffAt ℝ 1 A (iteratedFDeriv ℝ 2 f x))
    (hAx : A (iteratedFDeriv ℝ 2 f x) = hessianTrace m)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (heq : ∀ z w, ‖z - x‖ < r₀ → ‖w - x‖ < r₀ →
      segmentMean A (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w)
        (iteratedFDeriv ℝ 2 f w - iteratedFDeriv ℝ 2 f z) =
        R (fderiv ℝ f w) - R (fderiv ℝ f z) + (U w - U z))
    (v : E m) :
    ∃ χ : E m → ℝ, (∀ᶠ y in nhds x, χ y = 1) ∧
      ContDiff ℝ 2 (fun y => χ y * fderiv ℝ f y v) ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun y => χ y * fderiv ℝ f y v)) := by
  letI : FiniteDimensional ℝ (E m [×2]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (hessianCurry (E m) ℝ).toLinearEquiv.toLinearMap
      (hessianCurry (E m) ℝ).injective
  obtain ⟨U₀, hU₀, hU₀c, heU⟩ := exists_compact_contDiff_extension (n := 2) hU
  obtain ⟨R₀, hR₀, hR₀c, heR⟩ := exists_compact_contDiff_extension (n := 2) hR
  obtain ⟨A₀, hA₀, hA₀c, heA⟩ := exists_compact_contDiff_extension (n := 1) hA
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp heA
  have hHnear : ∀ᶠ z in nhds x, iteratedFDeriv ℝ 2 f z ∈ Metric.ball (iteratedFDeriv ℝ 2 f x) ρ :=
    (hf.continuous_iteratedFDeriv (by norm_num)).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
  have hRnear : ∀ᶠ z in nhds x, R₀ (fderiv ℝ f z) = R (fderiv ℝ f z) :=
    heR.comp_tendsto (hf.continuous_fderiv (by norm_num)).continuousAt
  have hnear : ∀ᶠ z in nhds x,
      iteratedFDeriv ℝ 2 f z ∈ Metric.ball (iteratedFDeriv ℝ 2 f x) ρ ∧
        R₀ (fderiv ℝ f z) = R (fderiv ℝ f z) ∧ U₀ z = U z ∧ ‖z - x‖ < r₀ := by
    filter_upwards [hHnear, hRnear, heU, Metric.ball_mem_nhds x hr₀] with z hz hRz hUz hzr
    exact ⟨hz, hRz, hUz, by simpa only [Metric.mem_ball, dist_eq_norm] using hzr⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hAx₀ : A₀ (iteratedFDeriv ℝ 2 f x) = hessianTrace m := heA.eq_of_nhds.trans hAx
  apply nonlinear_quotient_regularization hf hfc hU₀ hU₀c hR₀ hR₀c hA₀ hα hα1 hH x hAx₀ hr _ v
  intro z w hz hw
  have hzz := hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
  have hww := hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hw)
  have hmean : segmentMean A₀ (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w) =
      segmentMean A (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w) := by
    unfold segmentMean
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    apply hρsub
    exact (convex_ball _ _) hzz.1 hww.1 (sub_nonneg.mpr ht'.2) ht'.1 (by ring)
  rw [hmean, hzz.2.1, hww.2.1, hzz.2.2.1, hww.2.2.1]
  exact heq z w hzz.2.2.2 hww.2.2.2

end Submission.Obl.Entropy__smooth_gaussian_transport
