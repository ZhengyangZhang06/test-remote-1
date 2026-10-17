import Submission.Obl.Entropy__smooth_gaussian_transport.LocalNonlinearStep
import Submission.Obl.Entropy__smooth_gaussian_transport.LocalHessianExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.LocalDerivativeCriterion
import Submission.Obl.Entropy__smooth_gaussian_transport.JetLinearChange
import Submission.Obl.Entropy__smooth_gaussian_transport.TransportCoordinates

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A classical strictly elliptic Monge–Ampère transport potential with a
locally Hölder Hessian has three continuous derivatives. -/
theorem transport_contDiff_three {m : ℕ} {φ U V : E m → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (operatorMatrix (fderiv ℝ (gradient φ) x)).PosDef)
    (heq : ∀ x, Real.log (fderiv ℝ (gradient φ) x).det = U x + V (gradient φ x))
    (hholder : ∀ K : Set (E m), IsCompact K → ∃ α C : ℝ,
      0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ 2 φ x - iteratedFDeriv ℝ 2 φ y‖ ≤ C * ‖x - y‖ ^ α) :
    ContDiff ℝ 3 φ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨α, C, hα, hα1, hC, hmod⟩ := hholder (Metric.closedBall x 2) (isCompact_closedBall _ _)
  obtain ⟨g, hg, hgc, hge, hgH⟩ := exists_compact_hessian_holder_extension hφ x hα hα1 hC hmod
  obtain ⟨L, hL⟩ := exists_principal_hessian_normalizer (hpos x)
  let z : E m := L.symm x
  let f : E m → ℝ := fun y => g (L y)
  let ψ : E m → ℝ := fun y => φ (L y)
  have hf : ContDiff ℝ 2 f := hg.comp L.contDiff
  have hfc : HasCompactSupport f := hgc.comp_homeomorph L.toHomeomorph
  have hfH : UniformBoundedHolder (α / 2) (fun (_ : Unit) => iteratedFDeriv ℝ 2 f) :=
    uniformBoundedHolder_hessian_comp hg (by positivity)
      (hgH.lower_exponent (by positivity) (by linarith)) L.toContinuousLinearMap
  have hfe : f =ᶠ[nhds z] ψ := by
    apply hge.comp_tendsto
    simpa only [z, L.apply_symm_apply] using L.continuous.tendsto z
  have hfeD := hfe.fderiv (𝕜 := ℝ)
  have hfeH := hfe.iteratedFDeriv (𝕜 := ℝ) 2
  have hHbase : hessianOperator m (untransformHessian L (iteratedFDeriv ℝ 2 f z)) =
      fderiv ℝ (gradient φ) x := by
    rw [hfeH.eq_of_nhds, untransformHessian_iteratedFDeriv hφ, hessianOperator_iteratedFDeriv hφ]
    simp only [z, L.apply_symm_apply]
  have hAbase : normalizedPrincipal L (iteratedFDeriv ℝ 2 f z) = hessianTrace m := by
    rw [hfeH.eq_of_nhds]
    apply normalizedPrincipal_at_base hφ z L
    intro B
    simpa only [z, L.apply_symm_apply, untransformHessian,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply] using hL B
  have hA : ContDiffAt ℝ 1 (normalizedPrincipal L) (iteratedFDeriv ℝ 2 f z) :=
    normalizedPrincipal_contDiffAt L (by rw [hHbase]; simpa only [operatorMatrix_det] using (hpos x).det_pos.ne')
  have hnear : ∀ᶠ y in nhds z,
      fderiv ℝ f y = fderiv ℝ ψ y ∧ iteratedFDeriv ℝ 2 f y = iteratedFDeriv ℝ 2 ψ y := hfeD.and hfeH
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hinc (s t : E m) (hs : ‖s - z‖ < r) (ht : ‖t - z‖ < r) :
      segmentMean (normalizedPrincipal L) (iteratedFDeriv ℝ 2 f s) (iteratedFDeriv ℝ 2 f t)
        (iteratedFDeriv ℝ 2 f t - iteratedFDeriv ℝ 2 f s) =
      V (normalizedGradient m L (fderiv ℝ f t)) - V (normalizedGradient m L (fderiv ℝ f s)) +
        (U (L t) - U (L s)) := by
    have hss := hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hs)
    have htt := hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using ht)
    rw [hss.1, hss.2, htt.1, htt.2]
    exact normalized_transport_increment hφ hpos heq L s t
  have hf3 : ContDiffAt ℝ 3 f z := by
    apply contDiffAt_three_of_local_directional_derivatives (hf.of_le (by norm_num)) z
    intro v
    obtain ⟨χ, hone, hreg, hbound⟩ := local_nonlinear_quotient_regularization hf hfc
      (by positivity : 0 < α / 2) (by linarith : α / 2 < 1) hfH z
      (hU.comp L.contDiff).contDiffAt
      (hV.comp (normalizedGradient m L).contDiff).contDiffAt hA hAbase hr hinc v
    exact ⟨χ, hone, hreg⟩
  have hψ3 : ContDiffAt ℝ 3 ψ z := hf3.congr_of_eventuallyEq hfe.symm
  have hφ3 := hψ3.comp x L.symm.contDiff.contDiffAt
  convert! hφ3 using 1
  funext y
  exact congrArg φ (L.apply_symm_apply y).symm

end Submission.Obl.Entropy__smooth_gaussian_transport
