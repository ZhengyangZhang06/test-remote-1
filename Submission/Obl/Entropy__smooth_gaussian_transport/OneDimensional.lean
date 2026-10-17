import Submission.Obl.Entropy__smooth_gaussian_transport.Scalar

open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The single Euclidean coordinate, as a volume-preserving linear isometry. -/
noncomputable def oneCoordinate : E 1 ≃ₗᵢ[ℝ] ℝ :=
  { (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv with
    norm_map' := fun x => by
      change ‖x 0‖ = ‖x‖
      simp [PiLp.norm_eq_of_L2, Real.sqrt_sq_eq_abs] }

theorem map_oneCoordinate_stdGaussian :
    (stdGaussian (E 1)).map oneCoordinate = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map oneCoordinate.continuous.measurable (by fun_prop)]
  change (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map (Function.eval 0) = _
  exact (measurePreserving_eval (μ := fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq

theorem gradient_comp_oneCoordinate {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (x : E 1) :
    gradient (ψ ∘ oneCoordinate) x = oneCoordinate.symm (deriv ψ (oneCoordinate x)) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hψ (oneCoordinate x)).hasDerivAt.comp_hasFDerivAt x
    oneCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  convert! hd using 1
  ext v
  change inner ℝ (oneCoordinate.symm (deriv ψ (oneCoordinate x))) v =
    deriv ψ (oneCoordinate x) * oneCoordinate v
  rw [← oneCoordinate.inner_map_map, oneCoordinate.apply_symm_apply]
  simp [mul_comm]

theorem map_oneCoordinate_symm_withDensity {f : E 1 → ℝ} (hf : Measurable f) :
    (volume.withDensity (fun t => ENNReal.ofReal (f (oneCoordinate.symm t)))).map
      oneCoordinate.symm = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  ext s hs
  rw [Measure.map_apply oneCoordinate.symm.continuous.measurable hs,
    withDensity_apply _ (oneCoordinate.symm.continuous.measurable hs),
    withDensity_apply _ hs]
  exact oneCoordinate.symm.measurePreserving.setLIntegral_comp_preimage hs hf.ennreal_ofReal

/-- The obligation in dimension one. No Hessian or moment assumptions are needed in this case. -/
theorem exists_smooth_convex_gradient_transport_one {V : E 1 → ℝ}
    (hV : ContDiff ℝ ∞ V)
    (hi : Integrable (fun x => Real.exp (-V x)) volume)
    (hm : ∫ x, Real.exp (-V x) = 1) :
    ∃ φ : E 1 → ℝ, ContDiff ℝ ∞ φ ∧ ConvexOn ℝ univ φ ∧
      (stdGaussian (E 1)).map (gradient φ) =
        volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) := by
  let f : ℝ → ℝ := fun t => Real.exp (-V (oneCoordinate.symm t))
  have hf : ContDiff ℝ ∞ f :=
    (hV.comp oneCoordinate.symm.toContinuousLinearEquiv.contDiff).neg.exp
  have hfi : Integrable f volume :=
    oneCoordinate.symm.measurePreserving.integrable_comp_of_integrable hi
  have hfm : ∫ t, f t = 1 := by
    calc
      (∫ t, f t) = ∫ x, Real.exp (-V x) :=
        oneCoordinate.symm.measurePreserving.integral_comp
          oneCoordinate.symm.toHomeomorph.measurableEmbedding (fun x => Real.exp (-V x))
      _ = 1 := hm
  obtain ⟨ψ, hψs, hψc, hlaw⟩ :=
    exists_scalar_smooth_convex_transport hf hfi (fun t => Real.exp_pos _) hfm
  refine ⟨ψ ∘ oneCoordinate, hψs.comp oneCoordinate.toContinuousLinearEquiv.contDiff, ?_, ?_⟩
  · simpa using hψc.comp_linearMap oneCoordinate.toLinearEquiv.toLinearMap
  · have hgrad : gradient (ψ ∘ oneCoordinate) =
        oneCoordinate.symm ∘ deriv ψ ∘ oneCoordinate :=
      funext (gradient_comp_oneCoordinate (hψs.differentiable (by simp)))
    rw [hgrad, ← Measure.map_map oneCoordinate.symm.continuous.measurable
      ((measurable_deriv ψ).comp oneCoordinate.continuous.measurable),
      ← Measure.map_map (measurable_deriv ψ) oneCoordinate.continuous.measurable,
      map_oneCoordinate_stdGaussian, hlaw]
    exact map_oneCoordinate_symm_withDensity (f := fun x => Real.exp (-V x))
      hV.neg.exp.continuous.measurable

end Submission.Obl.Entropy__smooth_gaussian_transport
