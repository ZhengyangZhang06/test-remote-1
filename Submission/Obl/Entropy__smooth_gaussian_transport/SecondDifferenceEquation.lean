import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedDeterminant
import Submission.Obl.Entropy__smooth_gaussian_transport.UniformEllipticity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def secondDifference {m : ℕ} (u : E m → ℝ) (h x : E m) : ℝ :=
  symmetricAverage u h x - u x

theorem secondDifference_contDiff {m : ℕ} {u : E m → ℝ} {n : WithTop ENat}
    (hu : ContDiff ℝ n u) (h : E m) : ContDiff ℝ n (secondDifference u h) :=
  (symmetricAverage_contDiff hu h).sub hu

theorem gradient_secondDifference {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) (h x : E m) :
    gradient (secondDifference u h) x =
      (1 / 2 : ℝ) • (gradient u (x + h) + gradient u (x - h)) - gradient u x := by
  have he : gradient (secondDifference u h) x =
      gradient (symmetricAverage u h) x - gradient u x := by
    have hd : HasFDerivAt (secondDifference u h)
        (fderiv ℝ (symmetricAverage u h) x - fderiv ℝ u x) x :=
      ((symmetricAverage_contDiff hu h).differentiable_one x).hasFDerivAt.sub
        (hu.differentiable_one x).hasFDerivAt
    simp only [gradient, hd.fderiv, map_sub]
  rw [he, gradient_symmetricAverage hu.differentiable_one]

theorem hasFDerivAt_gradient_secondDifference {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {h x : E m}
    (hx : DifferentiableAt ℝ (gradient u) x)
    (hp : DifferentiableAt ℝ (gradient u) (x + h))
    (hn : DifferentiableAt ℝ (gradient u) (x - h)) :
    HasFDerivAt (gradient (secondDifference u h))
      ((1 / 2 : ℝ) • (fderiv ℝ (gradient u) (x + h) + fderiv ℝ (gradient u) (x - h)) -
        fderiv ℝ (gradient u) x) x := by
  rw [funext (gradient_secondDifference hu h)]
  exact ((((hasFDerivAt_comp_add_right h).mpr hp.hasFDerivAt).add
    ((hasFDerivAt_comp_sub h).mpr hn.hasFDerivAt)).const_smul (1 / 2 : ℝ)).sub hx.hasFDerivAt

/-- The nondivergence form operator obtained by linearizing the transport
equation. Its coefficients use only the almost-everywhere Hessian. -/
noncomputable def linearizedTransport {m : ℕ} (V u w : E m → ℝ) (x : E m) : ℝ :=
  linearizedTrace (fderiv ℝ (gradient u) x) (fderiv ℝ (gradient w) x) -
    inner ℝ (gradient V (gradient u x)) (gradient w x)

/-- The centered second difference is a subsolution of the linearized
transport equation. No second derivative continuity is required. -/
theorem brenier_ae_linearized_secondDifference {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (h : E m) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient (secondDifference φ h)) x ∧
      -‖h‖ ^ 2 / 2 ≤ linearizedTransport V φ (secondDifference φ h) x := by
  have hAE := brenier_ae_positive_hessian hm hV.continuous hφ hlaw
  have hplus := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hAE
  have hminus := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hAE
  have hC1 := (brenier_contDiff_one hm hV.continuous hφ hlaw).1
  filter_upwards [hAE, hplus, hminus] with x hx hp hn
  have hd := hasFDerivAt_gradient_secondDifference hC1 hx.1 hp.1 hn.1
  refine ⟨hd.differentiableAt, ?_⟩
  have hl := log_det_midpoint_sub_le_linearizedTrace hx.2.1 hp.2.1 hn.2.1
  rw [hx.2.2, hp.2.2, hn.2.2] at hl
  simp only [Real.log_mul (Submission.Lib.EntropyRemainder.gaussianDensity_pos _).ne'
    (Real.exp_ne_zero _), Real.log_exp] at hl
  have hgauss := log_gaussianDensity_midpoint x h
  have hvp := convex_gradient_support hVc (hV.differentiable_one (gradient φ x))
    (gradient φ (x + h))
  have hvn := convex_gradient_support hVc (hV.differentiable_one (gradient φ x))
    (gradient φ (x - h))
  have hinner : inner ℝ (gradient V (gradient φ x)) (gradient (secondDifference φ h) x) =
      (inner ℝ (gradient V (gradient φ x)) (gradient φ (x + h) - gradient φ x) +
        inner ℝ (gradient V (gradient φ x)) (gradient φ (x - h) - gradient φ x)) / 2 := by
    rw [gradient_secondDifference hC1]
    simp only [inner_sub_right, real_inner_smul_right, inner_add_right]
    ring
  rw [linearizedTransport, hd.fderiv, hinner]
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
