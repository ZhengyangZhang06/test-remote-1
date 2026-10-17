import Submission.Obl.Entropy__transport_finite_jacobian_energy.ChainRule
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Density
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Injective
import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.LocalL1
import Submission.Lib.GaussianTransport.GaussianMatrixInverse

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open Submission.Lib.GaussianTransport
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

noncomputable def gaussianPotential (x : space m) : ℝ :=
  ∑ i, -Real.log (normalPDF (x i))

lemma contDiff_gaussianPotential : ContDiff ℝ ∞ (gaussianPotential : space m → ℝ) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_normalPDF.comp (EuclideanSpace.proj i : space m →L[ℝ] ℝ).contDiff).log
    (fun x => (normalPDF_pos (x i)).ne')).neg

lemma directional_gaussianPotential (x : space m) (i : Fin m) :
    directional (basisVector i) gaussianPotential x = x i := by
  have hd (r : Fin m) : HasFDerivAt (fun y : space m => -Real.log (normalPDF (y r)))
      ((x r) • (EuclideanSpace.proj r : space m →L[ℝ] ℝ)) x := by
    have hp : HasDerivAt (fun t : ℝ => -Real.log (normalPDF t)) (x r) (x r) := by
      convert! ((hasDerivAt_normalPDF (x r)).log (normalPDF_pos (x r)).ne').neg using 1
      field_simp [(normalPDF_pos (x r)).ne']
    convert! hp.comp_hasFDerivAt x (EuclideanSpace.proj r : space m →L[ℝ] ℝ).hasFDerivAt using 1
  change fderiv ℝ (fun y : space m => ∑ r, -Real.log (normalPDF (y r))) x (basisVector i) = _
  rw [(HasFDerivAt.fun_sum (fun r _ => hd r)).fderiv]
  simp [basisVector, PiLp.single_apply]

lemma exp_neg_gaussianPotential (x : space m) :
    Real.exp (-gaussianPotential x) =
      Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.gaussianDensity x := by
  simp only [gaussianPotential, ← Finset.sum_neg_distrib, neg_neg, Real.exp_sum,
    Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.gaussianDensity]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (normalPDF_pos (x i))

lemma stdGaussian_eq_expPotential :
    stdGaussian (space m) = volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-gaussianPotential x))) := by
  simp_rw [exp_neg_gaussianPotential]
  exact Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.stdGaussian_eq_withDensity

/-- The hypotheses of the obligation imply the full logarithmic transport equation. -/
lemma transport_gaussian_logdet {φ V : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hpos : ∀ x, (J x).PosDef)
    (hmap : (stdGaussian (space m)).map (gradient φ) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (x : space m) : Real.log (J x).det = V (gradient φ x) - gaussianPotential x := by
  have hc := contDiff_gradient hφ
  have hd := hc.differentiable (by simp)
  have hdet (y : space m) : (fderiv ℝ (gradient φ) y).det = (J y).det :=
    det_derivative_from_basis (gradient φ) J hJ y
  rw [stdGaussian_eq_expPotential] at hmap
  have h := transport_logdet volume (fun y => (hd y).hasFDerivAt)
    (injective_of_posDef_jacobian hd hpos hJ)
    (ContinuousLinearMap.continuous_det.comp (hc.fderiv_right (m := ∞) (by simp)).continuous)
    (fun y => by rw [hdet]; exact (hpos y).det_pos)
    contDiff_gaussianPotential.continuous hV.continuous hmap x
  rwa [hdet] at h

end Submission.Obl.Entropy__transport_finite_jacobian_energy
