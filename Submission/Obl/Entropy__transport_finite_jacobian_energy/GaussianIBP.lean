import Submission.Obl.Entropy__transport_finite_jacobian_energy.GaussianBridge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma hasCompactSupport_directional {f : space m → ℝ}
    (hf : HasCompactSupport f) (v : space m) : HasCompactSupport (directional v f) :=
  hf.fderiv_apply ℝ v

lemma directional_exp_gaussianPotential (x : space m) (i : Fin m) :
    directional (basisVector i) (fun y : space m => Real.exp (-gaussianPotential y)) x =
      -x i * Real.exp (-gaussianPotential x) := by
  have hd := ((contDiff_gaussianPotential.differentiable (by simp) x).hasFDerivAt.neg.exp).fderiv
  change fderiv ℝ (fun y : space m => Real.exp (-gaussianPotential y)) x (basisVector i) = _
  erw [hd]
  change Real.exp (-gaussianPotential x) * (-directional (basisVector i) gaussianPotential x) = _
  rw [directional_gaussianPotential]
  ring

/-- Gaussian integration by parts for a compactly supported smooth function. -/
lemma gaussian_integral_directional {f : space m → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfK : HasCompactSupport f) (i : Fin m) :
    (∫ x, directional (basisVector i) f x ∂stdGaussian (space m)) =
      ∫ x, x i * f x ∂stdGaussian (space m) := by
  let ρ : space m → ℝ := fun x => Real.exp (-gaussianPotential x)
  have hρ : ContDiff ℝ ∞ ρ := contDiff_gaussianPotential.neg.exp
  have hdf := contDiff_directional hf (basisVector i)
  have hdρ := contDiff_directional hρ (basisVector i)
  have h1 : Integrable (fun x => directional (basisVector i) ρ x * f x) volume :=
    (hdρ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfK.mul_left
  have h2 : Integrable (fun x => ρ x * directional (basisVector i) f x) volume :=
    (hρ.continuous.mul hdf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_directional hfK _).mul_left
  have h3 : Integrable (fun x => ρ x * f x) volume :=
    (hρ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfK.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hρ.differentiable (by simp) x) (fun x _ => hf.differentiable (by simp) x)
  simp_rw [Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.integral_gaussian_eq_density,
    ← exp_neg_gaussianPotential]
  change (∫ x, ρ x * directional (basisVector i) f x) = ∫ x, ρ x * (x i * f x)
  erw [hibp, ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change -(directional (basisVector i) ρ x * f x) = _
    rw [directional_exp_gaussianPotential]
    dsimp [ρ]
    ring

/-- Compact-test adjoint identity for a smooth coefficient. -/
lemma gaussian_compact_adjoint {z f : space m → ℝ}
    (hz : ContDiff ℝ ∞ z) (hf : ContDiff ℝ ∞ f) (hzK : HasCompactSupport z)
    (i : Fin m) :
    (∫ x, z x * (directional (basisVector i) f x - x i * f x)
      ∂stdGaussian (space m)) =
    -(∫ x, directional (basisVector i) z x * f x ∂stdGaussian (space m)) := by
  have hdz := contDiff_directional hz (basisVector i)
  have hdf := contDiff_directional hf (basisVector i)
  have h1 : Integrable (fun x => directional (basisVector i) z x * f x) (stdGaussian (space m)) :=
    (hdz.continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_directional hzK _).mul_right
  have h2 : Integrable (fun x => z x * directional (basisVector i) f x) (stdGaussian (space m)) :=
    (hz.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hzK.mul_right
  have h3 : Integrable (fun x => z x * (x i * f x)) (stdGaussian (space m)) :=
    (hz.continuous.mul ((EuclideanSpace.proj i).continuous.mul hf.continuous)).integrable_of_hasCompactSupport
      hzK.mul_right
  have h := gaussian_integral_directional (hz.mul hf) hzK.mul_right i
  have he : directional (basisVector i) (fun x => z x * f x) = fun x =>
      directional (basisVector i) z x * f x + z x * directional (basisVector i) f x := by
    funext x
    exact directional_mul (hz.differentiable (by simp) x) (hf.differentiable (by simp) x) _
  rw [he, integral_add h1 h2] at h
  have he3 : (fun x : space m => x i * (z x * f x)) = fun x => z x * (x i * f x) := by
    funext x
    ring
  rw [he3] at h
  simp_rw [mul_sub]
  rw [integral_sub h2 h3]
  linarith

end Submission.Obl.Entropy__transport_finite_jacobian_energy
