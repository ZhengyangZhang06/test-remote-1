import Submission.Lib.GaussianTransport.GaussianModel
import Submission.Obl.Entropy__two_eigenvalue_negative_certificate.Calculus

open scoped ContDiff

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__two_eigenvalue_negative_certificate

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

noncomputable abbrev scalarK : ℝ → ℝ := transportRatio
noncomputable abbrev scalarB : ℝ → ℝ := deriv scalarK
noncomputable abbrev scalarL : ℝ → ℝ := deriv scalarB
noncomputable def scalarF (a : ℝ) : ℝ := scalarK a * (1 + scalarB a)
noncomputable def scalarP (a : ℝ) : ℝ :=
  deriv scalarF a - (scalarB a)^2 - (40/3) * (scalarL a)^2
noncomputable def scalarH (a : ℝ) : ℝ :=
  scalarK a * (1 + scalarB a) - (3/2) * scalarK a -
    (80/3) * (scalarB a - 7/25) * scalarL a
noncomputable def scalarCost (a : ℝ) : ℝ :=
  (40/37) * ((scalarB a - 7/25)^2 + (5/96) * (scalarH a)^2 / scalarP a)

lemma smooth_scalarK : ContDiff ℝ ∞ scalarK :=
  contDiff_exponentialTransport.div contDiff_gaussianHazard
    (fun a => (gaussianHazard_pos a).ne')

lemma smooth_scalarB : ContDiff ℝ ∞ scalarB :=
  (contDiff_infty_iff_deriv.mp smooth_scalarK).2

lemma smooth_scalarL : ContDiff ℝ ∞ scalarL :=
  (contDiff_infty_iff_deriv.mp smooth_scalarB).2

lemma smooth_scalarF : ContDiff ℝ ∞ scalarF :=
  smooth_scalarK.mul (contDiff_const.add smooth_scalarB)

lemma smooth_scalarP : ContDiff ℝ ∞ scalarP :=
  ((contDiff_infty_iff_deriv.mp smooth_scalarF).2.sub (smooth_scalarB.pow 2)).sub
    (contDiff_const.mul (smooth_scalarL.pow 2))

lemma smooth_scalarH : ContDiff ℝ ∞ scalarH :=
  ((smooth_scalarK.mul (contDiff_const.add smooth_scalarB)).sub
    (contDiff_const.mul smooth_scalarK)).sub
    ((contDiff_const.mul (smooth_scalarB.sub contDiff_const)).mul smooth_scalarL)

lemma smooth_scalarCost (hp : ∀ a, 0 < scalarP a) : ContDiff ℝ ∞ scalarCost :=
  contDiff_const.mul (((smooth_scalarB.sub contDiff_const).pow 2).add
    ((contDiff_const.mul (smooth_scalarH.pow 2)).div smooth_scalarP
      (fun a => (hp a).ne')))

lemma smooth_scalarInvSqrt (hp : ∀ a, 0 < scalarP a) :
    ContDiff ℝ ∞ (fun a => (Real.sqrt (scalarP a))⁻¹) :=
  (smooth_scalarP.sqrt (fun a => (hp a).ne')).inv
    (fun a => (Real.sqrt_pos.2 (hp a)).ne')

lemma scalar_hazard_identity (a : ℝ) :
    gaussianHazard a - scalarK a = a * scalarB a - scalarL a := by
  simp only [scalarK, scalarB, scalarL, deriv_ratio, deriv_slope]
  unfold transportCurvature
  ring

lemma cfc_hazard_identity {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    cfc gaussianHazard A - cfc scalarK A = A * cfc scalarB A - cfc scalarL A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  calc
    cfc gaussianHazard A - cfc scalarK A = cfc (fun a => gaussianHazard a - scalarK a) A :=
      (cfc_sub _ _ A (hc _) (hc _)).symm
    _ = cfc (fun a => a * scalarB a - scalarL a) A :=
      cfc_congr (fun a _ => scalar_hazard_identity a)
    _ = A * cfc scalarB A - cfc scalarL A := by
      rw [cfc_sub _ _ A (hc _) (hc _), cfc_mul _ _ A (hc _) (hc _)]
      rw [show cfc (fun a : ℝ => a) A = A from cfc_id ℝ A hA.isSelfAdjoint]

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
