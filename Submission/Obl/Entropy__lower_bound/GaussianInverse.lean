import Submission.Obl.Entropy__lower_bound.GaussianTails

/-!
# The inverse Gaussian parametrization

Section 2.1 uses the increasing Gaussian hazard as a smooth change of variable
from the real line to the positive real numbers. This module supplies its
inverse, including the smoothness and derivative needed for the transport
Jacobian parametrization.
-/

open Set Filter
open scoped Topology ContDiff

namespace Submission.Obl.Entropy__lower_bound

/-- The inverse Gaussian hazard, used only at positive arguments. -/
noncomputable def inverseGaussianHazard : ℝ → ℝ := Function.invFun gaussianHazard

/-- The inverse recovers every real parameter. -/
theorem inverseGaussianHazard_gaussianHazard (a : ℝ) :
    inverseGaussianHazard (gaussianHazard a) = a :=
  Function.leftInverse_invFun strictMono_gaussianHazard.injective a

/-- Every positive Jacobian eigenvalue has a parameter. -/
theorem gaussianHazard_inverseGaussianHazard {y : ℝ} (hy : 0 < y) :
    gaussianHazard (inverseGaussianHazard y) = y := by
  apply Function.invFun_eq
  change y ∈ Set.range gaussianHazard
  rwa [range_gaussianHazard]

/-- The inverse is strictly increasing on its natural domain. -/
theorem strictMonoOn_inverseGaussianHazard :
    StrictMonoOn inverseGaussianHazard (Ioi 0) := by
  intro x hx y hy hxy
  apply strictMono_gaussianHazard.lt_iff_lt.mp
  simpa only [gaussianHazard_inverseGaussianHazard hx,
    gaussianHazard_inverseGaussianHazard hy] using hxy

/-- Inverse differentiation on the positive real axis. -/
theorem hasStrictDerivAt_inverseGaussianHazard {y : ℝ} (hy : 0 < y) :
    HasStrictDerivAt inverseGaussianHazard
      (deriv gaussianHazard (inverseGaussianHazard y))⁻¹ y := by
  have hd := contDiff_gaussianHazard.hasStrictDerivAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    (x := inverseGaussianHazard y)
  have hi := hd.to_local_left_inverse
    (ne_of_gt (deriv_gaussianHazard_pos _))
    (Eventually.of_forall inverseGaussianHazard_gaussianHazard)
  simpa only [gaussianHazard_inverseGaussianHazard hy] using hi

/-- The inverse is continuous throughout the positive real axis. -/
theorem continuousOn_inverseGaussianHazard :
    ContinuousOn inverseGaussianHazard (Ioi 0) :=
  fun _ hy => (hasStrictDerivAt_inverseGaussianHazard hy).hasDerivAt.continuousAt.continuousWithinAt

/-- The hazard is a homeomorphism between the real line and the positive axis. -/
noncomputable def gaussianHazardPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := gaussianHazard
  invFun := inverseGaussianHazard
  source := univ
  target := Ioi 0
  map_source' := fun a _ => gaussianHazard_pos a
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun a _ => inverseGaussianHazard_gaussianHazard a
  right_inv' := fun _ hy => gaussianHazard_inverseGaussianHazard hy
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  continuousOn_toFun := contDiff_gaussianHazard.continuous.continuousOn
  continuousOn_invFun := continuousOn_inverseGaussianHazard

/-- Smoothness of the inverse at every positive value. -/
theorem contDiffAt_inverseGaussianHazard {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ inverseGaussianHazard y := by
  exact gaussianHazardPartialHomeomorph.contDiffAt_symm_deriv
    (ne_of_gt (deriv_gaussianHazard_pos _)) hy
    (contDiff_gaussianHazard.differentiable (by simp) _).hasDerivAt
    contDiff_gaussianHazard.contDiffAt

/-- Smoothness on the positive real axis. -/
theorem contDiffOn_inverseGaussianHazard :
    ContDiffOn ℝ ∞ inverseGaussianHazard (Ioi 0) :=
  fun _ hy => (contDiffAt_inverseGaussianHazard hy).contDiffWithinAt

/-- The inverse derivative in the scalar notation of Section 2.1. -/
theorem deriv_inverseGaussianHazard {y : ℝ} (hy : 0 < y) :
    deriv inverseGaussianHazard y =
      (y * gaussianGap (inverseGaussianHazard y))⁻¹ := by
  rw [(hasStrictDerivAt_inverseGaussianHazard hy).hasDerivAt.deriv,
    (hasDerivAt_gaussianHazard _).deriv]
  simp only [gaussianHazard_inverseGaussianHazard hy, gaussianGap]

/-- Since the hazard has derivative less than one, its inverse expands lengths. -/
theorem one_lt_deriv_inverseGaussianHazard {y : ℝ} (hy : 0 < y) :
    1 < deriv inverseGaussianHazard y := by
  rw [(hasStrictDerivAt_inverseGaussianHazard hy).hasDerivAt.deriv]
  exact (one_lt_inv₀ (deriv_gaussianHazard_pos _)).2 (deriv_gaussianHazard_lt_one _)

end Submission.Obl.Entropy__lower_bound
