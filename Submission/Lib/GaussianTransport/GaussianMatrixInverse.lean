/-
Adapted from: here:o001

Original proofs by session x0022 (commit 9b4efef), building on the Gaussian scalar
calculus developed by x0004 in this workspace.
-/

import Submission.Lib.GaussianTransport.GaussianInverse

/-!
# Spectral inverse of the Gaussian hazard

The transport parametrization in Section 2 is `A = q⁻¹(J)`, where `J` is
positive definite. The identities below justify this change of variable
and transfer compact spectral bounds from `J` to `A`.
-/

open Set

namespace Submission.Lib.GaussianTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positivity of the spectrum of a positive definite real matrix. -/
theorem posDef_spectrum_subset_pos {J : Matrix ι ι ℝ} (hJ : J.PosDef) :
    spectrum ℝ J ⊆ Ioi 0 := by
  rw [hJ.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hJ.eigenvalues_pos i

/-- Spectral application of the inverse recovers every symmetric parameter matrix. -/
theorem cfc_inverseGaussianHazard_gaussianHazard {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) :
    cfc inverseGaussianHazard (cfc gaussianHazard A) = A := by
  rw [← cfc_comp inverseGaussianHazard gaussianHazard A hA.isSelfAdjoint
    (continuousOn_inverseGaussianHazard.mono (by
      rintro _ ⟨a, _, rfl⟩
      exact gaussianHazard_pos a)) contDiff_gaussianHazard.continuous.continuousOn]
  have he : inverseGaussianHazard ∘ gaussianHazard = id :=
    funext inverseGaussianHazard_gaussianHazard
  rw [he, cfc_id ℝ A hA.isSelfAdjoint]

/-- Applying the hazard after its spectral inverse recovers a positive Jacobian. -/
theorem cfc_gaussianHazard_inverseGaussianHazard {J : Matrix ι ι ℝ}
    (hJ : J.PosDef) :
    cfc gaussianHazard (cfc inverseGaussianHazard J) = J := by
  rw [← cfc_comp gaussianHazard inverseGaussianHazard J hJ.isHermitian.isSelfAdjoint
    contDiff_gaussianHazard.continuous.continuousOn
    (continuousOn_inverseGaussianHazard.mono (posDef_spectrum_subset_pos hJ))]
  calc
    cfc (gaussianHazard ∘ inverseGaussianHazard) J = cfc (id : ℝ → ℝ) J :=
      cfc_congr fun _ hy => gaussianHazard_inverseGaussianHazard
        (posDef_spectrum_subset_pos hJ hy)
    _ = J := cfc_id ℝ J hJ.isHermitian.isSelfAdjoint

/-- The hazard of a symmetric matrix is positive definite. -/
theorem posDef_cfc_gaussianHazard {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (cfc gaussianHazard A).PosDef := by
  have hQ : (cfc gaussianHazard A).IsHermitian := cfc_predicate _ _
  apply hQ.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hs := hQ.eigenvalues_mem_spectrum_real i
  rw [cfc_map_spectrum gaussianHazard A hA.isSelfAdjoint
    contDiff_gaussianHazard.continuous.continuousOn] at hs
  rcases hs with ⟨a, _, ha⟩
  rw [← ha]
  exact gaussianHazard_pos a

/-- The symmetric parameter of a positive Jacobian is unique. -/
theorem cfc_gaussianHazard_eq_iff {A J : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hJ : J.PosDef) :
    cfc gaussianHazard A = J ↔ A = cfc inverseGaussianHazard J := by
  constructor
  · intro h
    rw [← h, cfc_inverseGaussianHazard_gaussianHazard hA]
  · rintro rfl
    exact cfc_gaussianHazard_inverseGaussianHazard hJ

/-- Every positive definite Jacobian admits a unique symmetric parameter. -/
theorem existsUnique_gaussianHazard_parameter {J : Matrix ι ι ℝ} (hJ : J.PosDef) :
    ∃! A : Matrix ι ι ℝ, A.IsHermitian ∧ cfc gaussianHazard A = J := by
  refine ⟨cfc inverseGaussianHazard J,
    ⟨cfc_predicate _ _, cfc_gaussianHazard_inverseGaussianHazard hJ⟩, ?_⟩
  intro A hA
  exact (cfc_gaussianHazard_eq_iff hA.1 hJ).mp hA.2

/-- Compact positive spectral bounds become compact bounds on the parameter. -/
theorem spectrum_inverseGaussianHazard_subset {J : Matrix ι ι ℝ}
    (hJ : J.PosDef) {l u : ℝ} (hl : 0 < l)
    (hbounds : spectrum ℝ J ⊆ Icc l u) :
    spectrum ℝ (cfc inverseGaussianHazard J) ⊆
      Icc (inverseGaussianHazard l) (inverseGaussianHazard u) := by
  rw [cfc_map_spectrum inverseGaussianHazard J hJ.isHermitian.isSelfAdjoint
    (continuousOn_inverseGaussianHazard.mono (posDef_spectrum_subset_pos hJ))]
  rintro _ ⟨a, ha, rfl⟩
  have ha0 := posDef_spectrum_subset_pos hJ ha
  have hb := hbounds ha
  exact ⟨strictMonoOn_inverseGaussianHazard.monotoneOn hl ha0 hb.1,
    strictMonoOn_inverseGaussianHazard.monotoneOn ha0 (lt_of_lt_of_le ha0 hb.2) hb.2⟩

end Submission.Lib.GaussianTransport
