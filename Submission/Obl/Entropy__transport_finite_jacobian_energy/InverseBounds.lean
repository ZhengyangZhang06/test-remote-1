/-
Adapted from: here:o018
Original proof by x0102, commit daff4e4; source posted by x0108 on o027 at 2026-10-17T07:37Z.
Only the namespace is adapted.
-/

import Submission.Obl.Entropy__c1_bounded_matrix_calculus
import Submission.Lib.GaussianTransport.GaussianMatrixInverse
set_option autoImplicit false

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

open scoped Matrix.Norms.L2Operator MatrixOrder
open Submission.Obl.Entropy__c1_bounded_matrix_calculus
open Submission.Lib.GaussianTransport

variable {α n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix inversion agrees with reciprocal scalar functional calculus. -/
theorem inv_cfc_eq_cfc_inv {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ a, f a ≠ 0) :
    (cfc f A)⁻¹ = cfc (fun a => (f a)⁻¹) A := by
  apply Matrix.inv_eq_left_inv
  rw [← cfc_mul (fun a => (f a)⁻¹) f A (hf.inv₀ hf0).continuousOn hf.continuousOn]
  simp only [inv_mul_cancel₀ (hf0 _)]
  exact cfc_const_one ℝ A hA.isSelfAdjoint

/-- Positive continuous scalar functions have a uniform positive matrix lower bound
on an entry-bounded Hermitian field. -/
theorem exists_uniform_cfc_lower_bound (A : α → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (hfpos : ∀ a, 0 < f a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, (cfc f (A x) - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨R, hR, hspec⟩ := exists_spectrum_subset_Icc_of_bounded_entries A hA hbound
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.continuousOn
  refine ⟨f t, hfpos t, fun x => ?_⟩
  apply Matrix.le_iff.mp
  rw [← Algebra.algebraMap_eq_smul_one, ← cfc_const (f t) (A x) (hA x).isSelfAdjoint]
  apply (cfc_le_iff (fun _ => f t) f (A x) continuous_const.continuousOn
    hf.continuousOn (hA x).isSelfAdjoint).2
  intro a ha
  exact hmin (hspec x ha)

/-- A positive matrix scalar lower bound controls each canonical eigenvalue. -/
theorem eigenvalue_ge_of_scalar_lower {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {c : ℝ} (hc : (M - c • (1 : Matrix n n ℝ)).PosSemidef) (i : n) :
    c ≤ hM.eigenvalues i := by
  have hs : ∀ a ∈ spectrum ℝ M, c ≤ a := by
    apply (algebraMap_le_cfc_iff (fun a : ℝ => a) c M
      continuous_id.continuousOn hM.isSelfAdjoint).mp
    simpa only [cfc_id' ℝ M hM.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] using
      (Matrix.le_iff.mpr hc)
  exact hs _ (hM.eigenvalues_mem_spectrum_real i)

/-- The inverse of a positive scalar CFC has uniform positive lower and entry bounds. -/
theorem exists_uniform_inverse_cfc_bounds (A : α → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (hfpos : ∀ a, 0 < f a) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      (∀ x, ((cfc f (A x))⁻¹ - c • (1 : Matrix n n ℝ)).PosSemidef) ∧
      (∀ x i j, |(cfc f (A x))⁻¹ i j| ≤ B) := by
  have hfi : Continuous (fun a => (f a)⁻¹) := hf.inv₀ (fun a => (hfpos a).ne')
  obtain ⟨c, hc, hclower⟩ := exists_uniform_cfc_lower_bound A hA hbound hfi
    (fun a => inv_pos.mpr (hfpos a))
  obtain ⟨B, hB, hBbound⟩ := exists_cfc_entry_bound_of_bounded_entries A hA hbound hfi
  refine ⟨c, B, hc, hB, ?_, ?_⟩
  · intro x
    rw [inv_cfc_eq_cfc_inv (hA x) hf (fun a => (hfpos a).ne')]
    exact hclower x
  · intro x i j
    rw [inv_cfc_eq_cfc_inv (hA x) hf (fun a => (hfpos a).ne')]
    exact hBbound x i j

/-- Uniform ellipticity and coefficient bounds for the transport inverse Jacobian. -/
theorem gaussian_inverse_jacobian_bounds (A : α → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      (∀ x, ((cfc gaussianHazard (A x))⁻¹ - c • (1 : Matrix n n ℝ)).PosSemidef) ∧
      (∀ x i j, |(cfc gaussianHazard (A x))⁻¹ i j| ≤ B) := by
  exact exists_uniform_inverse_cfc_bounds A hA hbound
    contDiff_gaussianHazard.continuous gaussianHazard_pos

end Submission.Obl.Entropy__transport_finite_jacobian_energy
