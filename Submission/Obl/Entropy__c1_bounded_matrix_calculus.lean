import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCUniform

open scoped Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__c1_bounded_matrix_calculus

lemma exists_cfc_entry_bound_of_bounded_entries {α n : Type*} [Fintype n] [DecidableEq n]
    (A : α → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ S : ℝ, 0 < S ∧ ∀ x i j, |cfc f (A x) i j| ≤ S := by
  obtain ⟨C, hC, hnorm⟩ := exists_cfc_norm_bound_of_bounded_entries A hA hbound hf
  let L : Matrix n n ℝ →L[ℝ] (n → n → ℝ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨‖L‖ * C + 1, by positivity, fun x i j => ?_⟩
  have hpi : ‖L (cfc f (A x))‖ ≤ ‖L‖ * C :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hnorm x) (norm_nonneg L))
  have hi : ‖L (cfc f (A x)) i j‖ ≤ ‖L (cfc f (A x))‖ :=
    (norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)
  change |cfc f (A x) i j| ≤ ‖L‖ * C + 1
  have := hi.trans hpi
  have he : L (cfc f (A x)) i j = cfc f (A x) i j := rfl
  rw [he, Real.norm_eq_abs] at this
  exact this.trans (by linarith)

end Submission.Obl.Entropy__c1_bounded_matrix_calculus

open Submission.Obl.Entropy__c1_bounded_matrix_calculus

theorem Submission.Entropy.c1_bounded_matrix_calculus : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), (∀ x, (A x).IsHermitian) → (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → (∀ i j, ContDiff ℝ 1 (fun x => cfc g (A x) i j)) ∧ (∃ S : ℝ, 0 < S ∧ ∀ x i j, |cfc g (A x) i j| ≤ S) := by
  intro m _ A hA hAs hbound g hg
  exact ⟨contDiff_one_cfc_entries hAs hA hg,
    exists_cfc_entry_bound_of_bounded_entries A hA hbound hg.continuous⟩
