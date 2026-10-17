import Submission.Obl.Entropy__noncommuting_remainder_assembly.MatrixAlgebra
import Submission.Lib.MatrixEntropy

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_cfc_transpose (f : ℝ → ℝ) (A : Matrix ι ι ℝ) :
    (cfc f A).transpose = cfc f A := by
  simpa using (show (cfc f A).IsHermitian from cfc_predicate f A).eq

lemma matrix_cfc_posDef (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (p : ℝ → ℝ) (hp : ∀ a, 0 < p a) : (cfc p A).PosDef := by
  have hP : (cfc p A).IsHermitian := cfc_predicate p A
  apply hP.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hi := hP.eigenvalues_mem_spectrum_real i
  rw [cfc_map_spectrum p A hA.isSelfAdjoint (A.finite_real_spectrum.continuousOn p)] at hi
  obtain ⟨a, _, ha⟩ := hi
  exact ha ▸ hp a

lemma squareSum_cfc_right (F A : Matrix ι ι ℝ) (f : ℝ → ℝ) :
    squareSum (F * cfc f A) =
      Matrix.trace (F.transpose * F * cfc (fun a => (f a) ^ 2) A) := by
  rw [squareSum_trace, Matrix.transpose_mul, matrix_cfc_transpose]
  calc
    _ = Matrix.trace ((F.transpose * F) * (cfc f A * cfc f A)) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (cfc f A) (F.transpose * F * cfc f A)
    _ = _ := by
      rw [← cfc_mul f f A (A.finite_real_spectrum.continuousOn f)
        (A.finite_real_spectrum.continuousOn f)]
      simp only [pow_two]

lemma squareSum_cfc_inverse_sqrt (F A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (p : ℝ → ℝ) (hp : ∀ a, 0 < p a) :
    squareSum (F * cfc (fun a => (Real.sqrt (p a))⁻¹) A) =
      Matrix.trace (F.transpose * F * (cfc p A)⁻¹) := by
  rw [squareSum_cfc_right]
  have heq : (fun a => ((Real.sqrt (p a))⁻¹) ^ 2) = fun a => (p a)⁻¹ := by
    funext a
    rw [inv_pow, Real.sq_sqrt (hp a).le]
  rw [heq]
  apply congrArg (fun Z : Matrix ι ι ℝ => Matrix.trace (F.transpose * F * Z))
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact cfc_inv p A (fun a _ => ne_of_gt (hp a))
    (A.finite_real_spectrum.continuousOn p) hA.isSelfAdjoint

lemma squareSum_cfc_weighted (Y A : Matrix ι ι ℝ) (hY : Y.IsHermitian)
    (h p : ℝ → ℝ) (hp : ∀ a, 0 < p a) :
    squareSum (Y * cfc h A * cfc (fun a => (Real.sqrt (p a))⁻¹) A) =
      Matrix.trace (Y * Y * cfc (fun a => (h a) ^ 2 / p a) A) := by
  rw [Matrix.mul_assoc, ← cfc_mul h (fun a => (Real.sqrt (p a))⁻¹) A
    (A.finite_real_spectrum.continuousOn h)
    (A.finite_real_spectrum.continuousOn _), squareSum_cfc_right]
  have hYs : Y.transpose = Y := by simpa using hY.eq
  rw [hYs]
  apply congrArg (fun Z : Matrix ι ι ℝ => Matrix.trace (Y * Y * Z))
  apply cfc_congr
  intro a _
  dsimp only
  rw [mul_pow, inv_pow, Real.sq_sqrt (hp a).le, div_eq_mul_inv]

lemma squareSum_cfc_sub_const (Y A : Matrix ι ι ℝ) (hY : Y.IsHermitian)
    (hA : A.IsHermitian) (b : ℝ → ℝ) (β : ℝ) :
    squareSum (Y * (cfc b A - β • (1 : Matrix ι ι ℝ))) =
      Matrix.trace (Y * Y * cfc (fun a => (b a - β) ^ 2) A) := by
  have hc : cfc (fun _ : ℝ => β) A = β • (1 : Matrix ι ι ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using cfc_const β A hA.isSelfAdjoint
  have hsub : cfc b A - β • (1 : Matrix ι ι ℝ) = cfc (fun a => b a - β) A := by
    calc
      _ = cfc b A - cfc (fun _ : ℝ => β) A := congrArg (cfc b A - ·) hc.symm
      _ = _ := (cfc_sub b (fun _ => β) A (A.finite_real_spectrum.continuousOn b)
        (A.finite_real_spectrum.continuousOn _)).symm
  rw [hsub, squareSum_cfc_right]
  have hYs : Y.transpose = Y := by simpa using hY.eq
  rw [hYs]

/-- The two quadratic terms in `Y` have exactly the scalar absorption cost. -/
lemma cfc_cost_identity (Y A : Matrix ι ι ℝ) (hY : Y.IsHermitian) (hA : A.IsHermitian)
    (b h p : ℝ → ℝ) (hp : ∀ a, 0 < p a) :
    (40 / 37 : ℝ) * squareSum (Y * (cfc b A - (7 / 25 : ℝ) • 1)) +
      (40 / 37 : ℝ) * (5 / 96 : ℝ) *
        squareSum (Y * cfc h A * cfc (fun a => (Real.sqrt (p a))⁻¹) A) =
      Matrix.trace (Y * Y *
        cfc (fun a => (40 / 37) * ((b a - 7 / 25) ^ 2 + (5 / 96) * (h a) ^ 2 / p a)) A) := by
  rw [squareSum_cfc_sub_const Y A hY hA, squareSum_cfc_weighted Y A hY h p hp]
  have hadd := cfc_add (a := A) (fun a => (b a - 7 / 25) ^ 2)
    (fun a => (5 / 96) * (h a) ^ 2 / p a)
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  have hscale : cfc (fun a => (5 / 96) * (h a) ^ 2 / p a) A =
      (5 / 96 : ℝ) • cfc (fun a => (h a) ^ 2 / p a) A := by
    simpa only [mul_div_assoc] using cfc_const_mul (5 / 96 : ℝ)
      (fun a => (h a) ^ 2 / p a) A (A.finite_real_spectrum.continuousOn _)
  rw [cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _)]
  rw [hadd, hscale]
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  ring

end Submission.Obl.Entropy__noncommuting_remainder_assembly
