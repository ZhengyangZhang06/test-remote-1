import Mathlib

/-! Matrix spectral bookkeeping for the first-chaos absorption estimate.
The matrix order is used only for positive quadratic forms; no commutation
between the field and the first-chaos Gram matrix is assumed. -/

open Matrix
open scoped BigOperators MatrixOrder

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal quadratic forms in a fixed orthonormal basis. -/
noncomputable def basisDiag (U : unitary (Matrix n n ℝ)) (M : Matrix n n ℝ) (i : n) : ℝ :=
  (star (U : Matrix n n ℝ) * M * (U : Matrix n n ℝ)) i i

lemma basisDiag_add (U : unitary (Matrix n n ℝ)) (M N : Matrix n n ℝ) (i : n) :
    basisDiag U (M + N) i = basisDiag U M i + basisDiag U N i := by
  simp [basisDiag, mul_add, add_mul]

lemma basisDiag_sub (U : unitary (Matrix n n ℝ)) (M N : Matrix n n ℝ) (i : n) :
    basisDiag U (M - N) i = basisDiag U M i - basisDiag U N i := by
  simp [basisDiag, mul_sub, sub_mul]

lemma basisDiag_smul (U : unitary (Matrix n n ℝ)) (c : ℝ) (M : Matrix n n ℝ) (i : n) :
    basisDiag U (c • M) i = c * basisDiag U M i := by
  simp [basisDiag]

lemma basisDiag_one (U : unitary (Matrix n n ℝ)) (i : n) :
    basisDiag U 1 i = 1 := by
  simp [basisDiag]

lemma basisDiag_zero (U : unitary (Matrix n n ℝ)) (i : n) :
    basisDiag U 0 i = 0 := by
  simp [basisDiag]

lemma basisDiag_nonneg (U : unitary (Matrix n n ℝ)) {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (i : n) : 0 ≤ basisDiag U M i := by
  exact (hM.conjTranspose_mul_mul_same (U : Matrix n n ℝ)).diag_nonneg

lemma basisDiag_mono (U : unitary (Matrix n n ℝ)) {M N : Matrix n n ℝ}
    (hMN : M ≤ N) (i : n) : basisDiag U M i ≤ basisDiag U N i := by
  have h := basisDiag_nonneg U hMN i
  rw [basisDiag_sub] at h
  linarith

lemma sum_basisDiag (U : unitary (Matrix n n ℝ)) (M : Matrix n n ℝ) :
    ∑ i, basisDiag U M i = M.trace := by
  change (star (U : Matrix n n ℝ) * M * (U : Matrix n n ℝ)).trace = _
  rw [Matrix.trace_mul_cycle]
  simp

lemma basisDiag_self {B : Matrix n n ℝ} (hB : B.IsHermitian) (i : n) :
    basisDiag hB.eigenvectorUnitary B i = hB.eigenvalues i := by
  have h := hB.conjStarAlgAut_star_eigenvectorUnitary
  simpa [basisDiag, Unitary.conjStarAlgAut_apply, Function.comp_def] using congrArg (fun M => M i i) h

lemma trace_cfc_mul {B : Matrix n n ℝ} (hB : B.IsHermitian) (f : ℝ → ℝ)
    (M : Matrix n n ℝ) :
    (cfc f B * M).trace = ∑ i, f (hB.eigenvalues i) * basisDiag hB.eigenvectorUnitary M i := by
  let U := hB.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal (f ∘ hB.eigenvalues)
  have hcf : cfc f B = (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) := by
    simp [hB.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      U, D, Function.comp_def]
  rw [hcf]
  calc
    _ = (D * (star (U : Matrix n n ℝ) * M * (U : Matrix n n ℝ))).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (U : Matrix n n ℝ) (D * star (U : Matrix n n ℝ) * M)
    _ = _ := by simp [D, U, Matrix.trace, Matrix.diagonal_mul, basisDiag]

lemma trace_cfc {B : Matrix n n ℝ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (cfc f B).trace = ∑ i, f (hB.eigenvalues i) := by
  simpa only [mul_one, basisDiag_one] using trace_cfc_mul hB f 1

lemma cfc_quadratic {A : Matrix n n ℝ} (hA : A.IsHermitian) (u v d : ℝ) :
    cfc (fun a => u + v * a - d * a ^ 2) A =
      u • (1 : Matrix n n ℝ) + v • A - d • (A * A) := by
  rw [cfc_sub (fun a => u + v * a) (fun a => d * a ^ 2) A (by fun_prop) (by fun_prop),
    cfc_add A (fun _ => u) (fun a => v * a) (by fun_prop) (by fun_prop),
    cfc_const u A hA.isSelfAdjoint, cfc_const_mul (p := IsSelfAdjoint) v (fun a : ℝ => a) A (by fun_prop),
    cfc_const_mul (p := IsSelfAdjoint) d (fun a : ℝ => a ^ 2) A (by fun_prop),
    cfc_pow (fun a : ℝ => a) 2 A (by fun_prop) hA.isSelfAdjoint]
  have hid : cfc (fun a : ℝ => a) A = A := cfc_id ℝ A hA.isSelfAdjoint
  rw [hid]
  simp only [Algebra.algebraMap_eq_smul_one, pow_two]

lemma quadratic_minorant_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {p : ℝ → ℝ} {u v d : ℝ} (hp : ∀ a, u + v * a - d * a ^ 2 ≤ p a) :
    u • (1 : Matrix n n ℝ) + v • A - d • (A * A) ≤ cfc p A := by
  rw [← cfc_quadratic hA]
  exact (cfc_le_iff _ _ A ((Matrix.finite_spectrum A).continuousOn _)
    ((Matrix.finite_spectrum A).continuousOn _) hA.isSelfAdjoint).mpr fun a _ => hp a

lemma trace_mul_cfc_le {A Y : Matrix n n ℝ} (hA : A.IsHermitian) (hY : Y.IsHermitian)
    {c : ℝ} {f : ℝ → ℝ} (hf : ∀ a, f a ≤ c) :
    (Y * Y * cfc f A).trace ≤ c * (Y * Y).trace := by
  have hle : cfc f A ≤ c • (1 : Matrix n n ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      cfc_le_algebraMap f c A (fun a _ => hf a) ((Matrix.finite_spectrum A).continuousOn _) hA.isSelfAdjoint
  have hpos := (Matrix.le_iff.mp hle).mul_mul_conjTranspose_same Y
  have ht := hpos.trace_nonneg
  rw [mul_sub, sub_mul, Matrix.trace_sub, mul_smul_comm, mul_one,
    smul_mul_assoc, Matrix.trace_smul] at ht
  rw [hY.eq] at ht
  rw [Matrix.trace_mul_cycle] at ht
  simpa only [smul_eq_mul] using sub_nonneg.mp ht

end Submission.Obl.Entropy__first_chaos_absorption
