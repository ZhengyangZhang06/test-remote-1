/-
Adapted from: here:o021
Original proofs by session x0046.
-/

import Submission.Lib.SpectralAbsorption.Spectral

open Matrix
open scoped BigOperators MatrixOrder

namespace Submission.Lib.SpectralAbsorption

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cfc_mul_any (B : Matrix n n ℝ) (f g : ℝ → ℝ) :
    cfc (fun z => f z * g z) B = cfc f B * cfc g B :=
  cfc_mul f g B ((Matrix.finite_spectrum B).continuousOn _)
    ((Matrix.finite_spectrum B).continuousOn _)

lemma cfc_add_any (B : Matrix n n ℝ) (f g : ℝ → ℝ) :
    cfc (fun z => f z + g z) B = cfc f B + cfc g B :=
  cfc_add B f g ((Matrix.finite_spectrum B).continuousOn _)
    ((Matrix.finite_spectrum B).continuousOn _)

lemma cfc_sub_any (B : Matrix n n ℝ) (f g : ℝ → ℝ) :
    cfc (fun z => f z - g z) B = cfc f B - cfc g B :=
  cfc_sub f g B ((Matrix.finite_spectrum B).continuousOn _)
    ((Matrix.finite_spectrum B).continuousOn _)

lemma cfc_const_mul_any (B : Matrix n n ℝ) (c : ℝ) (f : ℝ → ℝ) :
    cfc (fun z => c * f z) B = c • cfc f B :=
  cfc_const_mul c f B ((Matrix.finite_spectrum B).continuousOn _)

lemma cfc_const_eq {B : Matrix n n ℝ} (hB : B.IsHermitian) (c : ℝ) :
    cfc (fun _ : ℝ => c) B = c • (1 : Matrix n n ℝ) := by
  rw [cfc_const c B hB.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

lemma cfc_id_eq {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    cfc (fun z : ℝ => z) B = B := cfc_id ℝ B hB.isSelfAdjoint

lemma cfc_neg_any (B : Matrix n n ℝ) (f : ℝ → ℝ) :
    cfc (fun z => -f z) B = -cfc f B :=
  cfc_neg f B

lemma cfc_affine {B : Matrix n n ℝ} (hB : B.IsHermitian) (a b : ℝ) :
    cfc (fun z => a + b * z) B = a • (1 : Matrix n n ℝ) + b • B := by
  rw [cfc_add_any, cfc_const_mul_any, cfc_const_eq hB, cfc_id_eq hB]

lemma inverse_affine_eq_cfc {B : Matrix n n ℝ} (hB : B.IsHermitian) (a b : ℝ)
    (hn : ∀ i, a + b * hB.eigenvalues i ≠ 0) :
    (a • (1 : Matrix n n ℝ) + b • B)⁻¹ = cfc (fun z => (a + b * z)⁻¹) B := by
  apply Matrix.inv_eq_right_inv
  rw [← cfc_affine hB, ← cfc_mul_any]
  have heq : cfc (fun z => (a + b * z) * (a + b * z)⁻¹) B = cfc (fun _ : ℝ => 1) B := by
    apply cfc_congr
    intro z hz
    rw [hB.spectrum_real_eq_range_eigenvalues] at hz
    obtain ⟨i, rfl⟩ := hz
    exact mul_inv_cancel₀ (hn i)
  rw [heq, cfc_const_eq hB]
  simp

lemma det_cfc {B : Matrix n n ℝ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (cfc f B).det = ∏ i, f (hB.eigenvalues i) := by
  rw [hB.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.det_mul, Matrix.det_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  calc
    _ = (∏ i, f (hB.eigenvalues i)) *
        ((hB.eigenvectorUnitary : Matrix n n ℝ).det *
          (star (hB.eigenvectorUnitary : Matrix n n ℝ)).det) := by ring
    _ = _ := by rw [← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one, mul_one]

lemma logarithmic_cost_eq_sum {B : Matrix n n ℝ} (hB : B.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, f (hB.eigenvalues i) ≠ 0) :
    (cfc f B - 1).trace - Real.log (cfc f B).det =
      ∑ i, (f (hB.eigenvalues i) - 1 - Real.log (f (hB.eigenvalues i))) := by
  rw [Matrix.trace_sub, trace_cfc hB, det_cfc hB, Real.log_prod (fun i _ => hf i)]
  simp [Finset.sum_sub_distrib, Matrix.trace_one]

/-- The matrix coefficient Hρ is a function of B, although p(A) need not
commute with B. This is the exact coefficient occurring in the frozen goal. -/
lemma dual_weight_eq_cfc {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    let S := ((37/40 : ℝ) • (1 : Matrix n n ℝ) + (3/40 : ℝ) • B)⁻¹
    (-(S - 1) * (B - 1)) * ((3/20 : ℝ) • 1 + (1813/4000 : ℝ) • S) =
      cfc (fun z : ℝ => -((37/40 + (3/40)*z)⁻¹ - 1) * (z - 1) *
        (3/20 + (1813/4000)*(37/40 + (3/40)*z)⁻¹)) B := by
  dsimp only
  have hi := inverse_affine_eq_cfc hB.isHermitian (37/40) (3/40)
    (fun i => ne_of_gt (by have := hB.eigenvalues_nonneg i; positivity))
  rw [hi]
  simp only [cfc_mul_any, cfc_neg_any, cfc_sub_any, cfc_add_any, cfc_const_mul_any,
    cfc_const_eq hB.isHermitian, cfc_id_eq hB.isHermitian, one_smul, smul_mul_assoc, one_mul]

end Submission.Lib.SpectralAbsorption
