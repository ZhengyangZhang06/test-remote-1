import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedEllipticity

open Set Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Determinants and adjugates are polynomial maps, independently of the norm
chosen on the finite matrix space. -/
theorem matrix_det_contDiff {m : ℕ} {n : WithTop ENat} :
    ContDiff ℝ n (Matrix.det : Matrix (Fin m) (Fin m) ℝ → ℝ) := by
  change ContDiff ℝ n (fun M : Matrix (Fin m) (Fin m) ℝ => M.det)
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  fun_prop

theorem operatorMatrix_contDiff {m : ℕ} {n : WithTop ENat} :
    ContDiff ℝ n (operatorMatrix : (E m →L[ℝ] E m) → Matrix (Fin m) (Fin m) ℝ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [operatorMatrix, LinearMap.toMatrix_apply]
  change ContDiff ℝ n (fun A : E m →L[ℝ] E m =>
    (A ((EuclideanSpace.basisFun (Fin m) ℝ) j)) i)
  fun_prop

theorem operator_det_contDiff {m : ℕ} {n : WithTop ENat} :
    ContDiff ℝ n (fun A : E m →L[ℝ] E m => A.det) := by
  simpa only [Function.comp_def, operatorMatrix_det] using
    (matrix_det_contDiff (m := m) (n := n)).comp operatorMatrix_contDiff

theorem log_det_contDiffAt {m : ℕ} {n : WithTop ENat} {A : E m →L[ℝ] E m}
    (hA : A.det ≠ 0) : ContDiffAt ℝ n (fun B : E m →L[ℝ] E m => Real.log B.det) A :=
  operator_det_contDiff.contDiffAt.log hA

theorem matrix_adjugate_contDiff {m : ℕ} {n : WithTop ENat} :
    ContDiff ℝ n (Matrix.adjugate : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_det_contDiff.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hk]
    fun_prop

theorem linearizedTrace_contDiffAt {m : ℕ} {n : WithTop ENat} {A B : E m →L[ℝ] E m}
    (hA : A.det ≠ 0) :
    ContDiffAt ℝ n (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      linearizedTrace z.1 z.2) (A, B) := by
  have hl : ContDiff ℝ n (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      (operatorMatrix z.1).adjugate) := matrix_adjugate_contDiff.comp
        (operatorMatrix_contDiff.comp contDiff_fst)
  have hr : ContDiff ℝ n (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) => operatorMatrix z.2) :=
    operatorMatrix_contDiff.comp contDiff_snd
  have hnum : ContDiff ℝ n (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      Matrix.trace ((operatorMatrix z.1).adjugate * operatorMatrix z.2)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact ((contDiff_pi.mp (contDiff_pi.mp hl i)) j).mul
      ((contDiff_pi.mp (contDiff_pi.mp hr j)) i)
  have hden : ContDiffAt ℝ n (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      z.1.det⁻¹) (A, B) := (operator_det_contDiff.comp contDiff_fst).contDiffAt.inv hA
  convert! hden.mul hnum.contDiffAt using 1
  ext z
  simp only [linearizedTrace, Matrix.inv_def, Ring.inverse_eq_inv, operatorMatrix_det,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end Submission.Obl.Entropy__smooth_gaussian_transport
