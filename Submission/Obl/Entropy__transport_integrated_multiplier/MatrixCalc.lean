import Submission.Lib.MatrixEntropy.Completion

open scoped BigOperators ContDiff

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma isHermitian_entry_derivative {F : E → Matrix ι ι ℝ}
    (hF : ∀ x, (F x).IsHermitian) (x v : E) :
    (Matrix.of fun i j => fderiv ℝ (fun y => F y i j) x v).IsHermitian := by
  have he (i j : ι) : (fun y => F y j i) = (fun y => F y i j) := by
    funext y
    exact (hF y).apply i j
  ext i j
  simpa only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, he]

lemma fderiv_matrix_square {Q : E → Matrix ι ι ℝ}
    (hQ : ∀ i j, Differentiable ℝ (fun x => Q x i j)) (x v : E) (i j : ι) :
    fderiv ℝ (fun y => (Q y * Q y) i j) x v =
      ((Matrix.of fun a b => fderiv ℝ (fun y => Q y a b) x v) * Q x +
        Q x * (Matrix.of fun a b => fderiv ℝ (fun y => Q y a b) x v)) i j := by
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
  erw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => Q y i k * Q y k j)
    (fun k _ => (hQ i k x).mul (hQ k j x)), sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hd := fderiv_mul (hQ i k x) (hQ k j x)
  have hv := congrArg (fun L => L v) hd
  change fderiv ℝ (fun y => Q y i k * Q y k j) x v = _ at hv
  simpa only [add_apply, smul_apply, smul_eq_mul, mul_comm, add_comm] using hv

lemma contDiff_matrix_square {Q : E → Matrix ι ι ℝ}
    (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => (Q x * Q x) i j) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hQ i k).mul (hQ k j)

lemma square_isHermitian {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    (Q * Q).IsHermitian := by
  simpa only [hQ.eq] using (Matrix.posSemidef_conjTranspose_mul_self Q).isHermitian

lemma square_curvature_nonneg {Q B : Matrix ι ι ℝ}
    (hQ : Q.IsHermitian) (hB : B.PosSemidef) :
    0 ≤ ∑ i, ∑ j, (Q * Q) i j * B i j := by
  have hP : (Q * Q).PosSemidef := by
    simpa only [hQ.eq] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hsym : (Q * Q).transpose = Q * Q := by simpa using hP.isHermitian.eq
  rw [← Submission.Lib.MatrixEntropy.trace_transpose_mul, hsym]
  exact Submission.Lib.MatrixEntropy.trace_mul_nonneg_of_posSemidef hP hB

lemma square_trace_entries {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    (Q * Q).trace = ∑ i, ∑ j, (Q i j)^2 := by
  have hsym : Q.transpose = Q := by simpa using hQ.eq
  calc
    _ = (Q.transpose * Q).trace := by rw [hsym]
    _ = _ := by rw [Submission.Lib.MatrixEntropy.trace_transpose_mul]; simp only [pow_two]

lemma trace_mul_entries_right {P H : Matrix ι ι ℝ} (hH : H.IsHermitian) :
    Matrix.trace (P * H) = ∑ i, ∑ j, P i j * H i j := by
  have hsym : H.transpose = H := by simpa using hH.eq
  calc
    _ = (H.transpose * P).trace := by rw [hsym, Matrix.trace_mul_comm]
    _ = _ := by rw [Submission.Lib.MatrixEntropy.trace_transpose_mul]; simp only [mul_comm]

end Submission.Obl.Entropy__transport_integrated_multiplier
