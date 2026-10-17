import Submission.Lib.MatrixEntropy.Squares

open MeasureTheory
open scoped BigOperators MatrixOrder Matrix

namespace Submission.Obl.Entropy__gaussian_covariance_variational

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m : ℕ}

lemma memLp_row (H : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hH : ∀ i j, MemLp (fun x => H x i j) 2 μ) (u : Fin m → ℝ) (j : Fin m) :
    MemLp (fun x => ∑ i, u i * H x i j) 2 μ :=
  memLp_finsetSum _ fun i _ => (hH i j).const_mul (u i)

lemma trace_row_quadratic (R C : Matrix (Fin m) (Fin m) ℝ) :
    (R.transpose * R * C).trace = ∑ i, (R i) ⬝ᵥ (C *ᵥ (R i)) := by
  rw [← Matrix.trace_mul_cycle R C R.transpose]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma integral_weighted_square (R : Matrix (Fin m) (Fin m) ℝ)
    (H : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hH : ∀ i j, MemLp (fun x => H x i j) 2 μ) :
    (∫ x, ((H x).transpose * (R.transpose * R) * H x).trace ∂μ) =
      ∑ i, ∑ j, ∫ x, (∑ k, R i k * H x k j) ^ 2 ∂μ := by
  have he (x : Ω) : ((H x).transpose * (R.transpose * R) * H x).trace =
      ∑ i, ∑ j, (∑ k, R i k * H x k j) ^ 2 := by
    rw [show (H x).transpose * (R.transpose * R) * H x =
      (R * H x).transpose * (R * H x) by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]]
    simp only [Submission.Lib.MatrixEntropy.trace_transpose_mul, Matrix.mul_apply, pow_two]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (memLp_row H hH (R i) j).integrable_sq)]
  congr 1
  funext i
  exact integral_finsetSum _ fun j _ => (memLp_row H hH (R i) j).integrable_sq

/-- Scalar quadratic bounds imply the bound with every positive matrix weight. -/
theorem weighted_bound_of_quadratic_bound
    (C : Matrix (Fin m) (Fin m) ℝ)
    (a : Ω → Matrix (Fin m) (Fin m) ℝ)
    (b : Fin m → Ω → Matrix (Fin m) (Fin m) ℝ)
    (ha : ∀ i j, MemLp (fun x => a x i j) 2 μ)
    (hb : ∀ r i j, MemLp (fun x => b r x i j) 2 μ)
    (hq : ∀ u : Fin m → ℝ, u ⬝ᵥ (C *ᵥ u) ≤
      (∑ j, ∫ x, (∑ i, u i * a x i j)^2 ∂μ) +
      ∑ r, ∑ j, ∫ x, (∑ i, u i * b r x i j)^2 ∂μ)
    (P : Matrix (Fin m) (Fin m) ℝ) (hP : P.PosDef) :
    (P * C).trace ≤ (∫ x, ((a x).transpose * P * a x).trace ∂μ) +
      ∑ r, ∫ x, ((b r x).transpose * P * b r x).trace ∂μ := by
  let R := CFC.sqrt P
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hsym : R.transpose = R := by simpa using hR.isHermitian.eq
  have hRR : R.transpose * R = P := by
    rw [hsym]
    exact CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  rw [← hRR, trace_row_quadratic, integral_weighted_square R a ha]
  have he (r : Fin m) := integral_weighted_square R (b r) (hb r)
  simp_rw [he]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hq (R i))
  rw [Finset.sum_add_distrib] at h
  simpa only [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin m)))
    (f := fun i r => ∑ j, ∫ x, (∑ k, R i k * b r x k j)^2 ∂μ)] using h

end Submission.Obl.Entropy__gaussian_covariance_variational
