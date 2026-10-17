/-
Adapted from: here:o006
Original proofs by session x0062.
-/

import Submission.Lib.EntropyRemainder.WeakMatrix

/-! # Matrix integration by parts for the first chaos -/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma expectation_linearPart_mul {m : ℕ} (A : E m → Mat m) {f : E m → ℝ}
    (hf : Differentiable ℝ f) (hfL : MemLp f 2 (stdGaussian (E m)))
    (hdf : ∀ r, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))
      2 (stdGaussian (E m))) (i j : Fin m) :
    expectation (fun x => linearPart A x i j * f x) =
      ∑ r, firstCoeff A r i j *
        expectation (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, expectation]
  have hi (r : Fin m) : Integrable (fun x => x r * firstCoeff A r i j * f x)
      (stdGaussian (E m)) := by
    simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using!
      ((gaussian_coord_memLp r).integrable_mul hfL).const_mul (firstCoeff A r i j)
  rw [integral_finsetSum _ (fun r _ => hi r)]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [show ∀ x : E m, x r * firstCoeff A r i j * f x =
      firstCoeff A r i j * (x r * f x) by intro x; ring]
  rw [integral_const_mul, ← gaussian_integral_coordinateDerivative hf hfL r (hdf r)]

lemma expectation_firstChaos_mul {m : ℕ} {A : E m → Mat m} {f : E m → ℝ}
    (hA : SquareIntegrable A) (hf : Differentiable ℝ f)
    (hfL : MemLp f 2 (stdGaussian (E m)))
    (hdf : ∀ r, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))
      2 (stdGaussian (E m))) (i j : Fin m) :
    expectation (fun x => A x i j * f x) =
      expectation (fun x => nonlinearPart A x i j * f x) +
      ∑ r, firstCoeff A r i j *
        expectation (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) := by
  rw [← expectation_linearPart_mul A hf hfL hdf i j]
  unfold expectation
  erw [← integral_add ((nonlinearPart_memLp hA i j).integrable_mul hfL)
    ((linearPart_memLp A i j).integrable_mul hfL)]
  congr 1
  funext x
  simp [nonlinearPart, Matrix.sub_apply]
  ring

/-- Gaussian IBP on the linear part retains the order of all matrix factors. -/
theorem firstChaos_trace_integration_by_parts {m : ℕ} {A H : E m → Mat m}
    (hA : SquareIntegrable A) (hH : ∀ i j, Differentiable ℝ (fun x => H x i j))
    (hHL : SquareIntegrable H) (hHD : ∀ r, SquareIntegrable (coordinateDerivative H r))
    (T : Mat m) :
    expectation (fun x => Matrix.trace (T * A x * H x)) =
      expectation (fun x => Matrix.trace (T * nonlinearPart A x * H x)) +
      ∑ r, expectation (fun x => Matrix.trace (T * firstCoeff A r * coordinateDerivative H r x)) := by
  have hTF := squareIntegrable_const_mul T hA
  have hTY := squareIntegrable_const_mul T (nonlinearPart_memLp hA)
  rw [expectation_trace_mul hTF hHL, expectation_trace_mul hTY hHL]
  have hentry (i j : Fin m) :
      expectation (fun x => (T * A x) i j * H x j i) =
        expectation (fun x => (T * nonlinearPart A x) i j * H x j i) +
        ∑ r, expectation (fun x => (T * firstCoeff A r) i j * coordinateDerivative H r x j i) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, expectation]
    erw [integral_finsetSum _ (fun k _ => ((hA k j).const_mul (T i k)).integrable_mul (hHL j i)),
      integral_finsetSum _ (fun k _ =>
        ((nonlinearPart_memLp hA k j).const_mul (T i k)).integrable_mul (hHL j i))]
    simp only [Pi.mul_apply, mul_assoc, integral_const_mul]
    have he (k : Fin m) := expectation_firstChaos_mul hA (hH j i) (hHL j i)
      (fun r => hHD r j i) k j
    simp only [expectation] at he
    simp_rw [he, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    erw [integral_finsetSum _ (fun k _ => (((hHD r j i).integrable (by norm_num)).const_mul (firstCoeff A r k j)).const_mul (T i k))]
    simp only [integral_const_mul, coordinateDerivative, Matrix.of_apply]
  simp_rw [hentry, Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ i, ∑ r, ∑ j, expectation (fun x =>
        (T * firstCoeff A r) i j * coordinateDerivative H r x j i) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, expectation (fun x =>
        (T * firstCoeff A r) i j * coordinateDerivative H r x j i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact (expectation_trace_mul (fun i j => memLp_const ((T * firstCoeff A r) i j)) (hHD r)).symm

end Submission.Lib.EntropyRemainder
