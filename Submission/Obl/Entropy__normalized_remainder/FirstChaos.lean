import Mathlib
import Submission.Lib.EntropyTools.Remainder

/-!
# The first Gaussian chaos of a symmetric matrix field

The definitions in equation (3.5) of the supplied paper.  All expectations
are entrywise, as in the frozen interface of `normalized_remainder`.
-/

namespace Submission.Obl.Entropy__normalized_remainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

noncomputable def firstCoeff {m : ℕ} (A : E m → Mat m) (r : Fin m) : Mat m :=
  Matrix.of fun i j => ∫ x, x r * A x i j ∂stdGaussian (E m)

noncomputable def linearPart {m : ℕ} (A : E m → Mat m) (x : E m) : Mat m :=
  ∑ r, x r • firstCoeff A r

noncomputable def nonlinearPart {m : ℕ} (A : E m → Mat m) (x : E m) : Mat m :=
  A x - linearPart A x

noncomputable def firstGram {m : ℕ} (A : E m → Mat m) : Mat m :=
  ∑ r, firstCoeff A r * firstCoeff A r

noncomputable def fieldEnergy {m : ℕ} (A : E m → Mat m) : ℝ :=
  ∫ x, ∑ i, ∑ j, (A x i j) ^ 2 ∂stdGaussian (E m)

/-- The first-chaos coefficients inherit symmetry without any integrability premise. -/
theorem firstCoeff_isHermitian {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (r : Fin m) :
    (firstCoeff A r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [firstCoeff, Matrix.of_apply, star_trivial]
  congr 1
  funext x
  rw [show A x j i = A x i j by simpa using (hA x).apply i j]

/-- The matrix whose spectrum enters the strict remainder is positive semidefinite. -/
theorem firstGram_posSemidef {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) : (firstGram A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r _
  have h := Matrix.posSemidef_conjTranspose_mul_self (firstCoeff A r)
  rwa [(firstCoeff_isHermitian hA r).eq] at h

theorem linearPart_isHermitian {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (x : E m) : (linearPart A x).IsHermitian := by
  exact isSelfAdjoint_sum _ fun r _ =>
    (firstCoeff_isHermitian hA r).smul (show IsSelfAdjoint (x r) from isSelfAdjoint_iff.mpr rfl)

theorem nonlinearPart_isHermitian {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (x : E m) : (nonlinearPart A x).IsHermitian :=
  (hA x).sub (linearPart_isHermitian hA x)

theorem fieldEnergy_nonneg {m : ℕ} (A : E m → Mat m) : 0 ≤ fieldEnergy A := by
  apply integral_nonneg
  intro x
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Entry-square energy is the trace energy used in the paper. -/
theorem trace_square_eq {m : ℕ} {M : Mat m} (hM : M.IsHermitian) :
    Matrix.trace (M * M) = ∑ i, ∑ j, (M i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show M j i = M i j by simpa using hM.apply i j, pow_two]

/-- Every summand in the spectral remainder is nonnegative. -/
theorem firstGram_weight_nonneg {m : ℕ} {A : E m → Mat m}
    (hB : (firstGram A).PosSemidef) :
    0 ≤ ∑ i, Submission.Lib.EntropyTools.rigidityWeight (hB.isHermitian.eigenvalues i) := by
  exact Finset.sum_nonneg fun i _ =>
    Submission.Lib.EntropyTools.rigidityWeight_nonneg (hB.eigenvalues_nonneg i)

/-- Each coordinate is square-integrable under the standard Gaussian. -/
theorem gaussian_coord_memLp {m : ℕ} (i : Fin m) :
    MemLp (fun x : E m => x i) 2 (stdGaussian (E m)) := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp'
    (IsGaussian.memLp_two_id (μ := stdGaussian (E m)))

/-- Gaussian coordinates have mean zero. -/
theorem gaussian_coord_mean {m : ℕ} (i : Fin m) :
    (∫ x : E m, x i ∂stdGaussian (E m)) = 0 := by
  exact integral_strongDual_stdGaussian (EuclideanSpace.proj i)

/-- The coordinate covariance of the standard Gaussian is the identity. -/
theorem gaussian_coord_mul {m : ℕ} (i j : Fin m) :
    (∫ x : E m, x i * x j ∂stdGaussian (E m)) = if i = j then 1 else 0 := by
  have h := covariance_eval_multivariateGaussian
    (μ := (0 : E m)) (S := (1 : Mat m)) Matrix.PosSemidef.one i j
  rw [multivariateGaussian_zero_one,
    covariance_eq_sub (gaussian_coord_memLp i) (gaussian_coord_memLp j),
    gaussian_coord_mean, gaussian_coord_mean] at h
  simpa [Matrix.one_apply] using h

/-- Bounded continuous entries satisfy the integrability needed for projection. -/
theorem entry_memLp_of_bounded {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Continuous (fun x => A x i j))
    (hbound : ∃ R : ℝ, ∀ x i j, |A x i j| ≤ R) (i j : Fin m) :
    MemLp (fun x => A x i j) 2 (stdGaussian (E m)) := by
  obtain ⟨R, hR⟩ := hbound
  exact MemLp.of_bound (hA i j).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hR x i j)

/-- The integral defining every first-chaos coefficient is a genuine integral. -/
theorem firstCoeff_integrable {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (r i j : Fin m) : Integrable (fun x => x r * A x i j) (stdGaussian (E m)) := by
  exact (gaussian_coord_memLp r).integrable_mul (hA i j)

/-- Each entry of the linear projection is square-integrable. -/
theorem linearPart_memLp {m : ℕ} (A : E m → Mat m) (i j : Fin m) :
    MemLp (fun x => linearPart A x i j) 2 (stdGaussian (E m)) := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact memLp_finsetSum _ fun r _ => (gaussian_coord_memLp r).mul_const _

/-- The remainder is square-integrable whenever the original entries are. -/
theorem nonlinearPart_memLp {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m))) (i j : Fin m) :
    MemLp (fun x => nonlinearPart A x i j) 2 (stdGaussian (E m)) :=
  (hA i j).sub (linearPart_memLp A i j)

/-- The entry-square energy is integrable for a square-integrable matrix field. -/
theorem fieldEnergy_integrable {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m))) :
    Integrable (fun x => ∑ i, ∑ j, (A x i j) ^ 2) (stdGaussian (E m)) := by
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hA i j).integrable_sq

end Submission.Obl.Entropy__normalized_remainder
