import Mathlib
import Submission.Lib.EntropyTools.Remainder

/-!
# The first Gaussian chaos of a symmetric matrix field

The definitions in equation (3.5) of the supplied paper.  All expectations
are entrywise, as in the frozen interface of `normalized_remainder`.
-/

set_option backward.isDefEq.respectTransparency false

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

/-- A first-chaos field has no constant component. -/
theorem linearPart_mean {m : ℕ} (A : E m → Mat m) (i j : Fin m) :
    (∫ x, linearPart A x i j ∂stdGaussian (E m)) = 0 := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  erw [integral_finsetSum _ (fun r _ =>
    ((gaussian_coord_memLp r).integrable (by norm_num)).mul_const _)]
  simp [integral_mul_const, gaussian_coord_mean]

/-- Removing the first chaos preserves a vanishing mean. -/
theorem nonlinearPart_mean {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (hmean : ∀ i j, (∫ x, A x i j ∂stdGaussian (E m)) = 0) (i j : Fin m) :
    (∫ x, nonlinearPart A x i j ∂stdGaussian (E m)) = 0 := by
  change (∫ x, A x i j - linearPart A x i j ∂stdGaussian (E m)) = 0
  erw [integral_sub ((hA i j).integrable (by norm_num))
    ((linearPart_memLp A i j).integrable (by norm_num)), hmean, linearPart_mean, sub_self]

/-- Projection preserves every degree-one coefficient. -/
theorem linearPart_coord {m : ℕ} (A : E m → Mat m) (r i j : Fin m) :
    (∫ x, x r * linearPart A x i j ∂stdGaussian (E m)) = firstCoeff A r i j := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← mul_assoc]
  erw [integral_finsetSum _ (fun s _ =>
    ((gaussian_coord_memLp r).integrable_mul (gaussian_coord_memLp s)).mul_const _)]
  simp [integral_mul_const, gaussian_coord_mul, ite_mul]

/-- The remainder is orthogonal to every coordinate function. -/
theorem nonlinearPart_coord {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (r i j : Fin m) :
    (∫ x, x r * nonlinearPart A x i j ∂stdGaussian (E m)) = 0 := by
  change (∫ x, x r * (A x i j - linearPart A x i j) ∂stdGaussian (E m)) = 0
  simp only [mul_sub]
  erw [integral_sub (firstCoeff_integrable hA r i j)
    ((gaussian_coord_memLp r).integrable_mul (linearPart_memLp A i j)),
    linearPart_coord]
  simp only [firstCoeff, Matrix.of_apply, sub_self]

/-- Each entry of the remainder is orthogonal to every entry of the linear part. -/
theorem nonlinearPart_linearPart {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (i j k l : Fin m) :
    (∫ x, nonlinearPart A x i j * linearPart A x k l ∂stdGaussian (E m)) = 0 := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← mul_assoc]
  erw [integral_finsetSum _ (fun r _ =>
    ((nonlinearPart_memLp hA i j).integrable_mul (gaussian_coord_memLp r)).mul_const _)]
  simp only [integral_mul_const]
  have hzero (r : Fin m) :
      (∫ x, nonlinearPart A x i j * x r ∂stdGaussian (E m)) = 0 := by
    simpa only [mul_comm] using nonlinearPart_coord hA r i j
  simp [hzero]

/-- The Gram product of two projected entries is the product of their coefficients. -/
theorem linearPart_mul {m : ℕ} (A : E m → Mat m) (i j k l : Fin m) :
    (∫ x, linearPart A x i j * linearPart A x k l ∂stdGaussian (E m)) =
      ∑ r, firstCoeff A r i j * firstCoeff A r k l := by
  change (∫ x, linearPart A x i j *
    (∑ r, x r • firstCoeff A r) k l ∂stdGaussian (E m)) = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  erw [integral_finsetSum _ (fun r _ =>
    ((linearPart_memLp A i j).integrable_mul (gaussian_coord_memLp r)).mul_const _)]
  apply Finset.sum_congr rfl
  intro r _
  erw [integral_mul_const]
  congr 1
  change (∫ x, linearPart A x i j * x r ∂stdGaussian (E m)) = firstCoeff A r i j
  simpa only [mul_comm] using linearPart_coord A r i j

/-- Orthogonality gives the entrywise second-moment decomposition. -/
theorem entry_second_moment {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (i j k l : Fin m) :
    (∫ x, A x i j * A x k l ∂stdGaussian (E m)) =
      (∑ r, firstCoeff A r i j * firstCoeff A r k l) +
      ∫ x, nonlinearPart A x i j * nonlinearPart A x k l ∂stdGaussian (E m) := by
  have hexpand (x : E m) : A x i j * A x k l =
      linearPart A x i j * linearPart A x k l +
      nonlinearPart A x i j * linearPart A x k l +
      nonlinearPart A x k l * linearPart A x i j +
      nonlinearPart A x i j * nonlinearPart A x k l := by
    simp only [nonlinearPart, Matrix.sub_apply]
    ring
  simp_rw [hexpand]
  have hLL := (linearPart_memLp A i j).integrable_mul (linearPart_memLp A k l)
  have hYL := (nonlinearPart_memLp hA i j).integrable_mul (linearPart_memLp A k l)
  have hLY := (nonlinearPart_memLp hA k l).integrable_mul (linearPart_memLp A i j)
  have hYY := (nonlinearPart_memLp hA i j).integrable_mul (nonlinearPart_memLp hA k l)
  erw [integral_add ((hLL.add hYL).add hLY) hYY,
    integral_add (hLL.add hYL) hLY, integral_add hLL hYL,
    nonlinearPart_linearPart hA, nonlinearPart_linearPart hA, linearPart_mul]
  simp

/-- The matrix identity used for the expected spectral measure in Proposition 3.5. -/
theorem matrix_second_moment {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m))) :
    (Matrix.of fun i j => ∫ x, (A x * A x) i j ∂stdGaussian (E m)) =
      firstGram A + Matrix.of (fun i j =>
        ∫ x, (nonlinearPart A x * nonlinearPart A x) i j ∂stdGaussian (E m)) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  erw [integral_finsetSum _ (fun k _ => (hA i k).integrable_mul (hA k j)),
    integral_finsetSum _ (fun k _ =>
      (nonlinearPart_memLp hA i k).integrable_mul (nonlinearPart_memLp hA k j))]
  change (∑ k, ∫ x, A x i k * A x k j ∂stdGaussian (E m)) =
    firstGram A i j + ∑ k, ∫ x, nonlinearPart A x i k * nonlinearPart A x k j
      ∂stdGaussian (E m)
  simp_rw [entry_second_moment hA]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [firstGram, Matrix.sum_apply, Matrix.mul_apply]
  exact Finset.sum_comm

end Submission.Obl.Entropy__normalized_remainder
