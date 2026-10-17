import Submission.Obl.Entropy__normalized_remainder.GaussianIBP
import Submission.Obl.Entropy__normalized_remainder.Interfaces

/-!
# Differentiating the first Gaussian chaos

The first-chaos split is orthogonal both in L2 and in the Gaussian derivative
energy. The degree-one contributions therefore cancel in their difference.
-/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__normalized_remainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma linearPart_contDiff {m : ℕ} (A : E m → Mat m) (i j : Fin m)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun x => linearPart A x i j) := by
  simp only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact ContDiff.sum fun r _ => (EuclideanSpace.proj (𝕜 := ℝ) r).contDiff.mul contDiff_const

lemma nonlinearPart_contDiff {m : ℕ} {A : E m → Mat m} {n : WithTop ℕ∞}
    (hA : ∀ i j, ContDiff ℝ n (fun x => A x i j)) (i j : Fin m) :
    ContDiff ℝ n (fun x => nonlinearPart A x i j) :=
  (hA i j).sub (linearPart_contDiff A i j)

lemma coordinateDerivative_linearPart {m : ℕ} (A : E m → Mat m)
    (r : Fin m) (x : E m) : coordinateDerivative (linearPart A) r x = firstCoeff A r := by
  ext i j
  have h : HasFDerivAt (fun y : E m => linearPart A y i j)
      (∑ s, firstCoeff A s i j • EuclideanSpace.proj (𝕜 := ℝ) s) x := by
    simpa only [linearPart, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      using! HasFDerivAt.fun_sum (fun s (_ : s ∈ Finset.univ) =>
        (EuclideanSpace.proj (𝕜 := ℝ) s).hasFDerivAt.mul_const (firstCoeff A s i j))
  change fderiv ℝ (fun y => linearPart A y i j) x (PiLp.single 2 r (1 : ℝ)) = _
  rw [h.fderiv]
  simp [EuclideanSpace.proj, PiLp.single_apply]

lemma coordinateDerivative_nonlinearPart {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (r : Fin m) (x : E m) :
    coordinateDerivative (nonlinearPart A) r x = coordinateDerivative A r x - firstCoeff A r := by
  rw [← coordinateDerivative_linearPart A r x]
  ext i j
  change fderiv ℝ (fun y => A y i j - linearPart A y i j) x _ =
    fderiv ℝ (fun y => A y i j) x _ - fderiv ℝ (fun y => linearPart A y i j) x _
  erw [fderiv_sub (hA i j x) ((linearPart_contDiff A i j (n := 1)).differentiable_one x)]
  rfl

lemma coordinateDerivative_nonlinearPart_memLp {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j))
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) (r : Fin m) :
    SquareIntegrable (coordinateDerivative (nonlinearPart A) r) := by
  intro i j
  simp only [coordinateDerivative_nonlinearPart hA, Matrix.sub_apply]
  exact (hZ r i j).sub (memLp_const _)

lemma coordinateDerivative_mean {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (hL : SquareIntegrable A)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) (r i j : Fin m) :
    (∫ x, coordinateDerivative A r x i j ∂stdGaussian (E m)) = firstCoeff A r i j := by
  exact gaussian_integral_coordinateDerivative (hA i j) (hL i j) r (hZ r i j)

lemma coordinateDerivative_nonlinearPart_mean {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (hL : SquareIntegrable A)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) (r i j : Fin m) :
    (∫ x, coordinateDerivative (nonlinearPart A) r x i j ∂stdGaussian (E m)) = 0 := by
  simp only [coordinateDerivative_nonlinearPart hA, Matrix.sub_apply]
  rw [integral_sub ((hZ r i j).integrable (by norm_num)) (integrable_const _),
    coordinateDerivative_mean hA hL hZ]
  simp

lemma coordinateDerivative_entry_energy {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (hL : SquareIntegrable A)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) (r i j : Fin m) :
    (∫ x, (coordinateDerivative A r x i j)^2 ∂stdGaussian (E m)) =
      (firstCoeff A r i j)^2 +
        ∫ x, (coordinateDerivative (nonlinearPart A) r x i j)^2 ∂stdGaussian (E m) := by
  have hG := coordinateDerivative_nonlinearPart_memLp hA hZ r i j
  have he (x : E m) : (coordinateDerivative A r x i j)^2 =
      (firstCoeff A r i j)^2 +
      2 * firstCoeff A r i j * coordinateDerivative (nonlinearPart A) r x i j +
      (coordinateDerivative (nonlinearPart A) r x i j)^2 := by
    simp only [coordinateDerivative_nonlinearPart hA, Matrix.sub_apply]
    ring
  simp_rw [he]
  erw [integral_add ((integrable_const _).add
    ((hG.integrable (by norm_num)).const_mul _)) hG.integrable_sq,
    integral_add (integrable_const _) ((hG.integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul (2 * firstCoeff A r i j),
    coordinateDerivative_nonlinearPart_mean hA hL hZ, mul_zero, add_zero]
  simp

lemma coordinateDerivative_energy {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (hL : SquareIntegrable A)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) (r : Fin m) :
    fieldEnergy (coordinateDerivative A r) = (∑ i, ∑ j, (firstCoeff A r i j)^2) +
      fieldEnergy (coordinateDerivative (nonlinearPart A) r) := by
  unfold fieldEnergy
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hZ r i j).integrable_sq)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (coordinateDerivative_nonlinearPart_memLp hA hZ r i j).integrable_sq))]
  simp_rw [integral_finsetSum _ (fun j _ => (hZ r _ j).integrable_sq),
    integral_finsetSum _ (fun j _ =>
      (coordinateDerivative_nonlinearPart_memLp hA hZ r _ j).integrable_sq),
    coordinateDerivative_entry_energy hA hL hZ, Finset.sum_add_distrib]

lemma firstChaos_energy {m : ℕ} {A : E m → Mat m} (hL : SquareIntegrable A) :
    fieldEnergy A = (∑ r, ∑ i, ∑ j, (firstCoeff A r i j)^2) +
      fieldEnergy (nonlinearPart A) := by
  unfold fieldEnergy
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hL i j).integrable_sq)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (nonlinearPart_memLp hL i j).integrable_sq))]
  simp_rw [integral_finsetSum _ (fun j _ => (hL _ j).integrable_sq),
    integral_finsetSum _ (fun j _ => (nonlinearPart_memLp hL _ j).integrable_sq),
    pow_two, entry_second_moment hL, Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ i, ∑ r, ∑ j, firstCoeff A r i j * firstCoeff A r i j :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- The linear projection contributes exactly the same amount to both energies. -/
theorem firstChaos_energy_cancellation {m : ℕ} {A : E m → Mat m}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (hL : SquareIntegrable A)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) :
    fieldEnergy A - (∑ r, fieldEnergy (coordinateDerivative A r)) =
      fieldEnergy (nonlinearPart A) -
        ∑ r, fieldEnergy (coordinateDerivative (nonlinearPart A) r) := by
  rw [firstChaos_energy hL]
  simp_rw [coordinateDerivative_energy hA hL hZ, Finset.sum_add_distrib]
  ring

/-- The full H1 projection interface used by the chaos resolvent. -/
theorem firstChaos_h1_projection {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian)
    (hsm : ∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j))
    (hbd : ∃ R : ℝ, ∀ x i j, |A x i j| ≤ R)
    (hm : ∀ i j, expectation (fun x => A x i j) = 0)
    (hZ : ∀ r, SquareIntegrable (coordinateDerivative A r)) :
    (∀ x, (nonlinearPart A x).IsHermitian) ∧
    (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => nonlinearPart A x i j)) ∧
    SquareIntegrable (nonlinearPart A) ∧
    (∀ r, SquareIntegrable (coordinateDerivative (nonlinearPart A) r)) ∧
    (∀ i j, expectation (fun x => nonlinearPart A x i j) = 0) ∧
    (∀ r i j, expectation (fun x => x r * nonlinearPart A x i j) = 0) ∧
    fieldEnergy A - (∑ r, fieldEnergy (coordinateDerivative A r)) =
      fieldEnergy (nonlinearPart A) -
        ∑ r, fieldEnergy (coordinateDerivative (nonlinearPart A) r) := by
  have hL : SquareIntegrable A := entry_memLp_of_bounded (fun i j => (hsm i j).continuous) hbd
  have hd : ∀ i j, Differentiable ℝ (fun x => A x i j) :=
    fun i j => (hsm i j).differentiable (by simp)
  exact ⟨nonlinearPart_isHermitian hA, nonlinearPart_contDiff hsm,
    nonlinearPart_memLp hL, coordinateDerivative_nonlinearPart_memLp hd hZ,
    nonlinearPart_mean hL hm, nonlinearPart_coord hL, firstChaos_energy_cancellation hd hL hZ⟩

end Submission.Obl.Entropy__normalized_remainder
