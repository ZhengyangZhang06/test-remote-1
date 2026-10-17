import Submission.Obl.Entropy__gaussian_chaos_resolvent.ProjectionScalar

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

noncomputable def matrixFirstCoeff {m : ℕ} (A : E m → M m) (r : Fin m) : M m :=
  Matrix.of (fun i j => firstCoeff (fun x => A x i j) r)
noncomputable def matrixSecondRemainder {m : ℕ} (A : E m → M m) (x : E m) : M m :=
  A x - ∑ r, x r • matrixFirstCoeff A r

@[simp] theorem matrixSecondRemainder_apply {m : ℕ} (A : E m → M m)
    (x : E m) (i j : Fin m) :
    matrixSecondRemainder A x i j = secondRemainder (fun y => A y i j) x := by
  simp [matrixSecondRemainder, matrixFirstCoeff, secondRemainder, linearChaos, Matrix.sum_apply]

/-- Removing the first chaos preserves the difference between function and derivative energy. -/
theorem first_chaos_h1_projection (m : ℕ) (_hm : 1 ≤ m) (A : E m → M m)
    (hA : ∀ x, (A x).IsHermitian)
    (hsm : ∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j))
    (hbd : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    (hmean : ∀ i j, (∫ x, A x i j ∂gaussian m) = 0)
    (hD : ∀ r, MatrixL2 (matrixDeriv A r)) :
    (∀ x, (matrixSecondRemainder A x).IsHermitian) ∧
    (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => matrixSecondRemainder A x i j)) ∧
    MatrixL2 (matrixSecondRemainder A) ∧
    (∀ r, MatrixL2 (matrixDeriv (matrixSecondRemainder A) r)) ∧
    (∀ i j, (∫ x, matrixSecondRemainder A x i j ∂gaussian m) = 0) ∧
    (∀ r i j, (∫ x, x r * matrixSecondRemainder A x i j ∂gaussian m) = 0) ∧
    energy A - (∑ r, energy (matrixDeriv A r)) =
      energy (matrixSecondRemainder A) - (∑ r, energy (matrixDeriv (matrixSecondRemainder A) r)) := by
  obtain ⟨R, _, hR⟩ := hbd
  have hL : MatrixL2 A := by
    intro i j
    exact memLp_of_bounded (Filter.Eventually.of_forall (fun x => abs_le.mp (hR x i j)))
      (hsm i j).continuous.aestronglyMeasurable 2
  have hYL : MatrixL2 (matrixSecondRemainder A) := by
    intro i j
    simpa only [matrixSecondRemainder_apply] using memLp_secondRemainder (hL i j)
  have hYD : ∀ r, MatrixL2 (matrixDeriv (matrixSecondRemainder A) r) := by
    intro r i j
    change MemLp (coordDeriv (fun x => matrixSecondRemainder A x i j) r) 2 (gaussian m)
    have he : (fun x => matrixSecondRemainder A x i j) = secondRemainder (fun x => A x i j) :=
      funext (fun x => matrixSecondRemainder_apply A x i j)
    rw [he]
    have hd : coordDeriv (secondRemainder (fun x => A x i j)) r =
        fun x => coordDeriv (fun x => A x i j) r x - firstCoeff (fun x => A x i j) r :=
      funext (coordDeriv_secondRemainder ((hsm i j).differentiable (by norm_num)) r)
    rw [hd]
    exact (hD r i j).sub (memLp_const _)
  refine ⟨?_, ?_, hYL, hYD, ?_, ?_, ?_⟩
  · intro x
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, matrixSecondRemainder_apply]
    have he : (fun x => A x j i) = fun x => A x i j := funext (fun x => (hA x).apply i j)
    rw [he]
  · intro i j
    simpa only [matrixSecondRemainder_apply] using contDiff_secondRemainder (hsm i j)
  · intro i j
    simpa only [matrixSecondRemainder_apply] using integral_secondRemainder (hL i j) (hmean i j)
  · intro r i j
    simpa only [matrixSecondRemainder_apply] using integral_coordinate_secondRemainder (hL i j) r
  · rw [energy_eq_sum hL, energy_eq_sum hYL]
    simp_rw [energy_eq_sum (hD _), energy_eq_sum (hYD _)]
    have hswap (b : Fin m → Fin m → Fin m → ℝ) :
        (∑ r, ∑ i, ∑ j, b r i j) = ∑ i, ∑ j, ∑ r, b r i j := by
      rw [Finset.sum_comm]
      congr 1
      funext i
      exact Finset.sum_comm
    rw [hswap (fun r i j => ∫ x, (matrixDeriv A r x i j)^2 ∂gaussian m),
      hswap (fun r i j => ∫ x, (matrixDeriv (matrixSecondRemainder A) r x i j)^2 ∂gaussian m)]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [matrixDeriv, Matrix.of_apply, matrixSecondRemainder_apply] using
      scalar_projection_cancellation ((hsm i j).differentiable (by norm_num)) (hL i j)
        (fun r => hD r i j)

end Submission.Obl.Entropy__gaussian_chaos_resolvent
