import Mathlib
import ChallengeDeps

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

/-- The entries of a matrix, with their Euclidean rather than operator norm. -/
def entries {m : ℕ} (A : Mat m) : EuclideanSpace ℝ (Fin m × Fin m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

@[simp] theorem entries_apply {m : ℕ} (A : Mat m) (i j : Fin m) :
    entries A (i, j) = A i j := rfl

@[simp] theorem entries_sub {m : ℕ} (A B : Mat m) :
    entries (A - B) = entries A - entries B := rfl

@[simp] theorem entries_zero {m : ℕ} : entries (0 : Mat m) = 0 := rfl

theorem norm_entries_sq {m : ℕ} (A : Mat m) :
    ‖entries A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem continuous_entries {m : ℕ} : Continuous (@entries m) :=
  (PiLp.continuous_toLp 2 _).comp (by fun_prop)

/-- The assumed functional-calculus estimate in Euclidean matrix coordinates. -/
theorem norm_entries_cfc_sub_le {m : ℕ} {q : ℝ → ℝ}
    (hq : ∀ U V : Mat m, U.IsHermitian → V.IsHermitian →
      (∑ i, ∑ j, (cfc q U i j - cfc q V i j) ^ 2) ≤
        ∑ i, ∑ j, (U i j - V i j) ^ 2)
    {U V : Mat m} (hU : U.IsHermitian) (hV : V.IsHermitian) :
    ‖entries (cfc q U) - entries (cfc q V)‖ ≤ ‖entries U - entries V‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [← entries_sub, norm_entries_sq, Matrix.sub_apply] using hq U V hU hV

/-- A linear symmetric matrix field. -/
def linearField {m : ℕ} (X : Fin m → Mat m) (x : E m) : Mat m :=
  ∑ r, x r • X r

@[simp] theorem linearField_apply {m : ℕ} (X : Fin m → Mat m) (x : E m)
    (i j : Fin m) : linearField X x i j = ∑ r, x r * X r i j := by
  simp [linearField, Matrix.sum_apply]

theorem linearField_hermitian {m : ℕ} {X : Fin m → Mat m}
    (hX : ∀ r, (X r).IsHermitian) (x : E m) : (linearField X x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [linearField_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simpa using congrArg (fun M : Mat m => M i j) (hX r).eq

theorem continuous_linearField {m : ℕ} (X : Fin m → Mat m) :
    Continuous (linearField X) := by
  unfold linearField
  fun_prop

theorem memLp_coord {m : ℕ} (r : Fin m) :
    MemLp (fun x : E m => x r) 2 (stdGaussian (E m)) := by
  exact (IsGaussian.memLp_two_id (μ := stdGaussian (E m))).continuousLinearMap_comp
    (EuclideanSpace.proj (𝕜 := ℝ) r)

theorem memLp_linearField_entry {m : ℕ} (X : Fin m → Mat m) (i j : Fin m) :
    MemLp (fun x : E m => linearField X x i j) 2 (stdGaussian (E m)) := by
  simp only [linearField_apply]
  exact memLp_finsetSum _ (fun r _ => (memLp_coord r).mul_const _)

theorem memLp_entries {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    {A : α → Mat m} (hA : ∀ i j, MemLp (fun x => A x i j) 2 μ) :
    MemLp (fun x => entries (A x)) 2 μ := by
  have h : MemLp (fun x (p : Fin m × Fin m) => A x p.1 p.2) 2 μ :=
    memLp_pi_iff.mpr (fun p => hA p.1 p.2)
  exact h.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m × Fin m => ℝ)).symm.toContinuousLinearMap

theorem memLp_linearField {m : ℕ} (X : Fin m → Mat m) :
    MemLp (fun x : E m => entries (linearField X x)) 2 (stdGaussian (E m)) :=
  memLp_entries (memLp_linearField_entry X)

/-- Coefficient convergence gives Gaussian mean-square convergence of the linear fields. -/
theorem linearField_entry_energy {m : ℕ} (X : Fin m → Mat m) (i j : Fin m) :
    (∫ x : E m, (linearField X x i j) ^ 2 ∂stdGaussian (E m)) ≤
      (∫ x : E m, ‖x‖ ^ 2 ∂stdGaussian (E m)) * ∑ r, (X r i j) ^ 2 := by
  calc
    _ ≤ ∫ x : E m, ‖x‖ ^ 2 * ∑ r, (X r i j) ^ 2 ∂stdGaussian (E m) := by
      apply integral_mono (memLp_linearField_entry X i j).integrable_sq
        ((IsGaussian.memLp_two_id.integrable_norm_pow (by decide : 2 ≠ 0)).mul_const _)
      intro x
      dsimp only [id]
      rw [linearField_apply, EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := integral_mul_const _ _

end Submission.Obl.Entropy__linear_transport_limit
