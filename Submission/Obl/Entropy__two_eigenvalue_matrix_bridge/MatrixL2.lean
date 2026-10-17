import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.SpectralEnergy

open scoped BigOperators Topology
open Matrix MeasureTheory Filter

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate

variable {n Ω : Type*} [Fintype n] [DecidableEq n]

lemma mul_entry_bound (M N : Matrix n n ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ i j, |M i j| ≤ C) (hN : ∀ i j, |N i j| ≤ D) (i j : n) :
    |(M * N) i j| ≤ (Fintype.card n : ℝ) * (C * D) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : n, C * D := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) hC
    _ = _ := by simp

lemma eigenvalues_entry_bound {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ i j, |A i j| ≤ R) (i : n) :
    |hA.eigenvalues i| ≤ (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) * R) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU (i j : n) : |U i j| ≤ 1 :=
    entry_norm_bound_of_unitary hA.eigenvectorUnitary.property i j
  have hd : U.transpose * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [cfc_id ℝ A hA.isSelfAdjoint, id_eq] using cfc_in_eigenbasis hA id
  have hUA (i j : n) : |(U.transpose * A) i j| ≤ (Fintype.card n : ℝ) * R := by
    simpa only [one_mul] using mul_entry_bound U.transpose A zero_le_one hR
      (fun i j => hU j i) hb i j
  have hh := mul_entry_bound (U.transpose * A) U (mul_nonneg (Nat.cast_nonneg _) hR)
    zero_le_one hUA hU i i
  simpa only [hd, Matrix.diagonal_apply_eq, mul_one] using hh

lemma cfc_entry_bound {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, |f (hA.eigenvalues i)| ≤ C)
    (i j : n) : |cfc f A i j| ≤ (Fintype.card n : ℝ) * C := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_apply,
    RCLike.ofReal_real_eq_id]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Function.comp_apply,
    RCLike.ofReal_real_eq_id, id_eq]
  calc
    _ ≤ ∑ k, |(hA.eigenvectorUnitary : Matrix n n ℝ) i k * f (hA.eigenvalues k) *
        (hA.eigenvectorUnitary : Matrix n n ℝ) j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : n, C := by
      apply Finset.sum_le_sum
      intro k _
      simp only [abs_mul]
      have hi := entry_norm_bound_of_unitary hA.eigenvectorUnitary.property i k
      have hj := entry_norm_bound_of_unitary hA.eigenvectorUnitary.property j k
      calc
        _ ≤ (1 * C) * 1 :=
          mul_le_mul (mul_le_mul hi (hf k) (abs_nonneg _) zero_le_one) hj
            (abs_nonneg _) (by positivity)
        _ = C := by ring
    _ = _ := by simp

lemma bounded_cfc_entries (A : Ω → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hb : ∃ R : ℝ, 0 ≤ R ∧ ∀ x i j, |A x i j| ≤ R)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |cfc f (A x) i j| ≤ C := by
  obtain ⟨R, hR, hb⟩ := hb
  let S : ℝ := (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) * R)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
  refine ⟨(Fintype.card n : ℝ) * |C|, by positivity, ?_⟩
  intro x i j
  apply cfc_entry_bound (hA x) f (abs_nonneg C)
  intro k
  have hk : (hA x).eigenvalues k ∈ Set.Icc (-S) S :=
    abs_le.mp (eigenvalues_entry_bound (hA x) hR (hb x) k)
  exact (hC _ ⟨_, hk, rfl⟩).trans (le_abs_self C)

section Measure
variable [MeasurableSpace Ω] {μ : Measure Ω}

lemma l2_mul_bounded_left {F B : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) μ)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |B x i j| ≤ C) (i j : n) :
    MemLp (fun x => (B x * F x) i j) 2 μ := by
  obtain ⟨C, hC, hb⟩ := hb
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  apply (hF k j).of_le_mul (c := C) ((hB i k).mul (hF k j).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb x i k) (abs_nonneg _)

lemma l2_mul_bounded_right {F B : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) μ)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |B x i j| ≤ C) (i j : n) :
    MemLp (fun x => (F x * B x) i j) 2 μ := by
  obtain ⟨C, hC, hb⟩ := hb
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  apply (hF i k).of_le_mul (c := C) ((hF i k).aestronglyMeasurable.mul (hB k j))
  exact Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    calc
      _ ≤ |F x i k| * C := mul_le_mul_of_nonneg_left (hb x k j) (abs_nonneg _)
      _ = C * |F x i k| := mul_comm _ _

lemma l2_iterComm {L Z : Ω → Matrix n n ℝ}
    (hZ : ∀ i j, MemLp (fun x => Z x i j) 2 μ)
    (hL : ∀ i j, AEStronglyMeasurable (fun x => L x i j) μ)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |L x i j| ≤ C) (k : ℕ) (i j : n) :
    MemLp (fun x => iterComm (L x) k (Z x) i j) 2 μ := by
  induction k generalizing i j with
  | zero => exact hZ i j
  | succ k ih =>
    exact (l2_mul_bounded_left ih hL hb i j).sub (l2_mul_bounded_right ih hL hb i j)

end Measure

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
