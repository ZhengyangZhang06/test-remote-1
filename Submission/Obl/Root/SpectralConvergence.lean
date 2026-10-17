import Submission.Obl.Root.RigidityWeight

/-!
# Spectral convergence in the entropy rigidity argument

Vanishing scalar weights imply convergence of the positive semidefinite
first-chaos Gram matrices to the identity. The argument uses the spectral
theorem and a squared Frobenius identity, without choosing continuous eigenvectors.
-/

open Filter Topology
open scoped BigOperators
open Submission.Lib.EntropyTools

namespace Submission.Obl.Root

lemma sum_sq_eq_trace_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∑ i, ∑ j, A i j ^ 2) = (A ^ 2).trace := by
  have hs (i j : ι) : A j i = A i j := by
    simpa using congr_fun (congr_fun hA.eq i) j
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]

lemma trace_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul]

/-- The squared Frobenius distance to identity is the sum of squared spectral distances. -/
lemma sum_sq_sub_one_eq_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∑ i, ∑ j, (A i j - (1 : Matrix ι ι ℝ) i j) ^ 2) =
      ∑ i, (hA.eigenvalues i - 1) ^ 2 := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => hA.eigenvalues i - 1)
  have hdiag : A - 1 = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U D := by
    change A - 1 = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => hA.eigenvalues i - 1))
    rw [show Matrix.diagonal (fun i => hA.eigenvalues i - 1) =
      Matrix.diagonal hA.eigenvalues - 1 by rw [← Matrix.diagonal_sub]; rfl]
    rw [map_sub, map_one]
    congr 1
    simpa using hA.spectral_theorem
  calc
    _ = ((A - 1) ^ 2).trace := sum_sq_eq_trace_sq (hA.sub Matrix.isHermitian_one)
    _ = (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U (D ^ 2)).trace := by
      rw [hdiag, map_pow]
    _ = (D ^ 2).trace := trace_unitary_conj U _
    _ = _ := by simp [D, Matrix.diagonal_pow, Matrix.trace_diagonal]

/-- Spectral convergence to one implies matrix convergence to the identity. -/
theorem matrix_tendsto_one_of_eigenvalues {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} {A : α → Matrix ι ι ℝ} (hA : ∀ j, (A j).IsHermitian)
    (he : ∀ i, Tendsto (fun j => (hA j).eigenvalues i) l (𝓝 1)) :
    Tendsto A l (𝓝 1) := by
  have hs : Tendsto (fun j => ∑ i, ((hA j).eigenvalues i - 1) ^ 2) l (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => ((he i).sub_const 1).pow 2)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro k
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hs.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hj
  have hb : (A j i k - (1 : Matrix ι ι ℝ) i k) ^ 2 ≤
      ∑ r, ((hA j).eigenvalues r - 1) ^ 2 := by
    rw [← sum_sq_sub_one_eq_eigenvalues (hA j)]
    calc
      _ ≤ ∑ s, (A j i s - (1 : Matrix ι ι ℝ) i s) ^ 2 :=
        Finset.single_le_sum (fun s _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ _ := Finset.single_le_sum
        (fun r _ => Finset.sum_nonneg fun s _ =>
          sq_nonneg (A j r s - (1 : Matrix ι ι ℝ) r s)) (Finset.mem_univ i)
  rw [Real.dist_eq]
  nlinarith [sq_abs (A j i k - (1 : Matrix ι ι ℝ) i k),
    abs_nonneg (A j i k - (1 : Matrix ι ι ℝ) i k)]

/-- The strict remainder determines the limiting Gram matrix. -/
theorem matrix_tendsto_one_of_weight_sum {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} {A : α → Matrix ι ι ℝ} (hA : ∀ j, (A j).PosSemidef)
    (hw : Tendsto (fun j => ∑ i, rigidityWeight ((hA j).isHermitian.eigenvalues i))
      l (𝓝 0)) : Tendsto A l (𝓝 1) := by
  apply matrix_tendsto_one_of_eigenvalues (fun j => (hA j).isHermitian)
  exact eigenvalues_tendsto_one_of_weight_sum
    (Filter.Eventually.of_forall fun j i => (hA j).eigenvalues_nonneg i) hw

end Submission.Obl.Root
