import Submission.Obl.Entropy__equality_cases.Frobenius
import Submission.Obl.Entropy__equality_cases.Weight
import Submission.Obl.Entropy__equality_cases.CoefficientCompactness

namespace Submission.Obl.Entropy__equality_cases

open Matrix Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distance from the identity is the sum of squared eigenvalue deviations. -/
theorem frobeniusSq_sub_one {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    frobeniusSq (A - 1) = ∑ i, (hA.eigenvalues i - 1) ^ 2 := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hUU : U * U.transpose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hUtU : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hdiag : U.transpose * A * U = diagonal hA.eigenvalues := by
    simpa [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag' : U.transpose * (A - 1) * U = diagonal (fun i => hA.eigenvalues i - 1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag, Matrix.mul_one, hUtU]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.sub_apply, hij]
  rw [← frobeniusSq_orthogonal (A - 1) U U hUU hUU, hdiag', frobeniusSq_eq_sum]
  simp [Matrix.diagonal_apply]

/-- Eigenvalues converging to one force every matrix entry to converge to the identity,
without requiring convergence of eigenbases. -/
theorem hermitian_tendsto_one_of_eigenvalues {α : Type*} {l : Filter α}
    (A : α → Matrix ι ι ℝ) (hA : ∀ n, (A n).IsHermitian)
    (heig : ∀ i, Tendsto (fun n => (hA n).eigenvalues i) l (𝓝 1)) :
    ∀ i j, Tendsto (fun n => A n i j) l (𝓝 ((1 : Matrix ι ι ℝ) i j)) := by
  have hsq : Tendsto (fun n => frobeniusSq (A n - 1)) l (𝓝 0) := by
    simp_rw [frobeniusSq_sub_one (hA _)]
    simpa using tendsto_finsetSum Finset.univ (fun i _ => ((heig i).sub (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1))).pow 2)
  intro i j
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := hsq.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [hsmall] with n hn
  have hbound : (A n i j - (1 : Matrix ι ι ℝ) i j) ^ 2 ≤ frobeniusSq (A n - 1) := by
    rw [frobeniusSq_eq_sum]
    exact (Finset.single_le_sum (fun k _ => sq_nonneg ((A n - 1) i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun t _ => sq_nonneg ((A n - 1) k t)))
        (Finset.mem_univ i))
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Vanishing rigidity weights imply convergence of a positive semidefinite matrix to identity. -/
theorem posSemidef_tendsto_one_of_weight {α : Type*} {l : Filter α}
    (A : α → Matrix ι ι ℝ) (hA : ∀ n, (A n).PosSemidef)
    (hweight : Tendsto (fun n => ∑ i,
      Submission.Lib.EntropyTools.rigidityWeight ((hA n).isHermitian.eigenvalues i)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun n => A n i j) l (𝓝 ((1 : Matrix ι ι ℝ) i j)) := by
  apply hermitian_tendsto_one_of_eigenvalues A (fun n => (hA n).isHermitian)
  exact tendsto_one_of_sum_rigidityWeight _ (fun n i => (hA n).eigenvalues_nonneg i) hweight

/-- The complete coefficient extraction from vanishing eigenvalue slack in Section 6. -/
theorem coefficient_subsequence_of_vanishing_weight
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (hB : ∀ n, (∑ r, X n r * X n r).PosSemidef)
    (hweight : Tendsto (fun n => ∑ i,
      Submission.Lib.EntropyTools.rigidityWeight ((hB n).isHermitian.eigenvalues i)) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      (∀ r, (Y r).IsHermitian) ∧ (∑ r, Y r * Y r = 1) ∧
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) :=
  normalized_coefficient_subsequence X hX
    (posSemidef_tendsto_one_of_weight _ hB hweight)

end Submission.Obl.Entropy__equality_cases
