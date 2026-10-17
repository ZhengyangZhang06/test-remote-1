import Mathlib

open Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__centered_slack_transports

variable {m : ℕ}

/-- Orthogonal conjugation identifies the distance to identity with the maximum
absolute difference between an eigenvalue and one. -/
theorem norm_sub_one_eq_eigenvalues {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) :
    ‖B - 1‖ = ‖fun i => hB.eigenvalues i - 1‖ := by
  let U := hB.eigenvectorUnitary
  have he : B - 1 = Unitary.conjStarAlgAut ℝ _ U
      (Matrix.diagonal (fun i => hB.eigenvalues i - 1)) := by
    rw [show Matrix.diagonal (fun i => hB.eigenvalues i - 1) =
      Matrix.diagonal hB.eigenvalues - 1 by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub],
      map_sub, map_one]
    congr 1
    simpa [U] using hB.spectral_theorem
  rw [he]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

/-- Eigenvalues converging to one force Hermitian matrices to converge to identity,
without needing convergence of their eigenvectors. -/
theorem tendsto_matrix_one_of_eigenvalues
    (B : ℕ → Matrix (Fin m) (Fin m) ℝ) (hB : ∀ n, (B n).IsHermitian)
    (he : ∀ i, Tendsto (fun n => (hB n).eigenvalues i) atTop (nhds 1)) :
    Tendsto B atTop (nhds 1) := by
  have h : Tendsto (fun n => fun i => (hB n).eigenvalues i - 1) atTop (nhds 0) := by
    apply tendsto_pi_nhds.2
    intro i
    simpa only [Pi.zero_apply, sub_self] using (he i).sub_const 1
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_sub_one_eq_eigenvalues (hB _), norm_zero] using h.norm

end Submission.Obl.Entropy__centered_slack_transports
