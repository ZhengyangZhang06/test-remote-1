import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.Separation

open scoped BigOperators
open Matrix

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate Submission.Lib.EntropyTools

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def rotate (U M : Matrix n n ℝ) : Matrix n n ℝ := U.transpose * M * U

lemma rotate_sub (U M N : Matrix n n ℝ) : rotate U (M - N) = rotate U M - rotate U N := by
  simp [rotate, Matrix.mul_sub, Matrix.sub_mul]

lemma rotate_add (U M N : Matrix n n ℝ) : rotate U (M + N) = rotate U M + rotate U N := by
  simp [rotate, Matrix.mul_add, Matrix.add_mul]

lemma rotate_smul (U M : Matrix n n ℝ) (c : ℝ) : rotate U (c • M) = c • rotate U M := by
  simp [rotate]

lemma rotate_nsmul (U M : Matrix n n ℝ) (c : ℕ) : rotate U (c • M) = c • rotate U M := by
  simp only [rotate, Matrix.mul_smul, Matrix.smul_mul]

lemma rotate_symmetric (U M : Matrix n n ℝ) (hM : M.IsHermitian) (i j : n) :
    rotate U M j i = rotate U M i j := by
  have hh : (rotate U M).IsHermitian := by
    simpa only [rotate, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul U hM
  simpa only [star_trivial] using hh.apply i j

noncomputable def endpointCost (b l p e : ℝ → ℝ) (dk db psi : ℝ → ℝ → ℝ)
    (a c G g Z : ℝ) : ℝ :=
  (40/37)*(G*b c + Z*dk a c - (7/25)*g)^2 +
  (42/37)*(G*b c + Z*dk a c - (3/4)*g)^2 + (27/592)*g^2 +
  (40/3)*(G*l c + Z*db a c)^2 +
  (5/17)*(G*e c + Z*psi a c + (3/2)*g*b c)^2 / p c

noncomputable def matrixBudget (p : ℝ → ℝ) (A D L M g : Matrix n n ℝ) : ℝ :=
  (40/37)*squareEnergy (D - (7/25 : ℝ) • g) +
  (42/37)*squareEnergy (D - (3/4 : ℝ) • g) + (27/592)*squareEnergy g +
  (40/3)*squareEnergy L +
  (5/17)*squareEnergy (M * cfc (fun a => (Real.sqrt (p a))⁻¹) A)

lemma matrixBudget_nonneg (p : ℝ → ℝ) (A D L M g : Matrix n n ℝ) :
    0 ≤ matrixBudget p A D L M g := by
  unfold matrixBudget squareEnergy
  positivity

lemma matrixBudget_eq_endpoints (b l p e : ℝ → ℝ) (dk db psi : ℝ → ℝ → ℝ)
    (hp : ∀ a, 0 < p a) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (D L M G g Z : Matrix n n ℝ)
    (hD : ∀ i j, rotate hA.eigenvectorUnitary D i j =
      rotate hA.eigenvectorUnitary G i j * b (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * dk (hA.eigenvalues i) (hA.eigenvalues j))
    (hL : ∀ i j, rotate hA.eigenvectorUnitary L i j =
      rotate hA.eigenvectorUnitary G i j * l (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * db (hA.eigenvalues i) (hA.eigenvalues j))
    (hM : ∀ i j, rotate hA.eigenvectorUnitary M i j =
      rotate hA.eigenvectorUnitary G i j * e (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * psi (hA.eigenvalues i) (hA.eigenvalues j) +
        (3/2)*rotate hA.eigenvectorUnitary g i j*b (hA.eigenvalues j)) :
    matrixBudget p A D L M g = ∑ i, ∑ j,
      endpointCost b l p e dk db psi (hA.eigenvalues i) (hA.eigenvalues j)
        (rotate hA.eigenvectorUnitary G i j) (rotate hA.eigenvectorUnitary g i j)
        (rotate hA.eigenvectorUnitary Z i j) := by
  have hs (N : Matrix n n ℝ) : squareEnergy N = ∑ i, ∑ j,
      (rotate hA.eigenvectorUnitary N i j)^2 :=
    (squareSum_orthogonal _ N (eigenbasis_mul_transpose_self hA)).symm
  unfold matrixBudget
  rw [hs (D - (7/25 : ℝ) • g), hs (D - (3/4 : ℝ) • g), hs g, hs L]
  rw [squareEnergy, weighted_squareSum_in_eigenbasis hA M p hp]
  change _ = ∑ i, ∑ j, endpointCost b l p e dk db psi _ _ _ _ _
  simp only [rotate_sub, rotate_smul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _ + (5/17) * (rotate hA.eigenvectorUnitary M i j ^ 2 / p _) = _
  rw [hD, hL, hM]
  unfold endpointCost
  ring

lemma matrixBudget_le (b l p e : ℝ → ℝ) (dk db psi sigma : ℝ → ℝ → ℝ)
    (hp : ∀ a, 0 < p a)
    (hscalar : ∀ a c G g Z,
      (endpointCost b l p e dk db psi a c G g Z +
        endpointCost b l p e dk db psi c a G g Z)/2 ≤
          chaosQuadratic G (g-G/2) + sigma a c*Z^2)
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (D L M G g Z : Matrix n n ℝ)
    (hG : G.IsHermitian) (hg : g.IsHermitian) (hZ : Z.IsHermitian)
    (hD : ∀ i j, rotate hA.eigenvectorUnitary D i j =
      rotate hA.eigenvectorUnitary G i j * b (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * dk (hA.eigenvalues i) (hA.eigenvalues j))
    (hL : ∀ i j, rotate hA.eigenvectorUnitary L i j =
      rotate hA.eigenvectorUnitary G i j * l (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * db (hA.eigenvalues i) (hA.eigenvalues j))
    (hM : ∀ i j, rotate hA.eigenvectorUnitary M i j =
      rotate hA.eigenvectorUnitary G i j * e (hA.eigenvalues j) +
        rotate hA.eigenvectorUnitary Z i j * psi (hA.eigenvalues i) (hA.eigenvalues j) +
        (3/2)*rotate hA.eigenvectorUnitary g i j*b (hA.eigenvalues j)) :
    matrixBudget p A D L M g ≤
      (∑ i, ∑ j, chaosQuadratic (G i j) (g i j-G i j/2)) +
      ∑ i, ∑ j, sigma (hA.eigenvalues i) (hA.eigenvalues j) *
        (rotate hA.eigenvectorUnitary Z i j)^2 := by
  rw [matrixBudget_eq_endpoints b l p e dk db psi hp hA D L M G g Z hD hL hM]
  rw [← chaosQuadratic_orthogonal _ G g (eigenbasis_mul_transpose_self hA)]
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply sum_le_of_transpose_average
  intro i j
  simp only [rotate_symmetric _ G hG i j, rotate_symmetric _ g hg i j,
    rotate_symmetric _ Z hZ i j]
  exact hscalar _ _ _ _ _

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
