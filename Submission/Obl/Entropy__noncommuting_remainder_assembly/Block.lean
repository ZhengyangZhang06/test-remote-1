import Submission.Obl.Entropy__noncommuting_remainder_assembly.MatrixAlgebra

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

lemma pairing_young_two (A B : Matrix ι κ ℝ) {c : ℝ} (hc : 0 < c) :
    2 * pairing A B ≤ squareSum A / c + c * squareSum B := by
  simpa only [← Finset.sum_div, ← Finset.mul_sum, squareSum] using
    pairing_young_columns A B (fun _ => c) (fun _ => hc)

/-- The energy identity used in block Cauchy--Schwarz. -/
lemma block_energy [DecidableEq ι] (X : ν → Matrix ι κ ℝ)
    (E F : Matrix ι ι ℝ) (s α : ℝ)
    (hF : ((s⁻¹ • (1 : Matrix ι ι ℝ)) + α • (∑ r, X r * (X r).transpose)) * E = F) :
    squareSum E / s + α * (∑ r, squareSum ((X r).transpose * E)) = pairing E F := by
  rw [sum_squareSum_adjoint, ← hF, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_mul, pairing_add_right,
    pairing_smul_right, pairing_smul_right, pairing_self, div_eq_mul_inv]
  ring

/-- Block Cauchy--Schwarz in equation (3.21), valid for rectangular block factors. -/
lemma block_bound [DecidableEq ι] (X : ν → Matrix ι κ ℝ)
    (S a : Matrix ι ι ℝ) (L : ν → Matrix κ ι ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α)
    (hInv : (s⁻¹ • (1 : Matrix ι ι ℝ) + α • (∑ r, X r * (X r).transpose)) * S = 1) :
    pairing (a + ∑ r, X r * L r) (S * (a + ∑ r, X r * L r)) ≤
      s * squareSum a + (∑ r, squareSum (L r)) / α := by
  let F := a + ∑ r, X r * L r
  let E := S * F
  have hE : (s⁻¹ • (1 : Matrix ι ι ℝ) + α • (∑ r, X r * (X r).transpose)) * E = F := by
    dsimp [E]
    rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]
  have henergy := block_energy X E F s α hE
  have ha := pairing_young_two E a hs
  have hL := Finset.sum_le_sum (s := Finset.univ)
    (fun r _ => pairing_young_two (L r) ((X r).transpose * E) hα)
  have hpair : pairing E F = pairing E a + ∑ r, pairing (L r) ((X r).transpose * E) := by
    dsimp [F]
    rw [pairing_add_right, pairing_sum_right]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [pairing_mul_left, pairing_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hL
  change pairing F E ≤ _
  rw [pairing_comm F E]
  linarith

/-- The constants appearing in the frozen remainder budget. -/
lemma block_bound_constants [DecidableEq ι] (X : ν → Matrix ι κ ℝ)
    (S a : Matrix ι ι ℝ) (L : ν → Matrix κ ι ℝ)
    (hInv : ((37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) +
      (3 / 40 : ℝ) • (∑ r, X r * (X r).transpose)) * S = 1) :
    pairing (a + ∑ r, X r * L r) (S * (a + ∑ r, X r * L r)) ≤
      (40 / 37 : ℝ) * squareSum a + (40 / 3 : ℝ) * (∑ r, squareSum (L r)) := by
  have h := block_bound X S a L (s := 40 / 37) (α := 3 / 40)
    (by norm_num) (by norm_num) (by norm_num; exact hInv)
  convert h using 1 <;> ring

end Submission.Obl.Entropy__noncommuting_remainder_assembly
