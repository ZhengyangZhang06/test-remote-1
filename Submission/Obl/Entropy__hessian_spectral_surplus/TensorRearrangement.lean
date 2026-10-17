import Submission.Obl.Entropy__hessian_spectral_surplus.TensorRotation

open scoped BigOperators

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric three-index weight turns endpoint monotonicity into the required rearrangement. -/
lemma tensor_rearrangement (a : n → ℝ) (q : ℝ → ℝ) (B : ℝ → ℝ → ℝ)
    (hq : Monotone q) (hBs : ∀ x y, B x y = B y x)
    (hBm : ∀ y, Monotone (fun x => B x y)) (W : n → n → n → ℝ)
    (hW : ∀ r i j, 0 ≤ W r i j)
    (hW12 : ∀ r i j, W r i j = W i r j)
    (hW23 : ∀ r i j, W r i j = W r j i) :
    (∑ r, ∑ i, ∑ j, W r i j * q (a r) * B (a i) (a j)) ≤
      ∑ r, ∑ i, ∑ j, W r i j * ((q (a i) + q (a j)) / 2) * B (a i) (a j) := by
  let S : ℝ := ∑ r, ∑ i, ∑ j, W r i j * q (a i) * B (a i) (a j)
  let T : ℝ := ∑ r, ∑ i, ∑ j, W r i j * q (a r) * B (a i) (a j)
  have h1 : (∑ r, ∑ i, ∑ j, W r i j * q (a r) * B (a r) (a j)) = S := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hW12 i r j]
  have h2 : (∑ r, ∑ i, ∑ j, W r i j * q (a i) * B (a r) (a j)) = T := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hW12 i r j]
  have h3 : (∑ r, ∑ i, ∑ j, W r i j * q (a j) * B (a i) (a j)) = S := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hW23 r j i, hBs (a j) (a i)]
  have hnonneg : 0 ≤ ∑ r, ∑ i, ∑ j,
      W r i j * ((q (a i) - q (a r)) * (B (a i) (a j) - B (a r) (a j))) := by
    apply Finset.sum_nonneg
    intro r _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hW r i j)
    rcases le_total (a i) (a r) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hq h)) (sub_nonpos.mpr (hBm _ h))
    · exact mul_nonneg (sub_nonneg.mpr (hq h)) (sub_nonneg.mpr (hBm _ h))
  have he : (∑ r, ∑ i, ∑ j,
      W r i j * ((q (a i) - q (a r)) * (B (a i) (a j) - B (a r) (a j)))) =
      S - T - T + S := by
    simp only [mul_sub, sub_mul, ← mul_assoc, Finset.sum_sub_distrib]
    change S - T - ((∑ r, ∑ i, ∑ j, W r i j * q (a i) * B (a r) (a j)) -
      (∑ r, ∑ i, ∑ j, W r i j * q (a r) * B (a r) (a j))) = _
    rw [h1, h2]
    ring
  have hR : (∑ r, ∑ i, ∑ j, W r i j * ((q (a i) + q (a j)) / 2) * B (a i) (a j)) = S := by
    calc
      _ = (S + (∑ r, ∑ i, ∑ j, W r i j * q (a j) * B (a i) (a j))) / 2 := by
        dsimp only [S]
        simp only [Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = S := by rw [h3]; ring

  rw [he] at hnonneg
  rw [hR]
  change T ≤ S
  linarith

end Submission.Obl.Entropy__hessian_spectral_surplus
