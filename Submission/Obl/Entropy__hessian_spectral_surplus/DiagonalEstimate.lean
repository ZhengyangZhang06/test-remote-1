import Submission.Obl.Entropy__hessian_spectral_surplus.TensorRearrangement
import Submission.Obl.Entropy__hessian_spectral_surplus.ScalarCoefficients

open scoped BigOperators

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma diagonal_multiplier_estimate (a : n → ℝ) (q k : ℝ → ℝ)
    (B S : ℝ → ℝ → ℝ) (hqpos : ∀ a, 0 < q a) (hqmono : Monotone q)
    (hBs : ∀ a b, B a b = B b a) (hBm : ∀ b, Monotone (fun a => B a b))
    (hc : ∀ a b, (q a * k a ^ 2 + q b * k b ^ 2) * (dslope q a b) ^ 2 +
      2 * q a * q b * (k a + k b) * dslope k a b * dslope q a b =
      (q a + q b) * B a b * (dslope q a b) ^ 2)
    (hs : ∀ a b, 1 - (dslope k a b) ^ 2 + S a b ≤
      (dslope q a b) ^ 2 * B a b / (q a * q b))
    (T Z K : n → n → n → ℝ)
    (hT12 : ∀ r i j, T r i j = T i r j) (hT23 : ∀ r i j, T r i j = T r j i)
    (hT : ∀ r i j, T r i j = dslope q (a i) (a j) * Z r i j)
    (hK : ∀ r i j, K r i j = dslope k (a i) (a j) * Z r i j) :
    (∑ r, ∑ i, ∑ j, (Z r i j ^ 2 - K r i j ^ 2 + S (a i) (a j) * Z r i j ^ 2)) ≤
      (∑ r, ∑ i, ∑ j, k (a r) ^ 2 * (q (a i))⁻¹ * (q (a j))⁻¹ * T r i j ^ 2) +
      ∑ r, ∑ i, ∑ j, (q (a r))⁻¹ * (k (a i) + k (a j)) * K r i j * T r i j := by
  let W : n → n → n → ℝ := fun r i j => T r i j ^ 2 / (q (a r) * q (a i) * q (a j))
  have hW : ∀ r i j, 0 ≤ W r i j := fun r i j =>
    div_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (hqpos _).le (hqpos _).le) (hqpos _).le)
  have hW12 : ∀ r i j, W r i j = W i r j := by
    intro r i j
    dsimp [W]
    rw [hT12 r i j]
    congr 1
    ring
  have hW23 : ∀ r i j, W r i j = W r j i := by
    intro r i j
    dsimp [W]
    rw [hT23 r i j]
    congr 1
    ring
  have hfirst : (∑ r, ∑ i, ∑ j, k (a r) ^ 2 * (q (a i))⁻¹ * (q (a j))⁻¹ * T r i j ^ 2) =
      ∑ r, ∑ i, ∑ j,
        ((k (a i) ^ 2 * (q (a r))⁻¹ * (q (a j))⁻¹ +
          k (a j) ^ 2 * (q (a r))⁻¹ * (q (a i))⁻¹) / 2) * T r i j ^ 2 := by
    calc
      _ = ∑ r, ∑ i, ∑ j, k (a i) ^ 2 * (q (a r))⁻¹ * (q (a j))⁻¹ * T r i j ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hT12 i r j]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← Submission.Lib.PairEstimate.sum_transpose_average
          (fun i j => k (a i) ^ 2 * (q (a r))⁻¹ * (q (a j))⁻¹ * T r i j ^ 2)]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hT23 r j i]
        ring
  have hR : (∑ r, ∑ i, ∑ j, k (a r) ^ 2 * (q (a i))⁻¹ * (q (a j))⁻¹ * T r i j ^ 2) +
      (∑ r, ∑ i, ∑ j, (q (a r))⁻¹ * (k (a i) + k (a j)) * K r i j * T r i j) =
      ∑ r, ∑ i, ∑ j, W r i j * ((q (a i) + q (a j)) / 2) * B (a i) (a j) := by
    rw [hfirst]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [W]
    rw [hT r i j, hK r i j]
    exact scalar_multiplier_rewrite _ _ _ _ _ _ _ _ _ (ne_of_gt (hqpos _))
      (ne_of_gt (hqpos _)) (ne_of_gt (hqpos _)) (hc _ _)
  rw [hR]
  refine le_trans ?_ (tensor_rearrangement a q B hqmono hBs hBm W hW hW12 hW23)
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = (1 - (dslope k (a i) (a j)) ^ 2 + S (a i) (a j)) * Z r i j ^ 2 := by
      rw [hK]
      ring
    _ ≤ ((dslope q (a i) (a j)) ^ 2 * B (a i) (a j) / (q (a i) * q (a j))) * Z r i j ^ 2 :=
      mul_le_mul_of_nonneg_right (hs _ _) (sq_nonneg _)
    _ = W r i j * q (a r) * B (a i) (a j) := by
      dsimp [W]
      rw [hT]
      field_simp [ne_of_gt (hqpos (a r)), ne_of_gt (hqpos (a i)), ne_of_gt (hqpos (a j))]
      <;> ring

end Submission.Obl.Entropy__hessian_spectral_surplus
