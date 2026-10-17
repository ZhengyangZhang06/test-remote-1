import Mathlib

/-!
The symmetric third-tensor rearrangement in Proposition 2.5. The abstract
pair function is an arithmetic interval average of an increasing scalar
function. It suffices that it is symmetric and increasing in each endpoint.
-/

namespace Submission.Obl.Entropy__transport_energy_surplus

open scoped BigOperators

private theorem monotone_sub_mul_sub_nonneg (f : ℝ → ℝ) (hf : Monotone f)
    (x y : ℝ) : 0 ≤ (x - y) * (f x - f y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (hf h))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hf h))

/-- Rearrangement for one unordered triple, with repeated eigenvalues allowed. -/
theorem triple_rearrangement (B : ℝ → ℝ → ℝ)
    (hB : ∀ x y, B x y = B y x) (hmono : ∀ y, Monotone (fun x => B x y))
    (u v w : ℝ) :
    0 ≤ (u + v - 2 * w) * B u v + (u + w - 2 * v) * B u w +
      (v + w - 2 * u) * B v w := by
  have h1 := monotone_sub_mul_sub_nonneg (fun x => B x w) (hmono w) u v
  have h2 := monotone_sub_mul_sub_nonneg (fun x => B x v) (hmono v) u w
  have h3 := monotone_sub_mul_sub_nonneg (fun x => B x u) (hmono u) v w
  rw [hB w v] at h2
  rw [hB v u, hB w u] at h3
  nlinarith only [h1, h2, h3]

private theorem sum_triple_cycle {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ r, f i j r) = ∑ i, ∑ j, ∑ r, f r i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- Full symmetry of the third tensor permits replacing the average of the first
 two eigenvalues by the third eigenvalue inside the integrated multiplier. -/
theorem symmetric_tensor_rearrangement {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (W : ι → ι → ι → ℝ) (B : ℝ → ℝ → ℝ)
    (hW : ∀ i j r, 0 ≤ W i j r)
    (hWcycle : ∀ i j r, W i j r = W r i j)
    (hWswap : ∀ i j r, W i j r = W i r j)
    (hB : ∀ x y, B x y = B y x) (hmono : ∀ y, Monotone (fun x => B x y)) :
    (∑ i, ∑ j, ∑ r, W i j r * lam r * B (lam i) (lam j)) ≤
      ∑ i, ∑ j, ∑ r, W i j r * ((lam i + lam j) / 2) * B (lam i) (lam j) := by
  let T : ι → ι → ι → ℝ := fun i j r =>
    W i j r * (lam i + lam j - 2 * lam r) * B (lam i) (lam j)
  have hcycle1 : (∑ i, ∑ j, ∑ r, T i r j) = ∑ i, ∑ j, ∑ r, T i j r := by
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have hcycle2 : (∑ i, ∑ j, ∑ r, T j r i) = ∑ i, ∑ j, ∑ r, T i j r := by
    rw [sum_triple_cycle]
  have hpoint : ∀ i j r, 0 ≤ T i j r + T i r j + T j r i := by
    intro i j r
    have h := mul_nonneg (hW i j r) (triple_rearrangement B hB hmono (lam i) (lam j) (lam r))
    dsimp [T]
    rw [← hWswap i j r, hWcycle j r i]
    nlinarith only [h]
  have h := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      Finset.sum_nonneg fun r (_ : r ∈ (Finset.univ : Finset ι)) => hpoint i j r
  simp_rw [Finset.sum_add_distrib] at h
  rw [hcycle1, hcycle2] at h
  dsimp [T] at h
  have he : (∑ i, ∑ j, ∑ r, W i j r * (lam i + lam j - 2 * lam r) * B (lam i) (lam j)) =
      2 * ((∑ i, ∑ j, ∑ r, W i j r * ((lam i + lam j) / 2) * B (lam i) (lam j)) -
        ∑ i, ∑ j, ∑ r, W i j r * lam r * B (lam i) (lam j)) := by
    rw [mul_sub]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he] at h
  linarith

end Submission.Obl.Entropy__transport_energy_surplus
