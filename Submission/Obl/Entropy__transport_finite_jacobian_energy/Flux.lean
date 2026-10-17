import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma tensor_entry_sq_le (H : Fin m → Matrix (Fin m) (Fin m) ℝ) (r i j : Fin m) :
    (H r i j)^2 ≤ ∑ s, ∑ u, ∑ v, (H s u v)^2 := by
  exact (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
    ((Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (Finset.mem_univ r)))

/-- A coarse bound suffices for the compact-cutoff energy argument. -/
lemma trace_flux_sq_bound (P : Matrix (Fin m) (Fin m) ℝ)
    (H : Fin m → Matrix (Fin m) (Fin m) ℝ) {M : ℝ}
    (hM : ∀ s r, |P s r| ≤ M) :
    (∑ s, (∑ r, ∑ i, P s r * H r i i)^2) ≤
      ((m : ℝ)^5 * M^2 + 1) * (∑ r, ∑ i, ∑ j, (H r i j)^2) := by
  let E := ∑ r, ∑ i, ∑ j, (H r i j)^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp (s r i : Fin m) : (P s r * H r i i)^2 ≤ M^2 * E := by
    have hsq : (P s r)^2 ≤ M^2 := by
      have h := hM s r
      nlinarith [sq_abs (P s r), abs_nonneg (P s r)]
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (tensor_entry_sq_le H r i i) (sq_nonneg _))
  have hr (s r : Fin m) : (∑ i, P s r * H r i i)^2 ≤
      (m : ℝ)^2 * M^2 * E := by
    calc
      _ ≤ (m : ℝ) * ∑ i, (P s r * H r i i)^2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => P s r * H r i i)
      _ ≤ (m : ℝ) * ∑ _i : Fin m, M^2 * E := by
        gcongr with i
        exact hp s r i
      _ = _ := by simp; ring
  have hs (s : Fin m) : (∑ r, ∑ i, P s r * H r i i)^2 ≤
      (m : ℝ)^4 * M^2 * E := by
    calc
      _ ≤ (m : ℝ) * ∑ r, (∑ i, P s r * H r i i)^2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun r => ∑ i, P s r * H r i i)
      _ ≤ (m : ℝ) * ∑ _r : Fin m, (m : ℝ)^2 * M^2 * E := by
        gcongr with r
        exact hr s r
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ _s : Fin m, (m : ℝ)^4 * M^2 * E := Finset.sum_le_sum fun s _ => hs s
    _ = (m : ℝ)^5 * M^2 * E := by simp; ring
    _ ≤ _ := by dsimp [E] at *; nlinarith

end Submission.Obl.Entropy__transport_finite_jacobian_energy
