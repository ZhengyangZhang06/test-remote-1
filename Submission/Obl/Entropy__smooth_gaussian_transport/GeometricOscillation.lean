import Mathlib

open Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A geometric perturbation of a contraction still decays geometrically.
The majorant is uniform over all sequences with the same initial bound. -/
theorem geometric_recursion_bound {θ q E D : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hE : 0 ≤ E) (hD : 0 ≤ D) :
    ∃ β M : ℝ, 0 < β ∧ β < 1 ∧ 0 < M ∧
      ∀ d : ℕ → ℝ, d 0 ≤ D →
        (∀ n, d (n + 1) ≤ θ * d n + E * q ^ n) →
        ∀ n, d n ≤ M * β ^ n := by
  let β : ℝ := (max θ q + 1) / 2
  have hmax : max θ q < 1 := max_lt hθ1 hq1
  have hβ : 0 < β := by dsimp [β]; have := le_max_left θ q; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hθβ : θ < β := by dsimp [β]; have := le_max_left θ q; linarith
  have hqβ : q ≤ β := by dsimp [β]; have := le_max_right θ q; linarith
  let M : ℝ := D + E / (β - θ) + 1
  have hgap : 0 < β - θ := sub_pos.mpr hθβ
  have hfrac : 0 ≤ E / (β - θ) := div_nonneg hE hgap.le
  have hM : 0 < M := by dsimp [M]; linarith
  have hDM : D ≤ M := by dsimp [M]; linarith
  have hEM : E ≤ (β - θ) * M := by
    have hh : E / (β - θ) ≤ M := by dsimp [M]; linarith
    have hb := (div_le_iff₀ hgap).mp hh
    simpa only [mul_comm] using hb
  refine ⟨β, M, hβ, hβ1, hM, ?_⟩
  intro d hd0 hstep n
  induction n with
  | zero => simpa only [pow_zero, mul_one] using hd0.trans hDM
  | succ n ih =>
    calc
      d (n + 1) ≤ θ * d n + E * q ^ n := hstep n
      _ ≤ θ * (M * β ^ n) + E * β ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqβ _) hE)
      _ = (θ * M + E) * β ^ n := by ring
      _ ≤ (M * β) * β ^ n :=
        mul_le_mul_of_nonneg_right (by nlinarith [hEM]) (pow_nonneg hβ.le _)
      _ = M * β ^ (n + 1) := by rw [pow_succ]; ring

theorem tendsto_zero_of_geometric_bound {d : ℕ → ℝ} {M β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hd : ∀ n, 0 ≤ d n)
    (hbound : ∀ n, d n ≤ M * β ^ n) : Tendsto d atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => M * β ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := M)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1)
  exact squeeze_zero hd hbound ht

end Submission.Obl.Entropy__smooth_gaussian_transport
