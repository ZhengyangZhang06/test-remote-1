import Mathlib

open Set

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Absorb a strict multiple of an initially finite Hölder bound. -/
theorem holder_bound_absorption
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f : X → Y} {α θ B : ℝ} (hα : 0 < α) (hθ₀ : 0 ≤ θ) (hθ : θ < 1)
    (hB : 0 ≤ B)
    (hex : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α)
    (hstep : ∀ C : ℝ, 0 ≤ C →
      (∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) →
      ∀ x y, ‖f x - f y‖ ≤ (θ * C + B) * ‖x - y‖ ^ α) :
    ∀ x y, ‖f x - f y‖ ≤ (B / (1 - θ)) * ‖x - y‖ ^ α := by
  let S : Set ℝ := Set.range (fun p : X × X => ‖f p.1 - f p.2‖ / ‖p.1 - p.2‖ ^ α)
  have hzero : 0 ∈ S := by
    refine ⟨(0, 0), ?_⟩
    simp
  have hupper (C : ℝ) (hC : 0 ≤ C)
      (hc : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) : ∀ z ∈ S, z ≤ C := by
    rintro z ⟨⟨x, y⟩, rfl⟩
    by_cases hxy : x = y
    · simp only [hxy, sub_self, norm_zero, zero_div]
      exact hC
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).mpr (hc x y)
  obtain ⟨C₀, hC₀, hc₀⟩ := hex
  have hbd : BddAbove S := ⟨C₀, hupper C₀ hC₀ hc₀⟩
  have hH : 0 ≤ sSup S := le_csSup hbd hzero
  have hmod : ∀ x y, ‖f x - f y‖ ≤ sSup S * ‖x - y‖ ^ α := by
    intro x y
    by_cases hxy : x = y
    · simp only [hxy, sub_self, norm_zero]
      exact mul_nonneg hH (Real.rpow_nonneg (by norm_num) _)
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).mp
        (le_csSup hbd (mem_range_self (x, y)))
  have hs := hstep (sSup S) hH hmod
  have hnew : 0 ≤ θ * sSup S + B := add_nonneg (mul_nonneg hθ₀ hH) hB
  have hineq : sSup S ≤ θ * sSup S + B := csSup_le ⟨0, hzero⟩ (hupper _ hnew hs)
  have hfinal : sSup S ≤ B / (1 - θ) := (le_div_iff₀ (sub_pos.mpr hθ)).mpr (by nlinarith)
  intro x y
  exact (hmod x y).trans (mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg (norm_nonneg _) _))

end Submission.Obl.Entropy__smooth_gaussian_transport
