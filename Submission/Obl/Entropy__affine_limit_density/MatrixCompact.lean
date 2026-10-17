import Mathlib

open Filter Set
open scoped Topology Matrix

namespace Submission.Obl.Entropy__affine_limit_density
open scoped Matrix.Norms.Elementwise

variable {m : ℕ}

/-- Positive definiteness gives a uniform lower bound for nearby quadratic forms. -/
theorem eventually_quadratic_lower_bound [Nonempty (Fin m)]
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ D in 𝓝 C, ∀ u : Fin m → ℝ,
      c * ‖u‖ ^ 2 ≤ u ⬝ᵥ (D *ᵥ u) := by
  let q := fun (D : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) => u ⬝ᵥ (D *ᵥ u)
  have hcont : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      q p.1 p.2) := by
    dsimp [q, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : Fin m → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num))
    ((hcont.comp ((continuous_const (y := C)).prodMk continuous_id)).continuousOn)
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
  have hv0 : v ≠ 0 := by intro h; simp [h] at hvnorm
  have hpos : 0 < q C v := by simpa [q] using hC.dotProduct_mulVec_pos hv0
  refine ⟨q C v / 2, half_pos hpos, ?_⟩
  have hev : ∀ᶠ D in 𝓝 C, ∀ u ∈ Metric.sphere (0 : Fin m → ℝ) 1,
      q C v / 2 < q D u := by
    apply (isCompact_sphere (0 : Fin m → ℝ) 1).eventually_forall_of_forall_eventually
    intro u hu
    have hlt : q C v / 2 < q C u := by
      have hle : q C v ≤ q C u := hmin hu
      linarith
    exact hcont.continuousAt.eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with D hD u
  by_cases hu : u = 0
  · simp [hu, q]
  have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hunit : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hu
  have h := (hD _ hunit).le
  have heq : q D (‖u‖⁻¹ • u) = ‖u‖⁻¹ ^ 2 * q D u := by
    simp only [q, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [heq] at h
  have := mul_le_mul_of_nonneg_left h (sq_nonneg ‖u‖)
  field_simp at this ⊢
  nlinarith

/-- Covariance control bounds a sequence of arbitrary, possibly nonsymmetric, matrices. -/
theorem matrix_subsequence_of_covariance [Nonempty (Fin m)]
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {Cn Pn : ℕ → Matrix (Fin m) (Fin m) ℝ}
    (hCn : Tendsto Cn atTop (𝓝 C))
    (hPn : ∀ i, Tendsto (fun n => Pn n i ⬝ᵥ (Cn n *ᵥ Pn n i)) atTop (𝓝 1)) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, ∃ τ : ℕ → ℕ,
      StrictMono τ ∧ Tendsto (Pn ∘ τ) atTop (𝓝 P) := by
  obtain ⟨c, hc, hlocal⟩ := eventually_quadratic_lower_bound hC
  have hdiag : ∀ᶠ n in atTop, ∀ i, Pn n i ⬝ᵥ (Cn n *ᵥ Pn n i) ≤ 2 := by
    rw [eventually_all]
    intro i
    exact (hPn i).eventually (ge_mem_nhds (by norm_num))
  have hbdd : ∀ᶠ n in atTop, Pn n ∈ Metric.closedBall 0 (2 / c + 1) := by
    filter_upwards [hCn.eventually hlocal, hdiag] with n hn hd
    rw [Metric.mem_closedBall, dist_zero_right, Matrix.norm_def, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hsq : ‖Pn n i‖ ^ 2 ≤ 2 / c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using (hn (Pn n i)).trans (hd i)
    nlinarith [sq_nonneg (‖Pn n i‖ - 1)]
  obtain ⟨P, _, τ, hτ, hlim⟩ := (isCompact_closedBall (0 : Matrix (Fin m) (Fin m) ℝ)
    (2 / c + 1)).tendsto_subseq' hbdd.frequently
  exact ⟨P, τ, hτ, hlim⟩

end Submission.Obl.Entropy__affine_limit_density
