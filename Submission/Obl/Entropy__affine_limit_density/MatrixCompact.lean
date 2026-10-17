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

theorem diagonal_congruence (P C : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    (P * C * P.transpose) i i = P i ⬝ᵥ (C *ᵥ P i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A nondegenerate limiting covariance makes the compact limit invertible. -/
theorem matrix_subsequence_nonsingular [Nonempty (Fin m)]
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {Cn Pn : ℕ → Matrix (Fin m) (Fin m) ℝ}
    (hCn : Tendsto Cn atTop (𝓝 C))
    (hDn : Tendsto (fun n => Pn n * Cn n * (Pn n).transpose) atTop (𝓝 1)) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, P.det ≠ 0 ∧ ∃ τ : ℕ → ℕ,
      StrictMono τ ∧ Tendsto (Pn ∘ τ) atTop (𝓝 P) := by
  have hdiag (i : Fin m) :
      Tendsto (fun n => Pn n i ⬝ᵥ (Cn n *ᵥ Pn n i)) atTop (𝓝 1) := by
    have h := ((continuous_apply i).comp (continuous_apply i)).tendsto
      (1 : Matrix (Fin m) (Fin m) ℝ) |>.comp hDn
    change Tendsto (fun n => (Pn n * Cn n * (Pn n).transpose) i i) atTop
      (𝓝 ((1 : Matrix (Fin m) (Fin m) ℝ) i i)) at h
    simpa only [diagonal_congruence, Matrix.one_apply_eq] using h
  obtain ⟨P, τ, hτ, hP⟩ := matrix_subsequence_of_covariance hC hCn hdiag
  have hc : Continuous (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      z.1 * z.2 * z.1.transpose) := by fun_prop
  have hp := hc.tendsto (P, C) |>.comp (hP.prodMk_nhds (hCn.comp hτ.tendsto_atTop))
  have heq : P * C * P.transpose = 1 :=
    tendsto_nhds_unique hp (hDn.comp hτ.tendsto_atTop)
  have hdet : P.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det heq
    simp [Matrix.det_mul, h] at this
  exact ⟨P, hdet, τ, hτ, hP⟩

end Submission.Obl.Entropy__affine_limit_density
