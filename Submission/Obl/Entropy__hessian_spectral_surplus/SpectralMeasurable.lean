import Submission.Obl.Entropy__hessian_spectral_surplus.CFCDerivative

open scoped BigOperators Topology
open Matrix Filter MeasureTheory

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- On a finite spectrum, pointwise convergence of scalar functions implies convergence of CFC. -/
lemma tendsto_cfc_matrix_of_pointwise {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (h : ∀ a, Tendsto (fun k => f k a) l (𝓝 (g a))) :
    Tendsto (fun k => cfc (f k) A) l (𝓝 (cfc g A)) := by
  simp only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  apply Filter.Tendsto.mul _ tendsto_const_nhds
  apply Filter.Tendsto.mul tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simpa using h (hA.eigenvalues i)
  · simpa [Matrix.diagonal_apply_ne _ hij] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))

/-- Right-continuous spectral cutoffs are measurable, without choosing measurable eigenvectors. -/
lemma measurable_cfc_cutoff {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {A : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) (c : ℝ) (i j : n) :
    Measurable (fun x => cfc (fun t : ℝ => if c ≤ t then 1 else 0) (A x) i j) := by
  let f : ℕ → ℝ → ℝ := fun k t => max 0 (min 1 (1 + (k : ℝ) * (t - c)))
  have hc (k : ℕ) : Continuous (f k) := by dsimp [f]; fun_prop
  have ht (t : ℝ) : Tendsto (fun k => f k t) atTop
      (𝓝 (if c ≤ t then (1 : ℝ) else 0)) := by
    by_cases hct : c ≤ t
    · have heq : ∀ k, f k t = 1 := by
        intro k
        have hp : 0 ≤ (k : ℝ) * (t - c) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hct)
        simp only [f, min_eq_left (by linarith : (1 : ℝ) ≤ 1 + (k : ℝ) * (t - c))]
        norm_num
      simpa only [heq, if_pos hct] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · have hpos : 0 < c - t := sub_pos.mpr (lt_of_not_ge hct)
      have hev : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / (c - t) ≤ k :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
      have heq : (fun k => f k t) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
        filter_upwards [hev] with k hk
        have hk' := (div_le_iff₀ hpos).mp hk
        have hn : 1 + (k : ℝ) * (t - c) ≤ 0 := by nlinarith
        simp only [f, min_eq_right (by linarith : 1 + (k : ℝ) * (t - c) ≤ 1),
          max_eq_left hn]
      simpa only [if_neg hct] using tendsto_const_nhds.congr' heq.symm
  apply measurable_of_tendsto_metrizable
    (fun k => ((continuous_cfc_matrix hA hAc (hc k)).matrix_elem i j).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((tendsto_pi_nhds.mp (tendsto_cfc_matrix_of_pointwise (hA x) ht)) i).apply_nhds j

end Submission.Obl.Entropy__hessian_spectral_surplus
