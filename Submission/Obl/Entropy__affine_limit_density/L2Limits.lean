import Mathlib

open MeasureTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__affine_limit_density

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The stated squared-distance integral is the usual strong L2 topology. -/
theorem tendsto_toLp_of_integral_sq {fn : ℕ → α → E} {f : α → E}
    (hn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun n => ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)) := by
  have he (n : ℕ) : ‖(hn n).toLp (fn n) - hf.toLp f‖ ^ 2 =
      ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ := by
    rw [← (hn n).toLp_sub hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((hn n).sub hf).coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
    rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := hlim.sqrt
  simpa only [← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- Scalar continuous linear observations preserve the L2 inner-product limit. -/
theorem tendsto_integral_observation_mul {fn : ℕ → α → E} {f : α → E}
    (hn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun n => ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (a b : E →L[ℝ] ℝ) :
    Tendsto (fun n => ∫ x, a (fn n x) * b (fn n x) ∂μ) atTop
      (𝓝 (∫ x, a (f x) * b (f x) ∂μ)) := by
  have ht := tendsto_toLp_of_integral_sq hn hf hlim
  have ha := (a.compLpL 2 μ).continuous.tendsto (hf.toLp f) |>.comp ht
  have hb := (b.compLpL 2 μ).continuous.tendsto (hf.toLp f) |>.comp ht
  have hi := ha.inner hb (𝕜 := ℝ)
  have he (g : α → E) (hg : MemLp g 2 μ) :
      inner ℝ ((a.compLpL 2 μ) (hg.toLp g)) ((b.compLpL 2 μ) (hg.toLp g)) =
        ∫ x, a (g x) * b (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [a.coeFn_compLpL (hg.toLp g), b.coeFn_compLpL (hg.toLp g),
      hg.coeFn_toLp] with x hax hbx hx
    simp [hax, hbx, hx, mul_comm]
  simpa only [Function.comp_apply, he] using hi

/-- Strong L2 convergence supplies an almost-everywhere convergent subsequence. -/
theorem exists_ae_subsequence_of_integral_sq {fn : ℕ → α → E} {f : α → E}
    (hn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun n => ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => fn (τ n) x) atTop (𝓝 (f x)) := by
  have h := tendstoInMeasure_of_tendsto_Lp (tendsto_toLp_of_integral_sq hn hf hlim)
  have h' : TendstoInMeasure μ fn atTop f :=
    h.congr (fun n => (hn n).coeFn_toLp) hf.coeFn_toLp
  exact h'.exists_seq_tendsto_ae

end Submission.Obl.Entropy__affine_limit_density
