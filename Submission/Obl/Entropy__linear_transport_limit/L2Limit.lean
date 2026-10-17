import Submission.Obl.Entropy__linear_transport_limit.Energy

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

variable {α B : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

theorem L2_norm_sq (f : Lp B 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem toLp_norm_sq {f : α → B} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [L2_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun v => ‖v‖ ^ 2))

theorem toLp_dist_sq {f g : α → B} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [dist_eq_norm, ← MemLp.toLp_sub, toLp_norm_sq]
  rfl

theorem cauchySeq_toLp_of_energy_cauchy {f : ℕ → α → B}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ x, ‖f n x - f k x‖ ^ 2 ∂μ) < ε) :
    CauchySeq (fun n => (hf n).toLp (f n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn k hk => ?_⟩
  have hh := hN n hn k hk
  rw [← toLp_dist_sq (hf n) (hf k)] at hh
  nlinarith

variable [CompleteSpace B]

theorem exists_L2_limit_of_energy_cauchy {f : ℕ → α → B}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ x, ‖f n x - f k x‖ ^ 2 ∂μ) < ε) :
    ∃ g : α → B, MemLp g 2 μ ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_toLp_of_energy_cauchy hf hc)
  refine ⟨g, (Lp.memLp g), ?_⟩
  have hd := hg.dist (tendsto_const_nhds (x := g))
  have hs := hd.pow 2
  simp only [dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
  have heq (n : ℕ) : dist ((hf n).toLp (f n)) g ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
    simpa only [Lp.toLp_coeFn] using toLp_dist_sq (hf n) (Lp.memLp g)
  simpa only [heq] using hs

/-- Integration against constants is an L2 inner product, so centering is closed. -/
theorem integral_eq_zero_of_L2_limit [IsFiniteMeasure μ]
    {f : ℕ → α → B} {g : α → B}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ n, ∫ x, f n x ∂μ = 0)
    (hlim : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∫ x, g x ∂μ = 0 := by
  have hdist : Tendsto (fun n => dist ((hf n).toLp (f n)) (hg.toLp g)) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hlim
    have heq (n : ℕ) : Real.sqrt (∫ x, ‖f n x - g x‖ ^ 2 ∂μ) =
        dist ((hf n).toLp (f n)) (hg.toLp g) := by
      rw [← toLp_dist_sq (hf n) hg, Real.sqrt_sq dist_nonneg]
    simpa only [Function.comp_def, heq, Real.sqrt_zero] using hs
  have ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) :=
    (tendsto_iff_dist_tendsto_zero).mpr hdist
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ g (hg.integrable (by norm_num))
  intro v
  let c := (memLp_const v : MemLp (fun _ : α => v) 2 μ).toLp (fun _ => v)
  have hinner (h : α → B) (hh : MemLp h 2 μ) :
      inner ℝ c (hh.toLp h) = inner ℝ v (∫ x, h x ∂μ) := by
    rw [L2.inner_def, ← integral_inner (hh.integrable (by norm_num))]
    apply integral_congr_ae
    filter_upwards [(memLp_const v : MemLp (fun _ : α => v) 2 μ).coeFn_toLp,
      hh.coeFn_toLp] with x hx hy
    dsimp only [c]
    simp only [hx, hy]
  have hi := (tendsto_const_nhds (x := c)).inner (𝕜 := ℝ) ht
  have hi0 : Tendsto (fun n => inner ℝ c ((hf n).toLp (f n))) atTop (𝓝 0) := by
    simpa only [hinner, hf0, inner_zero_right] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hz := tendsto_nhds_unique hi hi0
  rw [hinner] at hz
  rw [integral_inner (hg.integrable (by norm_num))]
  exact hz

theorem exists_centered_L2_limit_of_energy_cauchy [IsFiniteMeasure μ]
    {f : ℕ → α → B} (hf : ∀ n, MemLp (f n) 2 μ)
    (hf0 : ∀ n, ∫ x, f n x ∂μ = 0)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ x, ‖f n x - f k x‖ ^ 2 ∂μ) < ε) :
    ∃ g : α → B, MemLp g 2 μ ∧ (∫ x, g x ∂μ) = 0 ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨g, hg, hlim⟩ := exists_L2_limit_of_energy_cauchy hf hc
  exact ⟨g, hg, integral_eq_zero_of_L2_limit hf hg hf0 hlim, hlim⟩

/-- An L2 convergence theorem with the only analytic input isolated as a bound on
centered differences. -/
theorem exists_centered_L2_limit_of_difference_bound [IsFiniteMeasure μ]
    {D : Type*} [NormedAddCommGroup D]
    {f : ℕ → α → B} {Jseq : ℕ → α → D} {J : α → D}
    (hf : ∀ n, MemLp (f n) 2 μ) (hf0 : ∀ n, ∫ x, f n x ∂μ = 0)
    (hJseq : ∀ n, MemLp (Jseq n) 2 μ) (hJ : MemLp J 2 μ)
    (hlim : Tendsto (fun n => ∫ x, ‖Jseq n x - J x‖ ^ 2 ∂μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ n k, (∫ x, ‖f n x - f k x‖ ^ 2 ∂μ) ≤
      C * ∫ x, ‖Jseq n x - Jseq k x‖ ^ 2 ∂μ) :
    ∃ g : α → B, MemLp g 2 μ ∧ (∫ x, g x ∂μ) = 0 ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply exists_centered_L2_limit_of_energy_cauchy hf hf0
  intro ε hε
  have hd : 0 < ε / (4 * C) := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hd))
  refine ⟨N, fun n hn k hk => ?_⟩
  have ht := integral_norm_sub_sq_triangle (hJseq n) hJ (hJseq k)
  simp only [norm_sub_rev (J _) (Jseq k _)] at ht
  have he : 4 * C * (ε / (4 * C)) = ε := by field_simp
  have hn' := mul_lt_mul_of_pos_left (hN n hn) hC
  have hk' := mul_lt_mul_of_pos_left (hN k hk) hC
  have hle := (hbound n k).trans (mul_le_mul_of_nonneg_left ht hC.le)
  nlinarith

end Submission.Obl.Entropy__linear_transport_limit
