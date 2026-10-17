import Submission.Obl.Entropy__linear_transport_limit.Fields

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

open scoped Matrix.Norms.Elementwise

/-- For real symmetric matrices, the trace of the sum of their squares is the sum of
all squared coefficients. -/
theorem trace_sum_squares {m : ℕ} (X : Fin m → Mat m)
    (hX : ∀ r, (X r).IsHermitian) :
    (∑ i, (∑ r, X r * X r) i i) = ∑ r, ∑ i, ∑ j, (X r i j) ^ 2 := by
  simp only [Matrix.sum_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : X r j i = X r i j := by simpa using (hX r).apply i j
  rw [he, pow_two]

theorem coefficient_sq_le_trace {m : ℕ} (X : Fin m → Mat m)
    (hX : ∀ r, (X r).IsHermitian) (r i j : Fin m) :
    (X r i j) ^ 2 ≤ ∑ a, (∑ b, X b * X b) a a := by
  rw [trace_sum_squares X hX]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (X r i k)) (Finset.mem_univ j)).trans
    ((Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (X r k l)))
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ =>
        Finset.sum_nonneg (fun a _ => sq_nonneg (X k l a)))) (Finset.mem_univ r)))

/-- The coefficient compactness step in Section 6, proved using only boundedness of
the trace and finite-dimensional compactness. -/
theorem normalized_coefficient_subsequence {m : ℕ}
    (Xseq : ℕ → Fin m → Mat m)
    (hX : ∀ n r, (Xseq n r).IsHermitian)
    (hB : Tendsto (fun n => ∑ r, Xseq n r * Xseq n r) atTop (𝓝 (1 : Mat m))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ X : Fin m → Mat m,
      Tendsto (fun n => Xseq (σ n)) atTop (𝓝 X) ∧
      (∀ r, (X r).IsHermitian) ∧ ∑ r, X r * X r = (1 : Mat m) := by
  have htr := tendsto_finsetSum Finset.univ
    (fun i _ => (hB.apply_nhds i).apply_nhds i)
  obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ htr).exists_norm_le
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK _ ⟨0, rfl⟩)
  have hbound (n : ℕ) : ‖Xseq n‖ ≤ Real.sqrt K := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr
    intro r
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr
    intro j
    apply (Real.le_sqrt (norm_nonneg _) hK0).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using
      (coefficient_sq_le_trace (Xseq n) (hX n) r i j).trans
        ((le_abs_self _).trans (hK _ ⟨n, rfl⟩))
  obtain ⟨X, _, σ, hσ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin m → Mat m) (Real.sqrt K)).tendsto_subseq
      (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n)
  refine ⟨σ, hσ, X, hlim, ?_, ?_⟩
  · intro r
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply tendsto_nhds_unique (((hlim.apply_nhds r).apply_nhds j).apply_nhds i)
    apply (((hlim.apply_nhds r).apply_nhds i).apply_nhds j).congr'
    exact Eventually.of_forall (fun n => by simpa using ((hX (σ n) r).apply i j).symm)
  · have hc : Continuous (fun Y : Fin m → Mat m => ∑ r, Y r * Y r) := by fun_prop
    exact tendsto_nhds_unique ((hc.tendsto X).comp hlim) (hB.comp hσ.tendsto_atTop)

end Submission.Obl.Entropy__linear_transport_limit
