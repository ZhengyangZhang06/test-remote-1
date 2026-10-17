import Mathlib

namespace Submission.Obl.Entropy__equality_cases

open Matrix Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The trace of the coefficient square sum is the sum of entry squares. -/
theorem trace_square_sum (X : ι → Matrix ι ι ℝ) (hX : ∀ r, (X r).IsHermitian) :
    (∑ r, X r * X r).trace = ∑ r, ∑ i, ∑ j, (X r i j) ^ 2 := by
  rw [Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : X r j i = X r i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun (hX r).eq i) j
  rw [h, sq]

omit [DecidableEq ι] in
/-- Bounded entry-square sums give a convergent subsequence of all coefficients together. -/
theorem coefficient_subsequence_of_square_bound
    (X : ℕ → ι → Matrix ι ι ℝ) (C : ℝ)
    (hbound : ∀ n, (∑ r, ∑ i, ∑ j, (X n r i j) ^ 2) ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  let v : ℕ → EuclideanSpace ℝ (ι × ι × ι) :=
    fun n => WithLp.toLp 2 (fun p => X n p.1 p.2.1 p.2.2)
  have hv (n : ℕ) : v n ∈ Metric.closedBall 0 (Real.sqrt C) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖v n‖ = Real.sqrt (‖v n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt (by
        simpa only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, v,
          WithLp.ofLp_toLp] using hbound n)
  obtain ⟨y, _, s, hs, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (ι × ι × ι)))
      (r := Real.sqrt C)) hv
  refine ⟨s, hs, fun r i j => y (r, i, j), ?_⟩
  intro r i j
  exact (EuclideanSpace.proj (r, i, j)).continuous.continuousAt.tendsto.comp hlim

omit [DecidableEq ι] in
/-- A bounded trace of the sum of squares suffices for Hermitian coefficient compactness. -/
theorem hermitian_coefficient_subsequence
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (C : ℝ) (hbound : ∀ n, (∑ r, X n r * X n r).trace ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  apply coefficient_subsequence_of_square_bound X C
  intro n
  simpa only [trace_square_sum _ (hX n)] using hbound n

/-- If the square sum tends to the identity, a subsequence converges to normalized
Hermitian coefficients. This is the finite-dimensional compactness step of Section 6. -/
theorem normalized_coefficient_subsequence
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (hB : ∀ i j, Tendsto (fun n => (∑ r, X n r * X n r) i j) atTop
      (𝓝 ((1 : Matrix ι ι ℝ) i j))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      (∀ r, (Y r).IsHermitian) ∧ (∑ r, Y r * Y r = 1) ∧
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  have ht : Tendsto (fun n => (∑ r, X n r * X n r).trace) atTop
      (𝓝 ((1 : Matrix ι ι ℝ).trace)) := by
    exact tendsto_finsetSum _ (fun i _ => hB i i)
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  obtain ⟨s, hs, Y, hY⟩ := hermitian_coefficient_subsequence X hX C
    (fun n => hC (Set.mem_range_self n))
  have hsym (n : ℕ) (r i j : ι) : X n r j i = X n r i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrFun (congrFun (hX n r).eq i) j
  refine ⟨s, hs, Y, ?_, ?_, hY⟩
  · intro r
    ext i j
    change star (Y r j i) = Y r i j
    simp only [star_trivial]
    exact tendsto_nhds_unique (hY r j i) (by simpa only [hsym] using hY r i j)
  · ext i j
    have hlim := (hB i j).comp hs.tendsto_atTop
    have hprod : Tendsto (fun n => ∑ r, ∑ k, X (s n) r i k * X (s n) r k j) atTop
        (𝓝 (∑ r, ∑ k, Y r i k * Y r k j)) := by
      apply tendsto_finsetSum
      intro r _
      apply tendsto_finsetSum
      intro k _
      exact (hY r i k).mul (hY r k j)
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    exact tendsto_nhds_unique hprod (by
      simpa only [Matrix.sum_apply, Matrix.mul_apply, Function.comp_def] using! hlim)

end Submission.Obl.Entropy__equality_cases
