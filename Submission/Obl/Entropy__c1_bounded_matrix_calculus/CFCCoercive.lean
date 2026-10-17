/-
Adapted from: here:o006
Original matrix functional-calculus derivative proofs by session x0063.
-/

import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCContinuity

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__c1_bounded_matrix_calculus

lemma dslope_ge_of_deriv_ge {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hf : Differentiable ℝ f) {c a b : ℝ}
    (hbound : ∀ t ∈ s, c ≤ deriv f t) (ha : a ∈ s) (hb : b ∈ s) :
    c ≤ dslope f a b := by
  have hinc := hs.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn (fun t ht => hbound t (interior_subset ht))
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [dslope_of_ne f (ne_of_gt hab), slope_def_field]
    exact (le_div_iff₀ (sub_pos.2 hab)).2 (hinc a ha b hb hab.le)
  · subst b
    simpa only [dslope_same] using hbound a ha
  · rw [dslope_of_ne f (ne_of_lt hab), slope_comm, slope_def_field]
    exact (le_div_iff₀ (sub_pos.2 hab)).2 (hinc b hb a ha hab.le)

lemma exists_dslope_pos_lower_Icc {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a ≤ b) (hpos : ∀ t ∈ Set.Icc a b, 0 < deriv f t) :
    ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      c ≤ dslope f u v := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab)
    (hf.continuous_deriv (by norm_num)).continuousOn
  exact ⟨deriv f t, hpos t ht, fun u hu v hv =>
    dslope_ge_of_deriv_ge (convex_Icc a b) (hf.differentiable (by norm_num)) hmin hu hv⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive scalar slope lower bound controls the matrix derivative from below. -/
lemma spectralDerivative_squareSum_ge {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (H : Matrix n n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ i j, c ≤ |dslope f (hA.eigenvalues i) (hA.eigenvalues j)|) :
    c^2 * matrixSquareSum H ≤ matrixSquareSum (spectralDerivative hA f H) := by
  rw [← matrixSquareSum_eigenbasis hA (spectralDerivative hA f H),
    ← matrixSquareSum_eigenbasis hA H]
  simp only [matrixSquareSum, spectralDerivative_eigenbasis, Finset.mul_sum, mul_pow]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ hc (abs_nonneg _)).2 (hbound i j)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma entryDirectionalDerivative_cfc_squareSum_ge (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : spectrum ℝ (A x) ⊆ s)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ t ∈ s, c ≤ deriv f t) :
    c^2 * matrixSquareSum (entryDirectionalDerivative A x v) ≤
      matrixSquareSum (entryDirectionalDerivative (fun y => cfc f (A y)) x v) := by
  rw [entryDirectionalDerivative_cfc A hAc hAH hf hAd]
  apply spectralDerivative_squareSum_ge (hAH x) f _ hc
  intro i j
  exact (dslope_ge_of_deriv_ge hs hf hbound
    (hspec ((hAH x).eigenvalues_mem_spectrum_real i))
    (hspec ((hAH x).eigenvalues_mem_spectrum_real j))).trans (le_abs_self _)

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- Recover square-integrable parameter derivatives from square-integrable
Jacobian derivatives when the scalar derivative has a positive lower bound. -/
lemma memLp_entryDirectionalDerivative_of_cfc (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : ∀ x, spectrum ℝ (A x) ⊆ s)
    {c : ℝ} (hc : 0 < c) (hbound : ∀ t ∈ s, c ≤ deriv f t)
    (hLp : ∀ i j, MemLp
      (fun x => entryDirectionalDerivative (fun y => cfc f (A y)) x v i j) 2 μ) :
    ∀ i j, MemLp (fun x => entryDirectionalDerivative A x v i j) 2 μ := by
  apply memLp_entries_of_squareSum_bound
    (G := fun x => entryDirectionalDerivative (fun y => cfc f (A y)) x v)
    (C := (c^2)⁻¹) _ hLp
  · intro x
    have h := entryDirectionalDerivative_cfc_squareSum_ge A hAc hAH hf (hAd x) v
      hs (hspec x) hc.le hbound
    calc
      matrixSquareSum (entryDirectionalDerivative A x v) =
          (c^2)⁻¹ * (c^2 * matrixSquareSum (entryDirectionalDerivative A x v)) := by
            field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 (sq_nonneg _))
  · intro i j
    exact (measurable_fderiv_apply_const ℝ (fun y => A y i j) v).aestronglyMeasurable

end Submission.Obl.Entropy__c1_bounded_matrix_calculus
