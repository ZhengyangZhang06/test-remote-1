import Submission.Obl.Entropy__normalized_remainder.CFCCoercive

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__normalized_remainder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Uniform entry bounds give a common compact interval for every spectrum. -/
lemma exists_spectrum_subset_Icc_of_bounded_entries {α : Type*}
    (A : α → Matrix n n ℝ) (hAH : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, spectrum ℝ (A x) ⊆ Set.Icc (-R) R := by
  obtain ⟨K, hK, hbound⟩ := hbound
  let L : (n → n → ℝ) →L[ℝ] Matrix n n ℝ :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let R : ℝ := ‖L‖ * K + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun x t ht => ?_⟩
  have hpi : ‖fun i j => A x i j‖ ≤ K := by
    apply (pi_norm_le_iff_of_nonneg hK.le).2
    intro i
    apply (pi_norm_le_iff_of_nonneg hK.le).2
    intro j
    simpa only [Real.norm_eq_abs] using hbound x i j
  have hnorm : ‖A x‖ ≤ ‖L‖ * K :=
    (L.le_opNorm (fun i j => A x i j)).trans
      (mul_le_mul_of_nonneg_left hpi (norm_nonneg L))
  have ht' := IsometricContinuousFunctionalCalculus.norm_spectrum_le (A x) ht
    (hAH x).isSelfAdjoint
  rw [Real.norm_eq_abs] at ht'
  have : |t| ≤ R := ht'.trans (hnorm.trans (by dsimp [R]; linarith))
  exact abs_le.1 this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- A scalar C1 function preserves L2 derivatives of a bounded Hermitian field. -/
lemma memLp_entryDirectionalDerivative_cfc_of_bounded (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    (hLp : ∀ i j, MemLp (fun x => entryDirectionalDerivative A x v i j) 2 μ) :
    ∀ i j, MemLp (fun x =>
      entryDirectionalDerivative (fun y => cfc f (A y)) x v i j) 2 μ := by
  obtain ⟨R, _, hspec⟩ := exists_spectrum_subset_Icc_of_bounded_entries A hAH hbound
  obtain ⟨C, hC, hCbound⟩ := exists_dslope_bound_Icc hf (-R) R
  exact memLp_entryDirectionalDerivative_cfc A hAc hAH (hf.differentiable (by norm_num))
    hAd v (convex_Icc (-R) R) hspec hC.le
    (fun t ht => by simpa only [dslope_same] using hCbound t ht t ht) hLp

/-- A strictly positive scalar derivative recovers L2 derivatives of a bounded
Hermitian parameter field from L2 derivatives of its CFC image. -/
lemma memLp_entryDirectionalDerivative_of_cfc_of_bounded (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hpos : ∀ t, 0 < deriv f t)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    (hLp : ∀ i j, MemLp (fun x =>
      entryDirectionalDerivative (fun y => cfc f (A y)) x v i j) 2 μ) :
    ∀ i j, MemLp (fun x => entryDirectionalDerivative A x v i j) 2 μ := by
  obtain ⟨R, hR, hspec⟩ := exists_spectrum_subset_Icc_of_bounded_entries A hAH hbound
  obtain ⟨c, hc, hcbound⟩ := exists_dslope_pos_lower_Icc hf (by linarith : -R ≤ R)
    (fun t _ => hpos t)
  exact memLp_entryDirectionalDerivative_of_cfc A hAc hAH (hf.differentiable (by norm_num))
    hAd v (convex_Icc (-R) R) hspec hc
    (fun t ht => by simpa only [dslope_same] using hcbound t ht t ht) hLp

end Submission.Obl.Entropy__normalized_remainder
