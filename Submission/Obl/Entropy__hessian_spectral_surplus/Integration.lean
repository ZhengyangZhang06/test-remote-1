import Submission.Lib.PairEstimate.Integration

open scoped BigOperators
open MeasureTheory

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

lemma integrate_surplus {μ : Measure X} {Z K : n → X → Matrix n n ℝ} {S R : X → ℝ}
    (hZ : ∀ r i j, MemLp (fun x => Z r x i j) 2 μ)
    (hK : ∀ r i j, MemLp (fun x => K r x i j) 2 μ)
    (hS : Measurable S) (hS0 : ∀ x, 0 ≤ S x) (hR : Integrable R μ)
    (hpoint : ∀ x, (∑ r, ∑ i, ∑ j, Z r x i j ^ 2) -
      (∑ r, ∑ i, ∑ j, K r x i j ^ 2) + S x ≤ R x) :
    Integrable S μ ∧
      (∑ r, ∫ x, ∑ i, ∑ j, Z r x i j ^ 2 ∂μ) -
      (∑ r, ∫ x, ∑ i, ∑ j, K r x i j ^ 2 ∂μ) + ∫ x, S x ∂μ ≤ ∫ x, R x ∂μ := by
  have hZi (r : n) := Submission.Lib.PairEstimate.integrable_squareSum (hZ r)
  have hKi (r : n) := Submission.Lib.PairEstimate.integrable_squareSum (hK r)
  have hZsum := integrable_finsetSum Finset.univ (fun r _ => hZi r)
  have hKsum := integrable_finsetSum Finset.univ (fun r _ => hKi r)
  have hSi : Integrable S μ := by
    apply (hR.add hKsum).mono' hS.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 x)]
    have hZ0 : 0 ≤ ∑ r, ∑ i, ∑ j, Z r x i j ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hp := hpoint x
    change S x ≤ R x + ∑ r, ∑ i, ∑ j, K r x i j ^ 2
    linarith
  refine ⟨hSi, ?_⟩
  have h := integral_mono ((hZsum.sub hKsum).add hSi) hR hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at h
  erw [integral_add (hZsum.sub hKsum) hSi, integral_sub hZsum hKsum,
    integral_finsetSum _ (fun r _ => hZi r), integral_finsetSum _ (fun r _ => hKi r)] at h
  exact h

end Submission.Obl.Entropy__hessian_spectral_surplus
