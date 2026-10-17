import Submission.Obl.Entropy__normalized_remainder.CFCField
import Submission.Lib.PairEstimate.Integration

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__normalized_remainder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma entry_sq_le_matrixSquareSum (H : Matrix n n ℝ) (i j : n) :
    (H i j)^2 ≤ matrixSquareSum H := by
  calc
    (H i j)^2 ≤ ∑ k, (H i k)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ l, ∑ k, (H l k)^2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
        (Finset.mem_univ i)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

omit [DecidableEq n] in
lemma integrable_matrixSquareSum {F : α → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ) :
    Integrable (fun x => matrixSquareSum (F x)) μ :=
  Submission.Lib.PairEstimate.integrable_squareSum hF

omit [DecidableEq n] in
lemma memLp_entries_of_squareSum_bound {F G : α → Matrix n n ℝ} {C : ℝ}
    (hF : ∀ i j, AEStronglyMeasurable (fun x => F x i j) μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ)
    (hbound : ∀ x, matrixSquareSum (F x) ≤ C * matrixSquareSum (G x)) :
    ∀ i j, MemLp (fun x => F x i j) 2 μ := by
  intro i j
  apply (memLp_two_iff_integrable_sq (hF i j)).2
  apply ((integrable_matrixSquareSum hG).const_mul C).mono_nonneg ((hF i j).pow 2)
  · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x => (entry_sq_le_matrixSquareSum (F x) i j).trans (hbound x))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {ν : Measure E}

/-- Scalar CFC preserves square-integrable directional derivatives on a bounded
spectral interval. This is valid for any measure, in particular the Gaussian. -/
lemma memLp_entryDirectionalDerivative_cfc (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : ∀ x, spectrum ℝ (A x) ⊆ s)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t ∈ s, |deriv f t| ≤ C)
    (hLp : ∀ i j, MemLp (fun x => entryDirectionalDerivative A x v i j) 2 ν) :
    ∀ i j, MemLp (fun x => entryDirectionalDerivative (fun y => cfc f (A y)) x v i j) 2 ν := by
  apply memLp_entries_of_squareSum_bound (G := fun x => entryDirectionalDerivative A x v)
    (C := C^2) _ hLp
  · intro x
    exact entryDirectionalDerivative_cfc_squareSum_le A hAc hAH hf (hAd x) v
      hs (hspec x) hC hbound
  · intro i j
    exact (measurable_fderiv_apply_const ℝ (fun y => cfc f (A y) i j) v).aestronglyMeasurable

/-- The pointwise matrix derivative estimate integrates without a change of constant. -/
lemma integral_entryDirectionalDerivative_cfc_le (A : E → Matrix n n ℝ)
    (hAc : ∀ i j, Continuous (fun y => A y i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : ∀ x, spectrum ℝ (A x) ⊆ s)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t ∈ s, |deriv f t| ≤ C)
    (hLp : ∀ i j, MemLp (fun x => entryDirectionalDerivative A x v i j) 2 ν) :
    (∫ x, matrixSquareSum (entryDirectionalDerivative (fun y => cfc f (A y)) x v) ∂ν) ≤
      C^2 * ∫ x, matrixSquareSum (entryDirectionalDerivative A x v) ∂ν := by
  rw [← integral_const_mul]
  apply integral_mono
    (integrable_matrixSquareSum
      (memLp_entryDirectionalDerivative_cfc A hAc hAH hf hAd v hs hspec hC hbound hLp))
    ((integrable_matrixSquareSum hLp).const_mul (C^2))
  intro x
  exact entryDirectionalDerivative_cfc_squareSum_le A hAc hAH hf (hAd x) v hs
    (hspec x) hC hbound

end Submission.Obl.Entropy__normalized_remainder
