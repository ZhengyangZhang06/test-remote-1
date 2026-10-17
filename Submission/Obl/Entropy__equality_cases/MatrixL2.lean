import Submission.Obl.Entropy__equality_cases.Frobenius

namespace Submission.Obl.Entropy__equality_cases

open MeasureTheory Filter Matrix
open scoped Topology

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

/-- Entrywise L2 hypotheses make the squared Frobenius difference integrable. -/
theorem integrable_frobeniusSq_sub (μ : Measure Ω) (A B : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 μ)
    (hB : ∀ i j, MemLp (fun x => B x i j) 2 μ) :
    Integrable (fun x => frobeniusSq (A x - B x)) μ := by
  simp only [frobeniusSq_eq_sum, Matrix.sub_apply]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((hA i j).sub (hB i j)).integrable_sq

/-- The elementary squared triangle bound, with its exact constant. -/
theorem frobeniusSq_sub_le (A B C : Matrix ι ι ℝ) :
    frobeniusSq (A - C) ≤ 2 * frobeniusSq (A - B) + 2 * frobeniusSq (B - C) := by
  simp only [frobeniusSq_eq_sum, Matrix.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  nlinarith [sq_nonneg (A i j - 2 * B i j + C i j)]

/-- A vanishing L2 residual transfers convergence from the approximating linear fields. -/
theorem frobeniusSq_L2_tendsto_trans {α : Type*} {l : Filter α}
    (μ : Measure Ω) (A B : α → Ω → Matrix ι ι ℝ) (C : Ω → Matrix ι ι ℝ)
    (hA : ∀ n i j, MemLp (fun x => A n x i j) 2 μ)
    (hB : ∀ n i j, MemLp (fun x => B n x i j) 2 μ)
    (hC : ∀ i j, MemLp (fun x => C x i j) 2 μ)
    (hAB : Tendsto (fun n => ∫ x, frobeniusSq (A n x - B n x) ∂μ) l (𝓝 0))
    (hBC : Tendsto (fun n => ∫ x, frobeniusSq (B n x - C x) ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, frobeniusSq (A n x - C x) ∂μ) l (𝓝 0) := by
  have hnonneg (n : α) : 0 ≤ ∫ x, frobeniusSq (A n x - C x) ∂μ := by
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ frobeniusSq (A n x - C x)
    rw [frobeniusSq_eq_sum]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hle (n : α) : (∫ x, frobeniusSq (A n x - C x) ∂μ) ≤
      2 * (∫ x, frobeniusSq (A n x - B n x) ∂μ) +
      2 * (∫ x, frobeniusSq (B n x - C x) ∂μ) := by
    have hABi := integrable_frobeniusSq_sub μ (A n) (B n) (hA n) (hB n)
    have hBCi := integrable_frobeniusSq_sub μ (B n) C (hB n) hC
    calc
      _ ≤ ∫ x, 2 * frobeniusSq (A n x - B n x) + 2 * frobeniusSq (B n x - C x) ∂μ :=
        integral_mono (integrable_frobeniusSq_sub μ (A n) C (hA n) hC)
          ((hABi.const_mul 2).add (hBCi.const_mul 2)) (fun x => frobeniusSq_sub_le _ _ _)
      _ = _ := by rw [integral_add (hABi.const_mul 2) (hBCi.const_mul 2),
        integral_const_mul, integral_const_mul]
  apply squeeze_zero hnonneg hle
  simpa using (hAB.const_mul 2).add (hBC.const_mul 2)

variable [DecidableEq ι]

/-- Spectral contraction passes to L2 convergence, with integrability justified by domination. -/
theorem cfc_frobeniusSq_L2_tendsto {α : Type*} {l : Filter α}
    (μ : Measure Ω) (A B : α → Ω → Matrix ι ι ℝ)
    (hA : ∀ n i j, MemLp (fun x => A n x i j) 2 μ)
    (hB : ∀ n i j, MemLp (fun x => B n x i j) 2 μ)
    (hAh : ∀ n x, (A n x).IsHermitian) (hBh : ∀ n x, (B n x).IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|)
    (hm : ∀ n, AEStronglyMeasurable (fun x => frobeniusSq (cfc q (A n x) - cfc q (B n x))) μ)
    (hlim : Tendsto (fun n => ∫ x, frobeniusSq (A n x - B n x) ∂μ) l (𝓝 0)) :
    (∀ n, Integrable (fun x => frobeniusSq (cfc q (A n x) - cfc q (B n x))) μ) ∧
      Tendsto (fun n => ∫ x, frobeniusSq (cfc q (A n x) - cfc q (B n x)) ∂μ) l (𝓝 0) := by
  have hnonneg (n : α) (x : Ω) :
      0 ≤ frobeniusSq (cfc q (A n x) - cfc q (B n x)) := by
    rw [frobeniusSq_eq_sum]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hbound (n : α) (x : Ω) :
      frobeniusSq (cfc q (A n x) - cfc q (B n x)) ≤ frobeniusSq (A n x - B n x) :=
    cfc_frobeniusSq_le (hAh n x) (hBh n x) q hq
  have hi (n : α) : Integrable (fun x => frobeniusSq (cfc q (A n x) - cfc q (B n x))) μ := by
    apply (integrable_frobeniusSq_sub μ (A n) (B n) (hA n) (hB n)).mono' (hm n)
    filter_upwards [] with x
    simpa only [Real.norm_of_nonneg (hnonneg n x)] using hbound n x
  refine ⟨hi, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (hnonneg n)) _ hlim
  intro n
  exact integral_mono (hi n) (integrable_frobeniusSq_sub μ (A n) (B n) (hA n) (hB n)) (hbound n)

end Submission.Obl.Entropy__equality_cases
