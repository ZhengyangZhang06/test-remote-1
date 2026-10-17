import Submission.Lib.MatrixEntropy.LogDet
import Submission.Lib.EntropyTools.DensityMoments

namespace Submission.Obl.Entropy__transport_covariance_completion

set_option linter.unusedSectionVars false

open MeasureTheory Matrix
open scoped BigOperators

variable {Ω n r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Fintype r]
  {μ : Measure Ω}

/-- Integrability of the trace follows entrywise. -/
theorem integrable_trace {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    Integrable (fun x => (F x).trace) μ :=
  integrable_finsetSum _ fun i _ => hF i i

/-- Multiplication by a constant weight preserves entrywise integrability. -/
theorem integrable_trace_const_mul (P : Matrix n n ℝ) {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    Integrable (fun x => (P * F x).trace) μ := by
  apply integrable_trace
  intro i j
  exact integrable_finsetSum _ fun k _ => (hF k j).const_mul (P i k)

/-- The trace of a symmetric square is the sum of the entrywise squares. -/
theorem trace_square_eq_sum_sq {F : Matrix n n ℝ} (hF : F.IsHermitian) :
    (F * F).trace = ∑ i, ∑ j, (F i j)^2 := by
  simp only [trace, diag_apply, mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : F j i = F i j := by simpa using congrFun (congrFun hF.eq i) j
  rw [hij, pow_two]

/-- Products of entrywise L2 fields have integrable entries. -/
theorem integrable_matrix_mul {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ) :
    ∀ i j, Integrable (fun x => (F x * G x) i j) μ := by
  intro i j
  exact integrable_finsetSum _ fun k _ => (hF i k).integrable_mul (hG k j)

/-- The trace of the completed covariance has the required energy expansion. -/
theorem integral_trace_completion
    {T k : Ω → Matrix n n ℝ} {K : r → Ω → Matrix n n ℝ}
    (hT : ∀ i j, Integrable (fun x => T x i j) μ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 μ)
    (hK : ∀ s i j, MemLp (fun x => K s x i j) 2 μ)
    (hks : ∀ x, (k x).IsHermitian) (hKs : ∀ s x, (K s x).IsHermitian) :
    (∫ x, (2 • T x - k x * k x - ∑ s, K s x * K s x).trace ∂μ) =
      2 * (∫ x, (T x).trace ∂μ) -
        (∫ x, ∑ i, ∑ j, (k x i j)^2 ∂μ) -
        ∑ s, (∫ x, ∑ i, ∑ j, (K s x i j)^2 ∂μ) := by
  have hik := integrable_trace (integrable_matrix_mul hk hk)
  have hiK s := integrable_trace (integrable_matrix_mul (hK s) (hK s))
  simp only [two_smul, trace_sub, trace_add, trace_sum]
  simp only [← two_mul]
  have hs := integral_sub ((integrable_trace hT).const_mul 2 |>.sub hik)
      (integrable_finsetSum Finset.univ fun s _ => hiK s)
  simp only [Pi.sub_apply] at hs
  rw [hs, integral_sub ((integrable_trace hT).const_mul 2) hik,
    integral_const_mul, integral_finsetSum Finset.univ (fun s _ => hiK s)]
  simp_rw [trace_square_eq_sum_sq (hks _), trace_square_eq_sum_sq (hKs _ _)]

/-- Once the transport entropy identity and covariance completion are supplied,
only the supporting plane and linear arithmetic remain. -/
theorem completion_from_entropy_and_covariance
    {C P : Matrix n n ℝ} (hC : C.PosDef) (hP : P.PosDef)
    {E : Ω → Matrix n n ℝ} (hE : ∀ i j, Integrable (fun x => E x i j) μ)
    {H a b c t w : ℝ}
    (hentropy : 2 * (Fintype.card n : ℝ) + 2 * H = a - 2 * t + Fintype.card n)
    (htrace : (∫ x, (E x).trace ∂μ) = 2 * t - b - c)
    (hcov : (P * C).trace ≤ (∫ x, (P * E x).trace ∂μ) + w) :
    2 * (Fintype.card n : ℝ) + Real.log C.det + 2 * H ≤
      a - b - c + (∫ x, ((P - 1) * E x).trace ∂μ) + w - Real.log P.det := by
  have hsplit : (∫ x, ((P - 1) * E x).trace ∂μ) =
      (∫ x, (P * E x).trace ∂μ) - (∫ x, (E x).trace ∂μ) := by
    simp only [sub_mul, one_mul, trace_sub]
    exact integral_sub (integrable_trace_const_mul P hE) (integrable_trace hE)
  have hplane := Submission.Lib.MatrixEntropy.log_det_supporting_plane hC hP
  linarith

end Submission.Obl.Entropy__transport_covariance_completion
