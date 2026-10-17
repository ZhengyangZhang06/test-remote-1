/-
Adapted from: here:o021
Original proofs by session x0046.
-/

import Submission.Lib.SpectralAbsorption.Spectral

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

namespace Submission.Lib.SpectralAbsorption

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_basisDiag (U : unitary (Matrix n n ℝ)) {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) (i : n) :
    Integrable (fun x => basisDiag U (F x) i) μ := by
  simp only [basisDiag, Matrix.mul_apply]
  apply integrable_finsetSum
  intro j _
  apply Integrable.mul_const
  apply integrable_finsetSum
  intro k _
  exact (hF k j).const_mul _

lemma integral_basisDiag (U : unitary (Matrix n n ℝ)) {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) (i : n) :
    (∫ x, basisDiag U (F x) i ∂μ) = basisDiag U (fun j k => ∫ x, F x j k ∂μ) i := by
  simp only [basisDiag, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_finsetSum _ (fun k _ => (hF k j).const_mul _)).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, integral_finsetSum _ (fun k _ => (hF k j).const_mul _)]
  simp only [integral_const_mul]

lemma integral_trace_cfc_mul {B : Matrix n n ℝ} (hB : B.IsHermitian)
    (f : ℝ → ℝ) {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    (∫ x, (cfc f B * F x).trace ∂μ) =
      ∑ i, f (hB.eigenvalues i) * ∫ x, basisDiag hB.eigenvectorUnitary (F x) i ∂μ := by
  simp_rw [trace_cfc_mul hB]
  rw [integral_finsetSum _ (fun i _ => (integrable_basisDiag _ hF i).const_mul _)]
  simp only [integral_const_mul]

lemma integrable_trace {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    Integrable (fun x => (F x).trace) μ := by
  exact integrable_finsetSum _ fun i _ => hF i i

lemma integral_sum_basisDiag (U : unitary (Matrix n n ℝ)) {F : Ω → Matrix n n ℝ}
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    (∑ i, ∫ x, basisDiag U (F x) i ∂μ) = ∫ x, (F x).trace ∂μ := by
  rw [← integral_finsetSum _ (fun i _ => integrable_basisDiag U hF i)]
  simp only [sum_basisDiag]

lemma trace_square {Y : Matrix n n ℝ} (hY : Y.IsHermitian) :
    (Y * Y).trace = ∑ i, ∑ j, (Y i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : Y j i = Y i j := by simpa using congrArg (fun M => M i j) hY.eq
  change Y i j * Y j i = Y i j ^ 2
  rw [h, pow_two]

lemma square_posSemidef {Y : Matrix n n ℝ} (hY : Y.IsHermitian) :
    (Y * Y).PosSemidef := by
  simpa only [hY.eq] using Matrix.posSemidef_conjTranspose_mul_self Y

/-- A scalar quadratic minorant can be averaged in each fixed unit direction.
Only entrywise integrability is needed, so the statement is independent of the
choice of norm on the matrix space. -/
lemma integral_basisDiag_minorant [IsProbabilityMeasure μ]
    (U : unitary (Matrix n n ℝ)) {A : Ω → Matrix n n ℝ}
    (hA : ∀ x, (A x).IsHermitian) {p : ℝ → ℝ} {u v d : ℝ}
    (hp : ∀ a, u + v * a - d * a ^ 2 ≤ p a)
    (hAint : ∀ i j, Integrable (fun x => A x i j) μ)
    (hA2int : ∀ i j, Integrable (fun x => (A x * A x) i j) μ)
    (hpint : ∀ i j, Integrable (fun x => cfc p (A x) i j) μ)
    (hmean : ∀ i j, (∫ x, A x i j ∂μ) = 0) (i : n) :
    u - d * (∫ x, basisDiag U (A x * A x) i ∂μ) ≤
      ∫ x, basisDiag U (cfc p (A x)) i ∂μ := by
  have hpoint x : u + v * basisDiag U (A x) i - d * basisDiag U (A x * A x) i ≤
      basisDiag U (cfc p (A x)) i := by
    simpa only [basisDiag_sub, basisDiag_add, basisDiag_smul, basisDiag_one, mul_one]
      using basisDiag_mono U (quadratic_minorant_cfc (hA x) hp) i
  have hv : Integrable (fun x => v * basisDiag U (A x) i) μ :=
    (integrable_basisDiag U hAint i).const_mul v
  have hd : Integrable (fun x => d * basisDiag U (A x * A x) i) μ :=
    (integrable_basisDiag U hA2int i).const_mul d
  have huv : Integrable (fun x => u + v * basisDiag U (A x) i) μ :=
    (integrable_const u).add hv
  have h := integral_mono (huv.sub hd) (integrable_basisDiag U hpint i) hpoint
  have heq : (∫ x, u + v * basisDiag U (A x) i - d * basisDiag U (A x * A x) i ∂μ) =
      u + v * (∫ x, basisDiag U (A x) i ∂μ) - d * (∫ x, basisDiag U (A x * A x) i ∂μ) := by
    rw [integral_sub huv hd, integral_add (integrable_const u) hv]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  change (∫ x, u + v * basisDiag U (A x) i - d * basisDiag U (A x * A x) i ∂μ) ≤ _ at h
  rw [heq] at h
  have hz : (∫ x, basisDiag U (A x) i ∂μ) = 0 := by
    rw [integral_basisDiag U hAint]
    simp only [hmean]
    exact basisDiag_zero U i
  simpa only [hz, mul_zero, add_zero] using h

lemma integral_trace_square_cfc_le {A Y : Ω → Matrix n n ℝ}
    (hA : ∀ x, (A x).IsHermitian) (hY : ∀ x, (Y x).IsHermitian)
    (hY2 : ∀ i j, Integrable (fun x => (Y x * Y x) i j) μ)
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ} (hf : ∀ a, f a ≤ c) :
    (∫ x, (Y x * Y x * cfc f (A x)).trace ∂μ) ≤
      c * (∫ x, (Y x * Y x).trace ∂μ) := by
  by_cases hint : Integrable (fun x => (Y x * Y x * cfc f (A x)).trace) μ
  · rw [← integral_const_mul]
    exact integral_mono hint ((integrable_trace hY2).const_mul c)
      (fun x => trace_mul_cfc_le (hA x) (hY x) hf)
  · rw [integral_undef hint]
    exact mul_nonneg hc (integral_nonneg fun x => (square_posSemidef (hY x)).trace_nonneg)

end Submission.Lib.SpectralAbsorption
