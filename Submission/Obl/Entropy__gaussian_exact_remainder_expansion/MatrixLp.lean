import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- Entrywise matrix integrability, with an exponent that also permits bounded fields. -/
def MatrixLp (μ : Measure α) (p : ℝ≥0∞) (F : α → Matrix ι ι ℝ) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) p μ

namespace MatrixLp

variable {μ : Measure α} {p q r : ℝ≥0∞} {F G : α → Matrix ι ι ℝ}

lemma add (hF : MatrixLp μ p F) (hG : MatrixLp μ p G) :
    MatrixLp μ p (fun x => F x+G x) := fun i j => (hF i j).add (hG i j)

lemma sub (hF : MatrixLp μ p F) (hG : MatrixLp μ p G) :
    MatrixLp μ p (fun x => F x-G x) := fun i j => (hF i j).sub (hG i j)

lemma smul (hF : MatrixLp μ p F) (a : ℝ) : MatrixLp μ p (fun x => a • F x) :=
  fun i j => (hF i j).const_mul a

lemma transpose (hF : MatrixLp μ p F) : MatrixLp μ p (fun x => (F x).transpose) :=
  fun i j => hF j i

lemma const_mul (hF : MatrixLp μ p F) (C : Matrix ι ι ℝ) :
    MatrixLp μ p (fun x => C*F x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun a _ => (hF a j).const_mul _)

lemma mul_const (hF : MatrixLp μ p F) (C : Matrix ι ι ℝ) :
    MatrixLp μ p (fun x => F x*C) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun a _ => (hF i a).mul_const _)

lemma mul (hF : MatrixLp μ p F) (hG : MatrixLp μ q G) [ENNReal.HolderTriple p q r] :
    MatrixLp μ r (fun x => F x*G x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun a _ => (hG a j).mul (hF i a))

lemma sum {ρ : Type*} [Fintype ρ] {F : ρ → α → Matrix ι ι ℝ}
    (hF : ∀ r, MatrixLp μ p (F r)) : MatrixLp μ p (fun x => ∑ r, F r x) := by
  intro i j
  simp only [Matrix.sum_apply]
  exact memLp_finsetSum _ (fun r _ => hF r i j)

lemma const [IsFiniteMeasure μ] (C : Matrix ι ι ℝ) : MatrixLp μ p (fun _ => C) :=
  fun _ _ => memLp_const _

lemma mono [IsFiniteMeasure μ] (hF : MatrixLp μ p F) (hq : q ≤ p) : MatrixLp μ q F :=
  fun i j => (hF i j).mono_exponent hq

lemma of_bound [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure μ]
    (hc : ∀ i j, Continuous (fun x => F x i j))
    (hb : ∃ R : ℝ, ∀ x i j, |F x i j| ≤ R) : MatrixLp μ p F := by
  obtain ⟨R,hR⟩ := hb
  intro i j
  exact MemLp.of_bound (hc i j).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hR x i j)

lemma trace (hF : MatrixLp μ p F) : MemLp (fun x => (F x).trace) p μ := by
  simp only [Matrix.trace, Matrix.diag]
  exact memLp_finsetSum _ (fun i _ => hF i i)

lemma integrable_trace (hF : MatrixLp μ 1 F) : Integrable (fun x => (F x).trace) μ :=
  memLp_one_iff_integrable.mp hF.trace

lemma integrable [IsFiniteMeasure μ] (hF : MatrixLp μ 2 F) (i j : ι) :
    Integrable (fun x => F x i j) μ := (hF i j).integrable (by norm_num)

lemma integrable_weighted_square (hF : MatrixLp μ 2 F) (S : Matrix ι ι ℝ) :
    Integrable (fun x => ((F x).transpose*S*F x).trace) μ :=
  ((hF.transpose.mul_const S).mul hF).integrable_trace

end MatrixLp

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
