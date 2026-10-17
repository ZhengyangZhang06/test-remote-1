import Submission.Lib.PairEstimate.Integration

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

variable {Ω n r : Type*} [MeasurableSpace Ω] [Fintype n]
variable {μ : Measure Ω} {p q t : ℝ≥0∞}

/-- Entrywise integrability, with a variable exponent for products. -/
def MatrixLp (μ : Measure Ω) (p : ℝ≥0∞) (F : Ω → Matrix n n ℝ) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) p μ

namespace MatrixLp

variable {F G : Ω → Matrix n n ℝ}

lemma add (hF : MatrixLp μ p F) (hG : MatrixLp μ p G) :
    MatrixLp μ p (fun x => F x + G x) := fun i j => (hF i j).add (hG i j)

lemma sub (hF : MatrixLp μ p F) (hG : MatrixLp μ p G) :
    MatrixLp μ p (fun x => F x - G x) := fun i j => (hF i j).sub (hG i j)

lemma neg (hF : MatrixLp μ p F) : MatrixLp μ p (fun x => -F x) :=
  fun i j => (hF i j).neg

lemma smul (hF : MatrixLp μ p F) (c : ℝ) : MatrixLp μ p (fun x => c • F x) :=
  fun i j => (hF i j).const_smul c

lemma nsmul (hF : MatrixLp μ p F) (c : ℕ) : MatrixLp μ p (fun x => c • F x) := by
  intro i j
  simpa only [Matrix.smul_apply, nsmul_eq_mul] using (hF i j).const_mul (c : ℝ)

lemma transpose (hF : MatrixLp μ p F) : MatrixLp μ p (fun x => (F x).transpose) :=
  fun i j => hF j i

lemma sum [Fintype r] {F : r → Ω → Matrix n n ℝ} (hF : ∀ a, MatrixLp μ p (F a)) :
    MatrixLp μ p (fun x => ∑ a, F a x) := by
  intro i j
  simpa only [Matrix.sum_apply] using
    memLp_finsetSum Finset.univ (fun a _ => hF a i j)

lemma const_mul (hF : MatrixLp μ p F) (C : Matrix n n ℝ) :
    MatrixLp μ p (fun x => C * F x) := by
  intro i j
  exact memLp_finsetSum _ (fun k _ => (hF k j).const_mul (C i k))

lemma mul_const (hF : MatrixLp μ p F) (C : Matrix n n ℝ) :
    MatrixLp μ p (fun x => F x * C) := by
  intro i j
  exact memLp_finsetSum _ (fun k _ => (hF i k).mul_const (C k j))

lemma mul (hF : MatrixLp μ p F) (hG : MatrixLp μ q G) [ENNReal.HolderTriple p q t] :
    MatrixLp μ t (fun x => F x * G x) := by
  intro i j
  exact memLp_finsetSum _ (fun k _ => (hG k j).mul' (hF i k))

lemma trace (hF : MatrixLp μ p F) : MemLp (fun x => Matrix.trace (F x)) p μ :=
  memLp_finsetSum _ (fun i _ => hF i i)

lemma integrable (hF : MatrixLp μ 1 F) (i j : n) :
    Integrable (fun x => F x i j) μ := memLp_one_iff_integrable.mp (hF i j)

lemma integrable_trace (hF : MatrixLp μ 1 F) :
    Integrable (fun x => Matrix.trace (F x)) μ := memLp_one_iff_integrable.mp hF.trace

lemma of_le [IsFiniteMeasure μ] (hF : MatrixLp μ p F) (h : q ≤ p) : MatrixLp μ q F :=
  fun i j => (hF i j).mono_exponent h

lemma integrable_trace_mul (hF : MatrixLp μ 2 F) (hG : MatrixLp μ 2 G) :
    Integrable (fun x => Matrix.trace (F x * G x)) μ :=
  (hF.mul hG).integrable_trace

lemma integrable_squares (hF : MatrixLp μ 2 F) :
    Integrable (fun x => ∑ i, ∑ j, (F x i j)^2) μ :=
  Submission.Lib.PairEstimate.integrable_squareSum hF

lemma const [IsFiniteMeasure μ] (C : Matrix n n ℝ) : MatrixLp μ p (fun _ : Ω => C) :=
  fun i j => memLp_const (C i j)

lemma of_bound {F : Ω → Matrix n n ℝ}
    (hmeas : ∀ i j, AEStronglyMeasurable (fun x => F x i j) μ)
    (hbound : ∃ C : ℝ, ∀ x i j, |F x i j| ≤ C) : MatrixLp μ ∞ F := by
  obtain ⟨C, hC⟩ := hbound
  intro i j
  exact memLp_top_of_bound (hmeas i j) C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x i j)

end MatrixLp
end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
