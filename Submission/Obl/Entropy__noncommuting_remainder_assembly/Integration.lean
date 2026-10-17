import Submission.Obl.Entropy__noncommuting_remainder_assembly.CommutatorInvariant

open scoped BigOperators
open MeasureTheory

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {Ω ι κ ν : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [Fintype ν]
  {μ : Measure Ω}

/-- Entrywise square integrability for matrix fields. -/
def EntryL2 (μ : Measure Ω) (F : Ω → Matrix ι κ ℝ) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) 2 μ

omit [Fintype κ] [Fintype ν] in
lemma EntryL2.const_mul {F : Ω → Matrix ι κ ℝ} (hF : EntryL2 μ F)
    (L : Matrix ν ι ℝ) : EntryL2 μ (fun x => L * F x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun k _ => (hF k j).const_mul (L i k)

omit [Fintype ι] [Fintype ν] in
lemma EntryL2.mul_const {F : Ω → Matrix ι κ ℝ} (hF : EntryL2 μ F)
    (R : Matrix κ ν ℝ) : EntryL2 μ (fun x => F x * R) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun k _ => (hF i k).mul_const (R k j)

omit [Fintype ι] [Fintype κ] in
lemma EntryL2.transpose {F : Ω → Matrix ι κ ℝ} (hF : EntryL2 μ F) :
    EntryL2 μ (fun x => (F x).transpose) := fun i j => hF j i

omit [Fintype ι] [Fintype κ] in
lemma EntryL2.sub {F G : Ω → Matrix ι κ ℝ} (hF : EntryL2 μ F) (hG : EntryL2 μ G) :
    EntryL2 μ (fun x => F x - G x) := fun i j => (hF i j).sub (hG i j)

omit [Fintype ι] [Fintype κ] in
lemma EntryL2.sum {F : ν → Ω → Matrix ι κ ℝ} (hF : ∀ r, EntryL2 μ (F r)) :
    EntryL2 μ (fun x => ∑ r, F r x) := by
  intro i j
  simp only [Matrix.sum_apply]
  exact memLp_finsetSum _ fun r _ => hF r i j

lemma EntryL2.integrable_squareSum {F : Ω → Matrix ι κ ℝ} (hF : EntryL2 μ F) :
    Integrable (fun x => squareSum (F x)) μ :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF i j).integrable_sq

lemma EntryL2.integrable_trace_mul {F : Ω → Matrix ι κ ℝ} {G : Ω → Matrix κ ι ℝ}
    (hF : EntryL2 μ F) (hG : EntryL2 μ G) :
    Integrable (fun x => Matrix.trace (F x * G x)) μ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hF i j).integrable_mul (hG j i)

/-- Lemma 3.4 integrated against any measure, with the L2 hypotheses making all terms legitimate. -/
lemma integrated_commutator_bound [DecidableEq ι]
    (X : ν → Matrix ι ι ℝ) (b : Ω → Matrix ι ι ℝ) (W : ν → Ω → Matrix ι ι ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hb : ∀ x, (b x).IsHermitian)
    (hb2 : EntryL2 μ b) (hW : ∀ r, EntryL2 μ (W r)) :
    let B := ∑ r, X r * X r;
    let S := ((37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B)⁻¹;
    let T := S - 1;
    -(∫ x, Matrix.trace (T * b x * B * b x - T * B * b x * b x) ∂μ) -
      2 * (∫ x, Matrix.trace ((T * b x - b x * T) * (∑ r, X r * W r x)) ∂μ) -
      (∫ x, Matrix.trace (T * (∑ r, (W r x).transpose * W r x)) ∂μ) ≤
        (42 / 37 : ℝ) * (∑ r, ∫ x, squareSum (W r x) ∂μ) := by
  intro B S T
  let P := fun x => Matrix.trace (T * b x * B * b x - T * B * b x * b x)
  let C := fun x => Matrix.trace ((T * b x - b x * T) * (∑ r, X r * W r x))
  let E := fun x => Matrix.trace (T * (∑ r, (W r x).transpose * W r x))
  have hP : Integrable P μ := by
    simp only [P, Matrix.trace_sub]
    exact (((hb2.const_mul T).mul_const B).integrable_trace_mul hb2).sub
      ((hb2.const_mul (T * B)).integrable_trace_mul hb2)
  have hC : Integrable C μ :=
    ((hb2.const_mul T).sub (hb2.mul_const T)).integrable_trace_mul
      (EntryL2.sum fun r => (hW r).const_mul (X r))
  have hE : Integrable E μ := by
    simp only [E, Matrix.mul_sum, Matrix.trace_sum, ← Matrix.mul_assoc]
    exact integrable_finsetSum _ fun r _ =>
      ((hW r).transpose.const_mul T).integrable_trace_mul (hW r)
  have hN : Integrable (fun x => ∑ r, squareSum (W r x)) μ :=
    integrable_finsetSum _ fun r _ => (hW r).integrable_squareSum
  have hpoint (x : Ω) : -P x - 2 * C x - E x ≤
      (42 / 37 : ℝ) * (∑ r, squareSum (W r x)) :=
    commutator_bound_constants X (fun r => W r x) (b x) hX (hb x)
  have hleft : Integrable (fun x => -P x - 2 * C x) μ := hP.neg.sub (hC.const_mul 2)
  have hint := integral_mono (f := fun x => -P x - 2 * C x - E x)
    (hleft.sub hE) (hN.const_mul (42 / 37)) hpoint
  rw [integral_sub hleft hE,
    integral_sub (f := fun x => -P x) (g := fun x => 2 * C x) hP.neg (hC.const_mul 2),
    integral_neg, integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun r _ => (hW r).integrable_squareSum)] at hint
  exact hint

end Submission.Obl.Entropy__noncommuting_remainder_assembly
