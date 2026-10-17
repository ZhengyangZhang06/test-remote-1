import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
  {μ : Measure X}

/-- Entrywise integrability of a finite matrix field. -/
def EntryLp (p : ℝ≥0∞) (F : X → Matrix ι ι ℝ) (μ : Measure X) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) p μ

lemma EntryLp.mul {p q r : ℝ≥0∞} [p.HolderTriple q r]
    {F G : X → Matrix ι ι ℝ} (hF : EntryLp p F μ) (hG : EntryLp q G μ) :
    EntryLp r (fun x => F x * G x) μ := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum Finset.univ fun k _ => (hG k j).mul' (hF i k)

lemma EntryLp.add {p : ℝ≥0∞} {F G : X → Matrix ι ι ℝ}
    (hF : EntryLp p F μ) (hG : EntryLp p G μ) : EntryLp p (fun x => F x + G x) μ :=
  fun i j => (hF i j).add (hG i j)

lemma EntryLp.trace {p : ℝ≥0∞} {F : X → Matrix ι ι ℝ} (hF : EntryLp p F μ) :
    MemLp (fun x => Matrix.trace (F x)) p μ := by
  exact memLp_finsetSum Finset.univ fun i _ => hF i i

lemma EntryLp.integrable {F : X → Matrix ι ι ℝ} (hF : EntryLp 1 F μ) (i j : ι) :
    Integrable (fun x => F x i j) μ := memLp_one_iff_integrable.mp (hF i j)

/-- The fixed-coordinate multiplier is integrable as soon as coefficients are bounded
and the two derivative fields have square-integrable entries. -/
theorem integrable_multiplier {Jinv Q : X → Matrix ι ι ℝ}
    {H K : ι → X → Matrix ι ι ℝ}
    (hJinv : EntryLp ∞ Jinv μ) (hQ : EntryLp ∞ Q μ)
    (hH : ∀ r, EntryLp 2 (H r) μ) (hK : ∀ r, EntryLp 2 (K r) μ) :
    Integrable (fun x =>
      (∑ i, ∑ j, (Q x * Q x) i j * Matrix.trace (Jinv x * H i x * Jinv x * H j x)) +
      ∑ r, ∑ s, Jinv x r s * Matrix.trace ((K s x * Q x + Q x * K s x) * H r x)) μ := by
  have hP : EntryLp ∞ (fun x => Q x * Q x) μ := hQ.mul hQ
  have hT (i j : ι) : MemLp
      (fun x => Matrix.trace (Jinv x * H i x * Jinv x * H j x)) 1 μ :=
    ((hJinv.mul (r := 2) (hH i) |>.mul (r := 2) hJinv).mul (r := 1) (hH j)).trace
  have hS (r s : ι) : MemLp
      (fun x => Matrix.trace ((K s x * Q x + Q x * K s x) * H r x)) 1 μ :=
    (((hK s).mul (r := 2) hQ).add (hQ.mul (r := 2) (hK s)) |>.mul (r := 1) (hH r)).trace
  apply Integrable.add
  · apply integrable_finsetSum Finset.univ fun i _ => ?_
    apply integrable_finsetSum Finset.univ fun j _ => ?_
    exact memLp_one_iff_integrable.mp ((hT i j).mul' (hP i j))
  · apply integrable_finsetSum Finset.univ fun r _ => ?_
    apply integrable_finsetSum Finset.univ fun s _ => ?_
    exact memLp_one_iff_integrable.mp ((hS r s).mul' (hJinv r s))

end Submission.Obl.Entropy__transport_integrated_multiplier
