/-
Adapted from: here:root
Original workspace contribution: x0119 original optimal-coupling and cyclic-rearrangement work.
The aggregate combines these three root sessions' original proofs.
-/

import Submission.Lib.Brenier.OptimalCoupling

/-!
# Finite rearrangements of couplings

Permuting the second coordinates of finitely many samples, on a measurable event,
preserves the averaged marginals. This supplies competitors for cyclic optimality.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical

namespace Submission.Lib.Brenier.OptimalCoupling

variable {ι Ω X Y Z : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private lemma card_ne_zero : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero (α := ι)

/-- The uniformly weighted average of a nonempty finite family of laws. -/
noncomputable def averageLaw (π : ι → ProbabilityMeasure Z) : ProbabilityMeasure Z :=
  ⟨(Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, (π i : Measure Z), ⟨by
    simp only [Measure.smul_apply, Measure.finsetSum_apply, measure_univ, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel card_ne_zero (by simp)⟩⟩

@[simp] lemma averageLaw_toMeasure (π : ι → ProbabilityMeasure Z) :
    (averageLaw π : Measure Z) = (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, (π i : Measure Z) := rfl

@[simp] lemma averageLaw_const (π : ProbabilityMeasure Z) :
    averageLaw (fun _ : ι => π) = π := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simp only [averageLaw_toMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel card_ne_zero (by simp), one_mul]

lemma averageLaw_map (π : ι → ProbabilityMeasure Z) {f : Z → Y} (hf : Measurable f) :
    (averageLaw π).map hf.aemeasurable = averageLaw (fun i => (π i).map hf.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, averageLaw_toMeasure, Measure.map_smul]
  rw [Measure.map_finset_sum hf.aemeasurable]

lemma integral_averageLaw {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (π : ι → ProbabilityMeasure Z) {f : Z → G} (hf : ∀ i, Integrable f (π i : Measure Z)) :
    (∫ z, f z ∂(averageLaw π : Measure Z)) =
      (Fintype.card ι : ℝ)⁻¹ • ∑ i, ∫ z, f z ∂(π i : Measure Z) := by
  rw [averageLaw_toMeasure, integral_smul_measure, integral_finsetSum_measure (fun i _ => hf i)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]

omit [Nonempty ι] in
/-- A simultaneous event-dependent permutation does not change the sum of laws. -/
lemma sum_map_piecewise_perm (P : Measure Ω) (f : ι → Ω → Y)
    (hf : ∀ i, Measurable (f i)) {s : Set Ω} (hs : MeasurableSet s) (σ : Equiv.Perm ι) :
    (∑ i, Measure.map (s.piecewise (f (σ i)) (f i)) P) = ∑ i, Measure.map (f i) P := by
  classical
  have hi (i : ι) : Measure.map (s.piecewise (f (σ i)) (f i)) P =
      Measure.map (f (σ i)) (P.restrict s) + Measure.map (f i) (P.restrict sᶜ) := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hs]
    rw [Measure.map_add _ _ ((hf (σ i)).piecewise hs (hf i))]
    congr 1
    · apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with x hx
      exact piecewise_eq_of_mem s (f (σ i)) (f i) hx
    · apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs.compl] with x hx
      exact piecewise_eq_of_notMem s (f (σ i)) (f i) hx
  simp_rw [hi]
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp σ (fun i => Measure.map (f i) (P.restrict s)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Measure.map_add _ _ (hf i), Measure.restrict_add_restrict_compl hs]

/-- Reassign only second coordinates on an event, using the same permutation for
every member of the family. -/
noncomputable def rearrange (f : ι → Ω → X × Y) (s : Set Ω) (σ : Equiv.Perm ι)
    (i : ι) (ω : Ω) : X × Y :=
  ((f i ω).1, s.piecewise (fun ω => (f (σ i) ω).2) (fun ω => (f i ω).2) ω)

lemma measurable_rearrange {f : ι → Ω → X × Y} (hf : ∀ i, Measurable (f i))
    {s : Set Ω} (hs : MeasurableSet s) (σ : Equiv.Perm ι) (i : ι) :
    Measurable (rearrange f s σ i) :=
  (hf i).fst.prodMk (((hf (σ i)).snd).piecewise hs (hf i).snd)

/-- Rearranged samples with the same coupling law give another coupling. -/
lemma average_rearrange_mem_couplings (P : ProbabilityMeasure Ω)
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {π : ProbabilityMeasure (X × Y)}
    (hπ : π ∈ couplings μ ν) {f : ι → Ω → X × Y} (hf : ∀ i, Measurable (f i))
    (hlaw : ∀ i, Measure.map (f i) (P : Measure Ω) = (π : Measure (X × Y)))
    {s : Set Ω} (hs : MeasurableSet s) (σ : Equiv.Perm ι) :
    averageLaw (fun i => P.map (measurable_rearrange hf hs σ i).aemeasurable) ∈ couplings μ ν := by
  constructor
  · rw [averageLaw_map _ measurable_fst]
    have he (i : ι) :
        (P.map (measurable_rearrange hf hs σ i).aemeasurable).map measurable_fst.aemeasurable = μ := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map measurable_fst (measurable_rearrange hf hs σ i)]
      change Measure.map (Prod.fst ∘ f i) (P : Measure Ω) = (μ : Measure X)
      rw [← Measure.map_map measurable_fst (hf i), hlaw i]
      exact (measurePreserving_fst hπ).map_eq
    simp_rw [he]
    exact averageLaw_const μ
  · apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, averageLaw_toMeasure, Measure.map_smul]
    rw [Measure.map_finset_sum measurable_snd.aemeasurable]
    simp_rw [Measure.map_map measurable_snd (measurable_rearrange hf hs σ _)]
    change (Fintype.card ι : ℝ≥0∞)⁻¹ •
      ∑ i, Measure.map (s.piecewise (fun ω => (f (σ i) ω).2) (fun ω => (f i ω).2))
        (P : Measure Ω) = (ν : Measure Y)
    rw [sum_map_piecewise_perm (P : Measure Ω) (fun i ω => (f i ω).2)
      (fun i => (hf i).snd) hs σ]
    have he (i : ι) : Measure.map (fun ω => (f i ω).2) (P : Measure Ω) = (ν : Measure Y) := by
      change Measure.map (Prod.snd ∘ f i) (P : Measure Ω) = (ν : Measure Y)
      rw [← Measure.map_map measurable_snd (hf i), hlaw i]
      exact (measurePreserving_snd hπ).map_eq
    simp_rw [he]
    exact congrArg ProbabilityMeasure.toMeasure (averageLaw_const (ι := ι) ν)

end Submission.Lib.Brenier.OptimalCoupling
