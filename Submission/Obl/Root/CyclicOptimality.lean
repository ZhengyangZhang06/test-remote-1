import Submission.Obl.Root.CouplingRearrangement

/-!
# Cyclic optimality of transport couplings

A finite rearrangement on precisely the event where it reduces cost cannot
improve an optimal coupling. Thus every permutation increases total cost almost
everywhere under any joint sample law whose individual laws are that coupling.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical

namespace Submission.Obl.Root.OptimalCoupling

variable {ι Ω X Y : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

/-- Optimality forbids cost-lowering finite permutations almost everywhere. -/
theorem ae_sum_cost_le_sum_permuted
    (P : ProbabilityMeasure Ω) {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν)
    {c : X × Y → ℝ} (hc : Measurable c) (hci : Integrable c (π : Measure (X × Y)))
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, c z ∂(π : Measure (X × Y))) ≤ ∫ z, c z ∂(ρ : Measure (X × Y)))
    {f : ι → Ω → X × Y} (hf : ∀ i, Measurable (f i))
    (hlaw : ∀ i, Measure.map (f i) (P : Measure Ω) = (π : Measure (X × Y)))
    (σ : Equiv.Perm ι)
    (hcross : ∀ i, Integrable (fun ω => c ((f i ω).1, (f (σ i) ω).2)) (P : Measure Ω)) :
    ∀ᵐ ω ∂(P : Measure Ω), ∑ i, c (f i ω) ≤ ∑ i, c ((f i ω).1, (f (σ i) ω).2) := by
  classical
  let A : Ω → ℝ := fun ω => ∑ i, c (f i ω)
  let B : Ω → ℝ := fun ω => ∑ i, c ((f i ω).1, (f (σ i) ω).2)
  let s : Set Ω := {ω | B ω < A ω}
  have hAi (i : ι) : Integrable (fun ω => c (f i ω)) (P : Measure Ω) := by
    apply (integrable_map_measure hc.aestronglyMeasurable (hf i).aemeasurable).mp
    rwa [hlaw i]
  have hAm : Measurable A := Finset.measurable_sum _ (fun i _ => hc.comp (hf i))
  have hBm : Measurable B := Finset.measurable_sum _
    (fun i _ => hc.comp ((hf i).fst.prodMk (hf (σ i)).snd))
  have hs : MeasurableSet s := measurableSet_lt hBm hAm
  let g : ι → Ω → X × Y := rearrange f s σ
  have hg (i : ι) : Measurable (g i) := measurable_rearrange hf hs σ i
  have hcost (i : ι) : (fun ω => c (g i ω)) =
      s.piecewise (fun ω => c ((f i ω).1, (f (σ i) ω).2)) (fun ω => c (f i ω)) := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [g, rearrange, hω]
  have hgi (i : ι) : Integrable (fun ω => c (g i ω)) (P : Measure Ω) := by
    rw [hcost]
    exact Integrable.piecewise hs (hcross i).integrableOn (hAi i).integrableOn
  have hgm (i : ι) : Integrable c (P.map (hg i).aemeasurable : Measure (X × Y)) := by
    exact (integrable_map_measure hc.aestronglyMeasurable (hg i).aemeasurable).mpr (hgi i)
  let C : Ω → ℝ := fun ω => ∑ i, c (g i ω)
  have hC : C = s.piecewise B A := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [C, g, rearrange, hω, A, B]
  have hCA (ω : Ω) : C ω ≤ A ω := by
    rw [hC]
    by_cases hω : ω ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hω]
      exact le_of_lt hω
    · rw [piecewise_eq_of_notMem _ _ _ hω]
  have hAI : Integrable A (P : Measure Ω) := integrable_finsetSum _ (fun i _ => hAi i)
  have hCI : Integrable C (P : Measure Ω) := integrable_finsetSum _ (fun i _ => hgi i)
  have hAint : (∫ ω, A ω ∂(P : Measure Ω)) =
      (Fintype.card ι : ℝ) * ∫ z, c z ∂(π : Measure (X × Y)) := by
    rw [show A = (fun ω => ∑ i, c (f i ω)) from rfl,
      integral_finsetSum _ (fun i _ => hAi i)]
    have he (i : ι) : (∫ ω, c (f i ω) ∂(P : Measure Ω)) =
        ∫ z, c z ∂(π : Measure (X × Y)) := by
      rw [← integral_map (hf i).aemeasurable hc.aestronglyMeasurable, hlaw i]
    simp_rw [he]
    simp
  have hCint : (∫ ω, C ω ∂(P : Measure Ω)) =
      ∑ i, ∫ z, c z ∂(P.map (hg i).aemeasurable : Measure (X × Y)) := by
    rw [show C = (fun ω => ∑ i, c (g i ω)) from rfl,
      integral_finsetSum _ (fun i _ => hgi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_map (hg i).aemeasurable hc.aestronglyMeasurable).symm
  have hmin' := hmin (averageLaw (fun i => P.map (hg i).aemeasurable))
    (average_rearrange_mem_couplings P hπ hf hlaw hs σ)
  rw [integral_averageLaw _ hgm, ← hCint, smul_eq_mul] at hmin'
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAC : (∫ ω, A ω ∂(P : Measure Ω)) ≤ ∫ ω, C ω ∂(P : Measure Ω) := by
    rw [hAint]
    calc
      _ ≤ (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ)⁻¹ * ∫ ω, C ω ∂(P : Measure Ω)) :=
        mul_le_mul_of_nonneg_left hmin' hn.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  have hae : C =ᵐ[(P : Measure Ω)] A :=
    (integral_eq_iff_of_ae_le hCI hAI (Filter.Eventually.of_forall hCA)).mp
      (le_antisymm (integral_mono hCI hAI hCA) hAC)
  filter_upwards [hae] with ω hω
  change A ω ≤ B ω
  by_contra h
  have hmem : ω ∈ s := lt_of_not_ge h
  have hval : C ω = B ω := by rw [hC, piecewise_eq_of_mem _ _ _ hmem]
  exact (ne_of_lt hmem) (hval.symm.trans hω)

end Submission.Obl.Root.OptimalCoupling
