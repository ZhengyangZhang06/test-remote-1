/-
Adapted from: here:root
Original workspace contribution: x0119 original optimal-coupling and cyclic-rearrangement work.
The aggregate combines these three root sessions' original proofs.
-/

import Submission.Lib.Brenier.CyclicOptimality

/-!
# Cyclic optimality on the support

The product of support points belongs to the support of a finite product law.
Consequently continuous cost inequalities valid almost everywhere hold on every
finite tuple of support points.
-/

open MeasureTheory Set
open scoped Topology BigOperators ENNReal NNReal Classical

namespace Submission.Lib.Brenier.OptimalCoupling

/-- Finite products of points in measure supports belong to the product support. -/
lemma mem_support_pi {ι : Type*} [Fintype ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] [∀ i, MeasurableSpace (Z i)]
    (P : ∀ i, Measure (Z i)) [∀ i, SigmaFinite (P i)]
    (z : ∀ i, Z i) (hz : ∀ i, z i ∈ (P i).support) :
    z ∈ (Measure.pi P).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hzU hU
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU z hzU
  apply lt_of_lt_of_le _ (measure_mono hVU)
  rw [Measure.pi_pi]
  apply pos_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    ((Measure.mem_support_iff_forall _).mp (hz i) _ ((hV i).1.mem_nhds (hV i).2)).ne')

variable {ι X Y : Type*} [Fintype ι] [Nonempty ι]
  [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

/-- Every source support point is a limit of source projections of coupling
support points. -/
lemma source_support_subset_closure_projection
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν) :
    (μ : Measure X).support ⊆ closure (Prod.fst '' (π : Measure (X × Y)).support) := by
  apply Measure.support_subset_of_isClosed isClosed_closure
  rw [← (measurePreserving_fst hπ).map_eq]
  apply (ae_map_iff measurable_fst.aemeasurable isClosed_closure.measurableSet).mpr
  filter_upwards [Measure.support_mem_ae (μ := (π : Measure (X × Y)))] with z hz
  exact subset_closure ⟨z, hz, rfl⟩

/-- Full source support makes the source projection of a coupling support dense. -/
lemma dense_source_projection
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν)
    (hμ : (μ : Measure X).support = univ) :
    Dense (Prod.fst '' (π : Measure (X × Y)).support) := by
  rw [dense_iff_closure_eq]
  exact eq_univ_of_univ_subset (hμ ▸ source_support_subset_closure_projection hπ)

/-- A continuous-cost optimal coupling satisfies every finite permutation
inequality at all tuples of support points, provided the cross costs are integrable. -/
theorem sum_cost_le_sum_permuted_on_support
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν)
    {c : X × Y → ℝ} (hc : Continuous c) (hci : Integrable c (π : Measure (X × Y)))
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, c z ∂(π : Measure (X × Y))) ≤ ∫ z, c z ∂(ρ : Measure (X × Y)))
    (σ : Equiv.Perm ι)
    (hcross : ∀ i, Integrable (fun z : ι → X × Y => c ((z i).1, (z (σ i)).2))
      (Measure.pi (fun _ : ι => (π : Measure (X × Y)))))
    (z : ι → X × Y) (hz : ∀ i, z i ∈ (π : Measure (X × Y)).support) :
    ∑ i, c (z i) ≤ ∑ i, c ((z i).1, (z (σ i)).2) := by
  let P := ProbabilityMeasure.pi (fun _ : ι => π)
  have hae := ae_sum_cost_le_sum_permuted P hπ hc.measurable hci hmin
    (f := fun i z => z i) (fun i => measurable_pi_apply i)
    (fun i => (measurePreserving_eval (fun _ : ι => (π : Measure (X × Y))) i).map_eq)
    σ hcross
  have hclosed : IsClosed {z : ι → X × Y |
      ∑ i, c (z i) ≤ ∑ i, c ((z i).1, (z (σ i)).2)} := by
    apply isClosed_le <;> fun_prop
  exact Measure.support_subset_of_isClosed hclosed hae
    (mem_support_pi (fun _ : ι => (π : Measure (X × Y))) z hz)

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- The support of a quadratic optimal coupling is cyclically monotone in the
cost form, including arbitrary finite permutations. -/
theorem sum_quadratic_le_sum_permuted_on_support {μ ν : ProbabilityMeasure E}
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    {π : ProbabilityMeasure (E × E)} (hπ : π ∈ couplings μ ν)
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, ‖z.1 - z.2‖^2 ∂(π : Measure (E × E))) ≤
        ∫ z, ‖z.1 - z.2‖^2 ∂(ρ : Measure (E × E)))
    (σ : Equiv.Perm ι) (z : ι → E × E)
    (hz : ∀ i, z i ∈ (π : Measure (E × E)).support) :
    ∑ i, ‖(z i).1 - (z i).2‖^2 ≤ ∑ i, ‖(z i).1 - (z (σ i)).2‖^2 := by
  apply sum_cost_le_sum_permuted_on_support hπ (by fun_prop)
    (integrable_quadratic_cost hμ hν hπ) hmin σ _ z hz
  intro i
  have hfst : MemLp (Prod.fst : E × E → E) 2 (π : Measure (E × E)) := by
    simpa only [Function.comp_def, id_eq] using hμ.comp_measurePreserving (measurePreserving_fst hπ)
  have hsnd : MemLp (Prod.snd : E × E → E) 2 (π : Measure (E × E)) := by
    simpa only [Function.comp_def, id_eq] using hν.comp_measurePreserving (measurePreserving_snd hπ)
  have hfi := hfst.comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => (π : Measure (E × E))) i)
  have hsi := hsnd.comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => (π : Measure (E × E))) (σ i))
  exact (memLp_two_iff_integrable_sq_norm (hfi.sub hsi).aestronglyMeasurable).mp (hfi.sub hsi)

end Quadratic

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Inner-product cyclic monotonicity of the support of a quadratic optimal plan. -/
theorem sum_inner_sub_le_zero_on_support {μ ν : ProbabilityMeasure E}
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    {π : ProbabilityMeasure (E × E)} (hπ : π ∈ couplings μ ν)
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, ‖z.1 - z.2‖^2 ∂(π : Measure (E × E))) ≤
        ∫ z, ‖z.1 - z.2‖^2 ∂(ρ : Measure (E × E)))
    (σ : Equiv.Perm ι) (z : ι → E × E)
    (hz : ∀ i, z i ∈ (π : Measure (E × E)).support) :
    ∑ i, inner ℝ (z i).2 ((z (σ i)).1 - (z i).1) ≤ 0 := by
  have hq := sum_quadratic_le_sum_permuted_on_support hμ hν hπ hmin σ.symm z hz
  have he : (∑ i, ‖(z i).1 - (z (σ.symm i)).2‖^2) =
      ∑ i, ‖(z (σ i)).1 - (z i).2‖^2 := by
    simpa using (Equiv.sum_comp σ (fun i => ‖(z i).1 - (z (σ.symm i)).2‖^2)).symm
  rw [he] at hq
  simp_rw [norm_sub_sq_real] at hq
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hq
  rw [Equiv.sum_comp σ (fun i => ‖(z i).1‖^2)] at hq
  calc
    _ = (∑ i, inner ℝ (z (σ i)).1 (z i).2) - ∑ i, inner ℝ (z i).1 (z i).2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sub_right, real_inner_comm (z i).2 (z (σ i)).1,
        real_inner_comm (z i).2 (z i).1]
    _ ≤ 0 := by linarith

end InnerProduct

end Submission.Lib.Brenier.OptimalCoupling
