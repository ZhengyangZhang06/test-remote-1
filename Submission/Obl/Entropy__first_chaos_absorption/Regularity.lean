import Mathlib

open Matrix MeasureTheory Set
open scoped BigOperators

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma continuous_cfc_field {Ω : Type*} [TopologicalSpace Ω]
    {A : Ω → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hc : ∀ i j, Continuous (fun x => A x i j)) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x => cfc f (A x)) := by
  exact Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) Filter.univ_mem
    (continuous_pi fun i => continuous_pi fun j => hc i j)
    (fun x => (hA x).isSelfAdjoint) hf.continuousOn

/-- On bounded Hermitian matrices, each entry of the functional calculus of a
continuous scalar function is uniformly bounded. -/
lemma cfc_entry_bound {f : ℝ → ℝ} (hf : Continuous f) (R : ℝ) (i j : n) :
    ∃ C : ℝ, ∀ A : Matrix n n ℝ, A.IsHermitian → (∀ k l, |A k l| ≤ R) →
      ‖cfc f A i j‖ ≤ C := by
  let K : Set (Matrix n n ℝ) :=
    {A | ∀ k l, A k l ∈ Icc (-R) R} ∩ {A | A.IsHermitian}
  have hbox : IsCompact {A : Matrix n n ℝ | ∀ k l, A k l ∈ Icc (-R) R} :=
    isCompact_pi_infinite fun k => isCompact_pi_infinite fun l => isCompact_Icc
  have hh : IsClosed {A : Matrix n n ℝ | A.IsHermitian} := by
    exact isClosed_eq (by fun_prop) continuous_id
  have hK : IsCompact K := hbox.inter_right hh
  have hcfc : ContinuousOn (fun A : Matrix n n ℝ => cfc f A) K :=
    ContinuousOn.cfc_of_mem_nhdsSet f (s := Set.univ) Filter.univ_mem continuousOn_id
      (fun A hAK => hAK.2.isSelfAdjoint) hf.continuousOn
  have hc : ContinuousOn (fun A : Matrix n n ℝ => cfc f A i j) K :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hcfc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨C, fun A hA hbound => hC A ⟨?_, hA⟩⟩
  intro k l
  exact abs_le.mp (hbound k l)

lemma integrable_cfc_entry {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Ω → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hc : ∀ i j, Continuous (fun x => A x i j))
    (hb : ∃ R : ℝ, ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (i j : n) :
    Integrable (fun x => cfc f (A x) i j) μ := by
  obtain ⟨R, hR⟩ := hb
  obtain ⟨C, hC⟩ := cfc_entry_bound hf R i j
  have hcont : Continuous (fun x => cfc f (A x) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_cfc_field hA hc hf))
  exact Integrable.of_bound hcont.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC (A x) (hA x) (hR x))

end Submission.Obl.Entropy__first_chaos_absorption
