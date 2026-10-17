import Mathlib

open MeasureTheory Set Filter BoxIntegral
open scoped Topology ENNReal

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem box_split_inter_measure {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) {S : Set (ι → ℝ)} (hS : MeasurableSet S) (J : Box ι) :
    μ (S ∩ (J : Set (ι → ℝ))) =
      ∑ s : Set ι, μ (S ∩ (J.splitCenterBox s : Set (ι → ℝ))) := by
  classical
  have he : S ∩ (J : Set (ι → ℝ)) =
      ⋃ s : Set ι, S ∩ (J.splitCenterBox s : Set (ι → ℝ)) := by
    rw [← inter_iUnion, Box.iUnion_coe_splitCenterBox]
  have hdisj : Pairwise (fun s t : Set ι => Disjoint
      (S ∩ (J.splitCenterBox s : Set (ι → ℝ)))
      (S ∩ (J.splitCenterBox t : Set (ι → ℝ)))) := by
    intro s t hst
    exact (J.disjoint_splitCenterBox hst).mono inter_subset_right inter_subset_right
  rw [he, measure_iUnion hdisj (fun s => hS.inter (J.splitCenterBox s).measurableSet_coe),
    tsum_fintype]

/-- A subdivision form of the growing-level-set argument. The shape predicate
lets the application restrict attention to cubes. A strict separation between
the two level sets supplies the neighborhood condition, so no differentiation
theorem for dyadic averages is needed. -/
theorem box_measure_decay {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (I : Box ι) {S T : Set (ι → ℝ)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) {θ : ℝ≥0∞}
    {Q : Box ι → Prop} (hQI : Q I)
    (hQsplit : ∀ J, Q J → ∀ s, Q (J.splitCenterBox s))
    (hcover : ∀ z ∈ I.Icc, z ∈ interior T ∨ z ∈ interior Sᶜ)
    (hsmall : μ (S ∩ (I : Set (ι → ℝ))) ≤ θ * μ I)
    (hparent : ∀ J ≤ I, Q J → ∀ s : Set ι,
      θ * μ (J.splitCenterBox s) < μ (S ∩ (J.splitCenterBox s : Set (ι → ℝ))) →
        (J : Set (ι → ℝ)) ⊆ T) :
    μ (S ∩ (I : Set (ι → ℝ))) ≤ θ * μ (T ∩ (I : Set (ι → ℝ))) := by
  classical
  have haux : Q I →
      μ (S ∩ (I : Set (ι → ℝ))) ≤ θ * μ (T ∩ (I : Set (ι → ℝ))) ∨
        (I : Set (ι → ℝ)) ⊆ T := by
    refine Box.subbox_induction_on' (p := fun J => Q J →
      μ (S ∩ (J : Set (ι → ℝ))) ≤ θ * μ (T ∩ (J : Set (ι → ℝ))) ∨
        (J : Set (ι → ℝ)) ⊆ T) I ?_ ?_
    · intro J hJI ih hQJ
      by_cases hh : ∃ s : Set ι,
          θ * μ (J.splitCenterBox s) < μ (S ∩ (J.splitCenterBox s : Set (ι → ℝ)))
      · obtain ⟨s, hs⟩ := hh
        exact Or.inr (hparent J hJI hQJ s hs)
      · left
        rw [box_split_inter_measure μ hS, box_split_inter_measure μ hT, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro s _
        rcases ih s (hQsplit J hQJ s) with hs | hs
        · exact hs
        · rw [inter_eq_right.mpr hs]
          exact le_of_not_gt (fun h => hh ⟨s, h⟩)
    · intro z hz
      rcases hcover z hz with hzT | hzS
      · refine ⟨interior T, mem_nhdsWithin_of_mem_nhds
          (isOpen_interior.mem_nhds hzT), ?_⟩
        intro J _ _ _ hJU _ _
        exact Or.inr ((Box.coe_subset_Icc.trans hJU).trans interior_subset)
      · refine ⟨interior Sᶜ, mem_nhdsWithin_of_mem_nhds
          (isOpen_interior.mem_nhds hzS), ?_⟩
        intro J _ _ _ hJU _ _
        left
        have he : S ∩ (J : Set (ι → ℝ)) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact interior_subset (hJU (Box.coe_subset_Icc hx.2)) hx.1
        rw [he, measure_empty]
        exact zero_le
  rcases haux hQI with h | h
  · exact h
  · rwa [inter_eq_right.mpr h]

theorem box_levelset_measure_decay {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (I : Box ι) {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    {α β : ℝ} (hβα : β < α) {θ : ℝ≥0∞}
    {Q : Box ι → Prop} (hQI : Q I)
    (hQsplit : ∀ J, Q J → ∀ s, Q (J.splitCenterBox s))
    (hsmall : μ ({x | α < f x} ∩ (I : Set (ι → ℝ))) ≤ θ * μ I)
    (hparent : ∀ J ≤ I, Q J → ∀ s : Set ι,
      θ * μ (J.splitCenterBox s) < μ ({x | α < f x} ∩ (J.splitCenterBox s : Set (ι → ℝ))) →
        ∀ x ∈ (J : Set (ι → ℝ)), β < f x) :
    μ ({x | α < f x} ∩ (I : Set (ι → ℝ))) ≤
      θ * μ ({x | β < f x} ∩ (I : Set (ι → ℝ))) := by
  apply box_measure_decay μ I (isOpen_lt continuous_const hf).measurableSet
    (isOpen_lt continuous_const hf).measurableSet hQI hQsplit ?_ hsmall hparent
  intro z _
  by_cases hz : β < f z
  · left
    rwa [(isOpen_lt continuous_const hf).interior_eq]
  · right
    have hza : f z < α := (le_of_not_gt hz).trans_lt hβα
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hza] with y hy
    exact not_lt.mpr hy.le

end Submission.Obl.Entropy__smooth_gaussian_transport
