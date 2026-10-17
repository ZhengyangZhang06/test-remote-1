import Submission.Obl.Entropy__transport_integrated_multiplier.MatrixLp
import Submission.Lib.GaussianTransport.GaussianModel

open MeasureTheory Set
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]

omit [TopologicalSpace X] [Fintype ι] [DecidableEq ι] in
/-- A continuous scalar observation of a bounded Hermitian field is bounded. -/
lemma bounded_observation_of_hermitian
    {A : X → Matrix ι ι ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : Matrix ι ι ℝ → ℝ} (hf : ContinuousOn f {B | B.IsHermitian}) :
    ∃ C : ℝ, ∀ x, ‖f (A x)‖ ≤ C := by
  obtain ⟨R, hR, hRb⟩ := hAb
  let s : Set (Matrix ι ι ℝ) := {B | ∀ i j, B i j ∈ Icc (-R) R}
  have hs : IsCompact s := isCompact_pi_infinite fun i =>
    isCompact_pi_infinite fun j => isCompact_Icc
  have hh : IsClosed {B : Matrix ι ι ℝ | B.IsHermitian} :=
    isClosed_eq continuous_star continuous_id
  obtain ⟨C, hC⟩ := (hs.inter_right hh).exists_bound_of_continuousOn
    (hf.mono inter_subset_right)
  exact ⟨C, fun x => hC (A x) ⟨fun i j => abs_le.mp (hRb x i j), hA x⟩⟩

lemma continuousOn_cfc_hermitian {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousOn (fun B : Matrix ι ι ℝ => cfc f B) {B | B.IsHermitian} := by
  exact continuousOn_id.cfc_of_mem_nhdsSet f (s := univ) (by simp)
    (fun B hB => hB.isSelfAdjoint) hf.continuousOn

omit [TopologicalSpace X] in
/-- Continuous functional calculus preserves boundedness of a Hermitian field, entrywise. -/
lemma bounded_cfc_entries {A : X → Matrix ι ι ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (i j : ι) :
    ∃ C : ℝ, ∀ x, ‖cfc f (A x) i j‖ ≤ C := by
  apply bounded_observation_of_hermitian (f := fun B => cfc f B i j) hA hAb
  exact (continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn (continuousOn_cfc_hermitian hf))

lemma continuous_cfc_field {A : X → Matrix ι ι ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x => cfc f (A x)) := by
  exact (continuousOn_cfc_hermitian hf).comp_continuous hAc hA

lemma entryLp_top_cfc [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {A : X → Matrix ι ι ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) :
    EntryLp ∞ (fun x => cfc f (A x)) μ := by
  intro i j
  obtain ⟨C, hC⟩ := bounded_cfc_entries hA hAb hf i j
  apply memLp_top_of_bound _ C (ae_of_all _ hC)
  exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_cfc_field hA hAc hf))).aestronglyMeasurable

lemma entryLp_top_inverse_cfc [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {A : X → Matrix ι ι ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, f t ≠ 0) :
    EntryLp ∞ (fun x => (cfc f (A x))⁻¹) μ := by
  have h := entryLp_top_cfc (μ := μ) hA hAc hAb (hf.inv₀ hf0)
  have he (x : X) : cfc (fun t => (f t)⁻¹) (A x) = (cfc f (A x))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact cfc_inv f (A x) (fun t _ => hf0 t) hf.continuousOn (hA x).isSelfAdjoint
  change EntryLp ∞ (fun x => cfc (fun t : ℝ => (f t)⁻¹) (A x)) μ at h
  simp_rw [he] at h
  exact h

end Submission.Obl.Entropy__transport_integrated_multiplier
