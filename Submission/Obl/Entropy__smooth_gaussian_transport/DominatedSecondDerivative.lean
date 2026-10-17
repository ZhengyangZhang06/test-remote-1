import Mathlib

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem norm_smul_clm {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℝ) (A : X →L[ℝ] Y) : ‖r • A‖ = ‖r‖ * ‖A‖ := norm_smul r A

theorem integral_clm_apply_of_norm_bound
    {A X Y : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {G : A → X →L[ℝ] Y} {b : A → ℝ}
    (hm : AEStronglyMeasurable G μ) (hi : Integrable b μ)
    (hb : ∀ᵐ a ∂μ, ‖G a‖ ≤ b a) (v : X) :
    (∫ a, G a ∂μ) v = ∫ a, G a v ∂μ := by
  have hI : Integrable G μ := hi.mono' hm hb
  exact ContinuousLinearMap.integral_apply hI v

/-- Twice differentiating under an integral, with separate integrable bounds
for the function and its first two derivatives. -/
theorem integral_contDiff_two_of_dominated
    {A X Y : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {F : A → X → Y} {F' : A → X → X →L[ℝ] Y}
    {F'' : A → X → X →L[ℝ] (X →L[ℝ] Y)}
    {b₀ b₁ b₂ : A → ℝ}
    (hi₀ : Integrable b₀ μ) (hi₁ : Integrable b₁ μ) (hi₂ : Integrable b₂ μ)
    (hm₀ : ∀ x, AEStronglyMeasurable (fun a => F a x) μ)
    (hm₁ : ∀ x, AEStronglyMeasurable (fun a => F' a x) μ)
    (hm₂ : ∀ x, AEStronglyMeasurable (fun a => F'' a x) μ)
    (hb₀ : ∀ᵐ a ∂μ, ∀ x, ‖F a x‖ ≤ b₀ a)
    (hb₁ : ∀ᵐ a ∂μ, ∀ x, ‖F' a x‖ ≤ b₁ a)
    (hb₂ : ∀ᵐ a ∂μ, ∀ x, ‖F'' a x‖ ≤ b₂ a)
    (hd₀ : ∀ᵐ a ∂μ, ∀ x, HasFDerivAt (F a) (F' a x) x)
    (hd₁ : ∀ᵐ a ∂μ, ∀ x, HasFDerivAt (F' a) (F'' a x) x)
    (hc₂ : ∀ᵐ a ∂μ, Continuous (F'' a)) :
    ContDiff ℝ 2 (fun x => ∫ a, F a x ∂μ) ∧
      (∀ x, fderiv ℝ (fun x => ∫ a, F a x ∂μ) x = ∫ a, F' a x ∂μ) ∧
      (∀ x v w, fderiv ℝ (fderiv ℝ (fun x => ∫ a, F a x ∂μ)) x v w =
        ∫ a, F'' a x v w ∂μ) := by
  have hd (x : X) : HasFDerivAt (fun x => ∫ a, F a x ∂μ) (∫ a, F' a x ∂μ) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := b₁) (F' := fun x a => F' a x)
      (Filter.univ_mem) (Filter.Eventually.of_forall hm₀)
      (hi₀.mono' (hm₀ x) (hb₀.mono (fun a ha => ha x))) (hm₁ x)
    · exact hb₁.mono (fun a ha x _ => ha x)
    · exact hi₁
    · exact hd₀.mono (fun a ha x _ => ha x)
  have hd' (x : X) : HasFDerivAt (fun x => ∫ a, F' a x ∂μ) (∫ a, F'' a x ∂μ) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := b₂) (F' := fun x a => F'' a x)
      (Filter.univ_mem) (Filter.Eventually.of_forall hm₁)
      (hi₁.mono' (hm₁ x) (hb₁.mono (fun a ha => ha x))) (hm₂ x)
    · exact hb₂.mono (fun a ha x _ => ha x)
    · exact hi₂
    · exact hd₁.mono (fun a ha x _ => ha x)
  have hc : Continuous (fun x => ∫ a, F'' a x ∂μ) :=
    continuous_of_dominated hm₂ (fun x => hb₂.mono (fun a ha => ha x)) hi₂ hc₂
  have hC1 : ContDiff ℝ 1 (fun x => ∫ a, F' a x ∂μ) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨_, hc, hd'⟩
  have hC2 : ContDiff ℝ 2 (fun x => ∫ a, F a x ∂μ) :=
    (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨_, hC1, hd⟩
  refine ⟨hC2, fun x => (hd x).fderiv, ?_⟩
  have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = fun x => ∫ a, F' a x ∂μ := funext (fun x => (hd x).fderiv)
  intro x v w
  rw [he, (hd' x).fderiv]
  rw [integral_clm_apply_of_norm_bound (hm₂ x) hi₂ (hb₂.mono (fun a ha => ha x)) v]
  apply integral_clm_apply_of_norm_bound
    ((hm₂ x).apply_continuousLinearMap v) (hi₂.mul_const ‖v‖) _ w
  filter_upwards [hb₂] with a ha
  exact ((F'' a x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (ha x) (norm_nonneg v))

end Submission.Obl.Entropy__smooth_gaussian_transport
