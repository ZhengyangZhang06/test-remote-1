import Mathlib

/-!
# Global inverse for uniformly positive derivatives

A uniformly positive quadratic derivative gives a quantitative lower bound on
distances. The inverse function theorem makes the range open, and properness makes
it closed. Connectedness then gives a global inverse.
-/

open Set Filter
open scoped Topology ContDiff

namespace Submission.Obl.Root.GlobalInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrating the derivative lower bound along a segment gives strong monotonicity. -/
lemma strong_mono_of_derivative {F : E → E} (hF : Differentiable ℝ F) {a : ℝ}
    (ha : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x y : E) :
    a * ‖y - x‖^2 ≤ inner ℝ (y - x) (F y - F x) := by
  let v := y - x
  let g : ℝ → ℝ := fun t => inner ℝ v (F (x + t • v)) - a * ‖v‖^2 * t
  have hd (t : ℝ) : HasDerivAt g
      (inner ℝ v (fderiv ℝ F (x + t • v) v) - a * ‖v‖^2) t := by
    have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hc := (hF _).hasFDerivAt.comp_hasDerivAt t hp
    simpa only [g, Function.comp_def, Pi.sub_apply, id_eq, mul_one, inner_zero_left,
      add_zero] using!
      ((hasDerivAt_const t v).inner ℝ hc).sub
        ((hasDerivAt_id t).const_mul (a * ‖v‖^2))
  have hm : Monotone g := monotone_of_hasDerivAt_nonneg hd
    (fun t => sub_nonneg.mpr (ha _ v))
  have hh := hm (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [g, zero_smul, one_smul, add_zero, mul_zero, sub_zero, mul_one,
    v, add_sub_cancel] at hh
  rw [inner_sub_right]
  linarith

lemma mul_norm_sub_le {F : E → E} (hF : Differentiable ℝ F) {a : ℝ}
    (ha : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x y : E) :
    a * ‖y - x‖ ≤ ‖F y - F x‖ := by
  have hh := (strong_mono_of_derivative hF ha x y).trans
    (real_inner_le_norm (y - x) (F y - F x))
  by_cases h : y = x
  · simp [h]
  · have hp : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    nlinarith

lemma antilipschitz_of_derivative {F : E → E} (hF : Differentiable ℝ F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    AntilipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ F := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist x y ≤ a⁻¹ * dist (F x) (F y)
  rw [dist_eq_norm, dist_eq_norm, ← div_eq_inv_mul, le_div_iff₀ ha]
  simpa only [mul_comm] using mul_norm_sub_le hF hlower y x

lemma injective_derivative {F : E → E} {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x : E) :
    Function.Injective (fderiv ℝ F x) := by
  intro v w h
  have hz : fderiv ℝ F x (v - w) = 0 := by rw [map_sub, h, sub_self]
  have hh := hlower x (v - w)
  rw [hz, inner_zero_right] at hh
  have hs : ‖v - w‖^2 ≤ 0 := (mul_le_mul_iff_right₀ ha).mp
    (by simpa only [mul_zero] using hh)
  have hn : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [FiniteDimensional ℝ E]

/-- The positive quadratic bound makes every derivative a linear isomorphism. -/
noncomputable def derivativeEquiv {F : E → E} {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x : E) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ F x).toLinearMap
    (injective_derivative ha hlower x)).toContinuousLinearEquiv

@[simp] lemma derivativeEquiv_toContinuousLinearMap {F : E → E} {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x : E) :
    (derivativeEquiv ha hlower x : E →L[ℝ] E) = fderiv ℝ F x := rfl

lemma isOpenMap_of_derivative {F : E → E} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    IsOpenMap F := by
  apply isOpenMap_of_hasStrictFDerivAt_equiv (f' := derivativeEquiv ha hlower)
  intro x
  rw [derivativeEquiv_toContinuousLinearMap]
  exact hF.contDiffAt.hasStrictFDerivAt one_ne_zero

lemma isProperMap_of_derivative {F : E → E} (hF : Differentiable ℝ F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    IsProperMap F := by
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨hF.continuous, ?_⟩
  simpa only [Metric.cobounded_eq_cocompact] using
    (antilipschitz_of_derivative hF ha hlower).tendsto_cobounded

/-- Uniformly positive derivatives force a `C1` map to be onto the whole space. -/
lemma surjective_of_derivative {F : E → E} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    Function.Surjective F := by
  have hc : IsClopen (range F) :=
    ⟨(isProperMap_of_derivative (hF.differentiable one_ne_zero) ha hlower).isClosed_range,
      (isOpenMap_of_derivative hF ha hlower).isOpen_range⟩
  exact range_eq_univ.mp (hc.eq_univ (range_nonempty F))

/-- The global inverse of a map with a uniformly positive derivative. -/
noncomputable def globalHomeomorph {F : E → E} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) : E ≃ₜ E :=
  (Equiv.ofBijective F
    ⟨(antilipschitz_of_derivative (hF.differentiable one_ne_zero) ha hlower).injective,
      surjective_of_derivative hF ha hlower⟩).toHomeomorphOfContinuousOpen
    hF.continuous (isOpenMap_of_derivative hF ha hlower)

@[simp] lemma globalHomeomorph_apply {F : E → E} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) (x : E) :
    globalHomeomorph hF ha hlower x = F x := rfl

lemma lipschitz_globalHomeomorph_symm {F : E → E} (hF : ContDiff ℝ 1 F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (globalHomeomorph hF ha hlower).symm :=
  (antilipschitz_of_derivative (hF.differentiable one_ne_zero) ha hlower).to_rightInverse
    (globalHomeomorph hF ha hlower).apply_symm_apply

/-- A smooth map with uniformly positive derivative has a smooth global inverse. -/
lemma contDiff_globalHomeomorph_symm {F : E → E} (hF : ContDiff ℝ ∞ F) {a : ℝ}
    (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖^2 ≤ inner ℝ v (fderiv ℝ F x v)) :
    ContDiff ℝ ∞ (globalHomeomorph (hF.of_le (by simp)) ha hlower).symm := by
  let e := globalHomeomorph (hF.of_le (by simp)) ha hlower
  rw [contDiff_iff_contDiffAt]
  intro y
  let x := e.symm y
  have he : F x = y := e.apply_symm_apply y
  have hf : ContDiffAt ℝ ∞ F x := hF.contDiffAt
  have hd : HasFDerivAt F (derivativeEquiv ha hlower x : E →L[ℝ] E) x := by
    rw [derivativeEquiv_toContinuousLinearMap]
    exact (hF.differentiable (by simp) x).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hf.hasStrictFDerivAt' hd hn
  have hg : e.symm =ᶠ[𝓝 (F x)] hf.localInverse hd hn := by
    filter_upwards [hs.eventually_right_inverse] with z hz
    apply e.injective
    rw [e.apply_symm_apply]
    change z = F (hf.localInverse hd hn z)
    exact hz.symm
  have hc := (hf.to_localInverse hd hn).congr_of_eventuallyEq hg
  simpa only [he] using hc

end Submission.Obl.Root.GlobalInverse
