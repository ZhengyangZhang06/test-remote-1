import Submission.Obl.Entropy__hazard_secant_surplus.IntervalMeasure

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

lemma weighted_chebyshev {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f g : α → ℝ} (hw : Integrable w μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hwg : Integrable (fun x => w x * g x) μ)
    (hwfg : Integrable (fun x => w x * (f x * g x)) μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hfg : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, w x * f x ∂μ) * (∫ x, w x * g x ∂μ) ≤
      (∫ x, w x ∂μ) * (∫ x, w x * (f x * g x) ∂μ) := by
  let W := ∫ x, w x ∂μ
  let F := ∫ x, w x * f x ∂μ
  let G := ∫ x, w x * g x ∂μ
  let H := ∫ x, w x * (f x * g x) ∂μ
  have hinner : ∀ᵐ x ∂μ, 0 ≤ W * (f x * g x) - f x * G - g x * F + H := by
    filter_upwards [hfg] with x hx
    have hi : 0 ≤ ∫ y, w y * (f x - f y) * (g x - g y) ∂μ :=
      integral_nonneg_of_ae (by
        filter_upwards [hw0, hx] with y hy hxy
        change 0 ≤ w y * (f x - f y) * (g x - g y)
        simpa only [mul_assoc] using mul_nonneg hy hxy)
    have he (y : α) : w y * (f x - f y) * (g x - g y) =
        w y * (f x * g x) - f x * (w y * g y) - g x * (w y * f y) +
          w y * (f y * g y) := by ring
    simp_rw [he] at hi
    have hA : Integrable (fun y => w y * (f x * g x) - f x * (w y * g y)) μ :=
      (hw.mul_const (f x * g x)).sub (hwg.const_mul (f x))
    have hB : Integrable (fun y => w y * (f x * g x) - f x * (w y * g y) -
        g x * (w y * f y)) μ := hA.sub (hwf.const_mul (g x))
    rw [integral_add hB hwfg, integral_sub hA (hwf.const_mul (g x)),
      integral_sub (hw.mul_const (f x * g x)) (hwg.const_mul (f x)), integral_mul_const,
      integral_const_mul, integral_const_mul] at hi
    exact hi
  have hout : 0 ≤ ∫ x, w x * (W * (f x * g x) - f x * G - g x * F + H) ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hw0, hinner] with x hx hi; exact mul_nonneg hx hi)
  have he (x : α) : w x * (W * (f x * g x) - f x * G - g x * F + H) =
      W * (w x * (f x * g x)) - (w x * f x) * G - (w x * g x) * F + w x * H := by ring
  simp_rw [he] at hout
  have hA : Integrable (fun x => W * (w x * (f x * g x)) - (w x * f x) * G) μ :=
    (hwfg.const_mul W).sub (hwf.mul_const G)
  have hB : Integrable (fun x => W * (w x * (f x * g x)) - (w x * f x) * G -
      (w x * g x) * F) μ := hA.sub (hwg.mul_const F)
  rw [integral_add hB (hw.mul_const H), integral_sub hA (hwg.mul_const F),
    integral_sub (hwfg.const_mul W) (hwf.mul_const G), integral_const_mul,
    integral_mul_const, integral_mul_const, integral_mul_const] at hout
  change 0 ≤ W * H - F * G - G * F + W * H at hout
  change F * G ≤ W * H
  nlinarith

lemma monotone_difference_product {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hx hy hxy))
      (sub_nonpos.mpr (hg hx hy hxy))
  · exact mul_nonneg (sub_nonneg.mpr (hf hy hx hyx)) (sub_nonneg.mpr (hg hy hx hyx))

lemma interval_weighted_chebyshev {u v : ℝ} (huv : u ≤ v) {w f g : ℝ → ℝ}
    (hw : ContinuousOn w (Icc u v)) (hf : ContinuousOn f (Icc u v))
    (hg : ContinuousOn g (Icc u v)) (hw0 : ∀ x ∈ Icc u v, 0 ≤ w x)
    (hmf : MonotoneOn f (Icc u v)) (hmg : MonotoneOn g (Icc u v)) :
    (∫ x in u..v, w x * f x) * (∫ x in u..v, w x * g x) ≤
      (∫ x in u..v, w x) * (∫ x in u..v, w x * (f x * g x)) := by
  have h := weighted_chebyshev (μ := volume.restrict (Icc u v))
    hw.integrableOn_Icc (hw.mul hf).integrableOn_Icc (hw.mul hg).integrableOn_Icc
    (hw.mul (hf.mul hg)).integrableOn_Icc
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hw0))
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun x hx =>
      (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun y hy =>
        monotone_difference_product hmf hmg hx hy)))
  simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv] using h

end Submission.Obl.Entropy__hazard_secant_surplus
