import Mathlib

/-!
Covariance comparisons for the arithmetic and logarithmic averages in
Proposition 2.5. All integrability hypotheses are explicit.
-/

namespace Submission.Obl.Entropy__transport_energy_surplus

open MeasureTheory

/-- The covariance of two functions that vary in the same direction is nonnegative. -/
theorem integral_mul_ge_mul_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hmono : ∀ x y, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hp : ∀ x, f x * (∫ y, g y ∂μ) + g x * (∫ y, f y ∂μ) ≤
      f x * g x + ∫ y, f y * g y ∂μ := by
    intro x
    have h : 0 ≤ ∫ y, (f x - f y) * (g x - g y) ∂μ :=
      integral_nonneg (fun y => hmono x y)
    have he : (fun y => (f x - f y) * (g x - g y)) =
        (fun y => ((f x * g x - f x * g y) - g x * f y) + f y * g y) := by
      funext y
      ring
    have h1 : Integrable (fun y => f x * g x - f x * g y) μ :=
      (integrable_const _).sub (hg.const_mul (f x))
    have h2 : Integrable (fun y => f x * g x - f x * g y - g x * f y) μ :=
      h1.sub (hf.const_mul (g x))
    rw [he, integral_add h2 hfg, integral_sub h1 (hf.const_mul (g x)),
      integral_sub (integrable_const (f x * g x)) (hg.const_mul (f x)),
      integral_const_mul, integral_const_mul] at h
    simp only [integral_const_mul, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
    linarith
  have h := integral_mono ((hf.mul_const _).add (hg.mul_const _))
    (hfg.add (integrable_const _)) hp
  dsimp only [Pi.add_apply] at h
  rw [integral_add (hf.mul_const _) (hg.mul_const _),
    integral_add hfg (integrable_const _), integral_mul_const, integral_mul_const] at h
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
  nlinarith only [h]

/-- The Chebyshev inequality on any real probability space. -/
theorem integral_mul_ge_mul_integral_of_monotone
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f g : ℝ → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hfm : Monotone f) (hgm : Monotone g) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  apply integral_mul_ge_mul_integral μ f g hf hg hfg
  intro x y
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfm h))
      (sub_nonpos.mpr (hgm h))
  · exact mul_nonneg (sub_nonneg.mpr (hfm h)) (sub_nonneg.mpr (hgm h))

/-- Chebyshev's inequality for the increasing functions `D(1+b)` and `D(1-b)`,
 together with the lower bound coming from `0 ≤ b ≤ 1/2`. Here `B = bD`. -/
theorem logarithmic_chebyshev (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D B : ℝ → ℝ) (hD : Integrable D μ) (hB : Integrable B μ)
    (hM : Integrable (fun x => D x ^ 2 - B x ^ 2) μ)
    (hB0 : ∀ x, 0 ≤ B x) (hBD : ∀ x, B x ≤ D x / 2)
    (hplus : Monotone (fun x => D x + B x))
    (hminus : Monotone (fun x => D x - B x)) :
    (3 / 4 : ℝ) * (∫ x, D x ∂μ) ^ 2 ≤
      (∫ x, D x ∂μ) ^ 2 - (∫ x, B x ∂μ) ^ 2 ∧
    (∫ x, D x ∂μ) ^ 2 - (∫ x, B x ∂μ) ^ 2 ≤
      ∫ x, D x ^ 2 - B x ^ 2 ∂μ := by
  have hprod : (fun x => (D x + B x) * (D x - B x)) =
      (fun x => D x ^ 2 - B x ^ 2) := by funext x; ring
  have hp := integral_mul_ge_mul_integral_of_monotone μ
    (fun x => D x + B x) (fun x => D x - B x) (hD.add hB) (hD.sub hB)
    (hprod ▸ hM) hplus hminus
  rw [integral_add hD hB, integral_sub hD hB, hprod] at hp
  have hb0 : 0 ≤ ∫ x, B x ∂μ := integral_nonneg (fun x => hB0 x)
  have hbd := integral_mono hB (hD.div_const 2) hBD
  rw [integral_div] at hbd
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hbd)
      (show 0 ≤ (∫ x, D x ∂μ) / 2 + ∫ x, B x ∂μ by linarith)]
  · nlinarith only [hp]

end Submission.Obl.Entropy__transport_energy_surplus
