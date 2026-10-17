import Submission.Lib.GaussianTransport.GaussianSlope

open scoped Topology

namespace Submission.Obl.Entropy__hessian_spectral_surplus

open Submission.Lib.GaussianTransport

noncomputable def secantMultiplier (q k : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a = b then k a ^ 2 + 2 * k a * deriv k a / (q a - a)
  else (q a * k a ^ 2 - q b * k b ^ 2) / (q a - q b)

lemma dslope_eq_dividedDifference (f : ℝ → ℝ) (a b : ℝ) :
    dslope f a b = if a = b then deriv f a else (f a - f b) / (a - b) := by
  by_cases h : a = b
  · subst b
    simp
  · rw [if_neg h, dslope_of_ne f (Ne.symm h), slope_def_field]
    field_simp [sub_ne_zero.mpr h, sub_ne_zero.mpr (Ne.symm h)]
    <;> ring

/-- The multiplier coefficient identity, in a form with no divided-difference denominator. -/
lemma secantMultiplier_coefficient_identity {q k : ℝ → ℝ}
    (hq : Function.Injective q) (hqd : ∀ a, deriv q a = q a * (q a - a))
    (hgap : ∀ a, q a - a ≠ 0) (a b : ℝ) :
    (q a * k a ^ 2 + q b * k b ^ 2) * (dslope q a b) ^ 2 +
      2 * q a * q b * (k a + k b) * dslope k a b * dslope q a b =
      (q a + q b) * secantMultiplier q k a b * (dslope q a b) ^ 2 := by
  by_cases hab : a = b
  · subst b
    simp only [dslope_same, secantMultiplier, ↓reduceIte, hqd]
    field_simp [hgap a] <;> ring
  · simp only [dslope_eq_dividedDifference, secantMultiplier, if_neg hab]
    have hqne : q a - q b ≠ 0 := sub_ne_zero.mpr (fun h => hab (hq h))
    field_simp [sub_ne_zero.mpr hab, hqne]
    ring

lemma scalar_multiplier_rewrite (lr li lj ki kj dq dk z B : ℝ)
    (hr : lr ≠ 0) (hi : li ≠ 0) (hj : lj ≠ 0)
    (hc : (li * ki ^ 2 + lj * kj ^ 2) * dq ^ 2 +
      2 * li * lj * (ki + kj) * dk * dq = (li + lj) * B * dq ^ 2) :
    ((ki ^ 2 * lr⁻¹ * lj⁻¹ + kj ^ 2 * lr⁻¹ * li⁻¹) / 2) * (dq * z) ^ 2 +
      lr⁻¹ * (ki + kj) * (dk * z) * (dq * z) =
      ((dq * z) ^ 2 / (lr * li * lj)) * ((li + lj) / 2) * B := by
  have hh := congrArg (fun t : ℝ => t * z ^ 2) hc
  field_simp
  nlinarith [hh]

end Submission.Obl.Entropy__hessian_spectral_surplus
