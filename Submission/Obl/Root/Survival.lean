import Mathlib

open MeasureTheory Set

namespace Submission.Obl.Root.Survival

/-- A submultiplicative survival function has first tail moment bounded by the square
of its mass. The comparison is integrated over each segment `0 ≤ u ≤ t`, then Fubini
identifies the forward-convolution integral. -/
theorem integral_mul_le_integral_sq {S : ℝ → ℝ}
    (hS : Continuous S) (hS0 : IntegrableOn S (Ioi 0))
    (hS1 : IntegrableOn (fun t => t * S t) (Ioi 0))
    (hsub : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → S (u + v) ≤ S u * S v) :
    (∫ t in Ioi 0, t * S t) ≤ (∫ t in Ioi 0, S t) ^ 2 := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hc : IntegrableOn (fun t : ℝ => ∫ u : ℝ in 0..t, S u * S (t - u))
      (Ioi 0) := by
    have hi := integrable_posConvolution hS0 hS0 L
    rw [posConvolution, integrable_indicator_iff measurableSet_Ioi] at hi
    exact hi
  have hb (t : ℝ) (ht : t ∈ Ioi 0) :
      t * S t ≤ ∫ u : ℝ in 0..t, S u * S (t - u) := by
    have hc' : Continuous (fun u : ℝ => S u * S (t - u)) :=
      hS.mul (hS.comp (continuous_const.sub continuous_id))
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun _ : ℝ => S t) ht.le
      (continuous_const.intervalIntegrable 0 t) (hc'.intervalIntegrable 0 t)
      (fun u hu => by
        simpa only [add_sub_cancel] using
          hsub u (t - u) hu.1 (sub_nonneg.mpr hu.2))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
  calc
    (∫ t in Ioi 0, t * S t) ≤
        ∫ t in Ioi 0, ∫ u : ℝ in 0..t, S u * S (t - u) :=
      setIntegral_mono_on hS1 hc measurableSet_Ioi hb
    _ = (∫ t in Ioi 0, S t) ^ 2 := by
      simpa only [L, ContinuousLinearMap.mul_apply', pow_two] using
        integral_posConvolution hS0 hS0 L

end Submission.Obl.Root.Survival
