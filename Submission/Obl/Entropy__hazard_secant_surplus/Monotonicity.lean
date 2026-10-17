import Submission.Obl.Entropy__hazard_secant_surplus.Basic

open Set

namespace Submission.Obl.Entropy__hazard_secant_surplus

open Submission.Lib.GaussianTransport

lemma monotoneOn_dividedDifference {f : ℝ → ℝ} {s : Set ℝ}
    (hc : ConvexOn ℝ s f) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    {c : ℝ} (hc' : c ∈ s) : MonotoneOn (fun x => dividedDifference f x c) s := by
  intro a ha b hb hab
  by_cases hac : a = c
  · subst a
    by_cases hbc : b = c
    · subst b; exact le_rfl
    · simp only [dividedDifference, ite_true, if_neg hbc]
      simpa only [slope_def_field] using
        hc.deriv_le_slope hc' hb (lt_of_le_of_ne hab (Ne.symm hbc)) (hd c hc')
  · by_cases hbc : b = c
    · subst b
      simp only [dividedDifference, if_neg hac, ite_true]
      have h := hc.slope_le_deriv ha hc' (lt_of_le_of_ne hab hac) (hd c hc')
      rw [slope_comm] at h
      simpa only [slope_def_field] using h
    · simp only [dividedDifference, if_neg hac, if_neg hbc]
      simpa only [slope_def_field] using
        hc.slope_mono hc' ⟨ha, hac⟩ ⟨hb, hbc⟩ hab

noncomputable def weightedSquare (u : ℝ) : ℝ :=
  gaussianHazard (inverseGaussianHazard u) * transportRatio (inverseGaussianHazard u) ^ 2

lemma hasDerivAt_weightedSquare {u : ℝ} (hu : 0 < u) :
    HasDerivAt weightedSquare (scalarM (inverseGaussianHazard u)) u := by
  convert! (hasDerivAt_weighted_square (inverseGaussianHazard u)).comp u
    (hasStrictDerivAt_inverseGaussianHazard hu).hasDerivAt using 1
  rw [(hasDerivAt_gaussianHazard _).deriv]
  change _ = scalarM (inverseGaussianHazard u) *
    (gaussianHazard (inverseGaussianHazard u) * gaussianGap (inverseGaussianHazard u)) *
      (gaussianHazard (inverseGaussianHazard u) * gaussianGap (inverseGaussianHazard u))⁻¹
  field_simp [ne_of_gt (gaussianHazard_pos (inverseGaussianHazard u)),
    ne_of_gt (gaussianGap_pos (inverseGaussianHazard u))]

lemma arithmeticMean_eq_dividedDifference (a b : ℝ) :
    arithmeticMean a b = dividedDifference weightedSquare (gaussianHazard a) (gaussianHazard b) := by
  by_cases hab : a = b
  · subst b
    simp only [arithmeticMean_self, dividedDifference, ite_true,
      (hasDerivAt_weightedSquare (gaussianHazard_pos a)).deriv,
      inverseGaussianHazard_gaussianHazard]
  · have hq : gaussianHazard a ≠ gaussianHazard b := strictMono_gaussianHazard.injective.ne hab
    simp only [arithmeticMean, if_neg hab, dividedDifference, if_neg hq, weightedSquare,
      inverseGaussianHazard_gaussianHazard]

lemma convexOn_weightedSquare (hm : Monotone scalarM) :
    ConvexOn ℝ (Ioi 0) weightedSquare := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi (0 : ℝ))
  · exact fun u hu => (hasDerivAt_weightedSquare hu).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun u hu => (hasDerivAt_weightedSquare hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro u hu v hv huv
    rw [(hasDerivAt_weightedSquare hu).deriv, (hasDerivAt_weightedSquare hv).deriv]
    exact hm (strictMonoOn_inverseGaussianHazard.monotoneOn hu hv huv)

lemma monotone_arithmeticMean_of_monotone (hm : Monotone scalarM) (c : ℝ) :
    Monotone (fun a => arithmeticMean a c) := by
  intro a b hab
  change arithmeticMean a c ≤ arithmeticMean b c
  rw [arithmeticMean_eq_dividedDifference, arithmeticMean_eq_dividedDifference]
  exact monotoneOn_dividedDifference (convexOn_weightedSquare hm)
    (fun u hu => (hasDerivAt_weightedSquare hu).differentiableAt)
    (gaussianHazard_pos c) (gaussianHazard_pos a) (gaussianHazard_pos b)
    (strictMono_gaussianHazard.monotone hab)

end Submission.Obl.Entropy__hazard_secant_surplus
