import Submission.Obl.Root.Normalization
import Submission.Obl.Root.Reduction
import Submission.Obl.Root.DensityAffine

open MeasureTheory
open Submission.Lib.EntropyTools

namespace Submission.Obl.Root

/-- Every density in the entropy theorem can be centered and put in identity-covariance position. -/
theorem exists_isotropic_density {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hu : UpperSemicontinuous f)
    (hc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hf : Integrable f) (hmass : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2))
    (hent : Integrable (fun x => f x * Real.log (f x))) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, 0 ≤ g x) ∧ UpperSemicontinuous g ∧
      ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) ∧
      Integrable g ∧ (∫ x, g x) = 1 ∧
      Integrable (fun x => g x * ‖x‖ ^ 2) ∧
      Integrable (fun x => g x * Real.log (g x)) ∧
      densityMean g = 0 ∧ densityCov g = 1 ∧
      densityEntropy g = densityEntropy f - Real.log (densityCov f).det / 2 := by
  have hp : (densityCov f).PosDef := densityCovariance_posDef hf0 hf hmass hf2 _
  obtain ⟨e, he⟩ := exists_covariance_normalizer (densityCov f) hp
  let b := -e (densityMean f)
  let g := DensityAffine.affineDensity e b f
  have hmean : densityMean g = 0 := by
    change (∫ y, DensityAffine.affineDensity e b f y • y) = 0
    rw [DensityAffine.mean_affineDensity e b hf (integrable_density_smul hf0 hf hf2) hmass]
    exact add_neg_cancel _
  have hcov : densityCov g = 1 := by
    have h := DensityAffine.covariance_affineDensity e b (densityMean f) hf0 hf hf2
    change densityCovariance g (e (densityMean f) + b) = _ at h
    have hb : e (densityMean f) + b = densityMean g := by rw [hmean]; exact add_neg_cancel _
    rw [hb] at h
    exact h.trans he
  refine ⟨g, DensityAffine.affineDensity_nonneg e b hf0,
    DensityAffine.upperSemicontinuous_affineDensity e b hu,
    DensityAffine.log_concave_affineDensity e b hc,
    DensityAffine.integrable_affineDensity e b hf, ?_,
    DensityAffine.integrable_second_affineDensity e b hf0 hf hf2,
    DensityAffine.integrable_entropy_affineDensity e b hf hent, hmean, hcov, ?_⟩
  · exact (DensityAffine.integral_affineDensity e b f).trans hmass
  · have h := DensityAffine.entropy_deficit_affineDensity e b hf0 hf hmass hf2 hent
    change densityEntropy g - Real.log (densityCov g).det / 2 =
      densityEntropy f - Real.log (densityCov f).det / 2 at h
    simpa only [hcov, Matrix.det_one, Real.log_one, zero_div, sub_zero] using h

/-- It suffices to prove the entropy inequality for centered densities of identity covariance. -/
theorem entropy_lower_bound_of_isotropic_case (n : ℕ)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, 0 ≤ g x) → UpperSemicontinuous g →
      ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) →
      Integrable g → (∫ x, g x) = 1 →
      Integrable (fun x => g x * ‖x‖ ^ 2) →
      Integrable (fun x => g x * Real.log (g x)) →
      densityMean g = 0 → densityCov g = 1 → (n : ℝ) ≤ densityEntropy g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hu : UpperSemicontinuous f)
    (hc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hf : Integrable f) (hmass : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2))
    (hent : Integrable (fun x => f x * Real.log (f x))) :
    (n : ℝ) + Real.log (densityCov f).det / 2 ≤ densityEntropy f := by
  obtain ⟨g, hg0, hgu, hgc, hg, hgmass, hg2, hgent, hgmean, hgcov, hgH⟩ :=
    exists_isotropic_density f hf0 hu hc hf hmass hf2 hent
  have h := hbound g hg0 hgu hgc hg hgmass hg2 hgent hgmean hgcov
  rw [hgH] at h
  linarith

end Submission.Obl.Root
