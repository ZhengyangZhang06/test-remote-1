import Submission.Obl.Entropy__affine_limit_density.Covariance
import Submission.Obl.Entropy__affine_exponential_moments.Exponential

open MeasureTheory
open scoped Topology

namespace Submission.Obl.Entropy__affine_limit_density

open Submission.Obl.Entropy__affine_exponential_moments

/-- Undo an affine pushforward at the level of real-valued densities. -/
theorem ae_eq_affineDensity_of_map_eq {m : ℕ} {f g : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g volume)
    (P : E m ≃L[ℝ] E m) (b : E m)
    (hlaw : Measure.map (fun x => P (x - b))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) :
    f =ᵐ[volume] affineDensity P.symm b g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq f (affineDensity P.symm b g)
    hf (integrable_affineDensity P.symm b hg)
  intro s hs _
  let k : E m → ℝ := fun y => s.indicator (fun _ => (1 : ℝ)) (P.symm y + b)
  have hk : Measurable k := (measurable_const.indicator hs).comp (by fun_prop)
  have hP : Continuous (fun x => P (x - b)) := by fun_prop
  have heq := congrArg (fun μ : Measure (E m) => ∫ y, k y ∂μ) hlaw
  rw [integral_map hP.aemeasurable hk.aestronglyMeasurable,
    integral_density hf0 hf, integral_density hg0 hg] at heq
  have hleft : (∫ x, f x * k (P (x - b))) = ∫ x in s, f x := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [k, hx]
  have hright : (∫ x, g x * k x) = ∫ x in s, affineDensity P.symm b g x := by
    rw [← integral_indicator hs]
    have h := integral_affineDensity_smul P.symm b g (s.indicator (fun _ => (1 : ℝ)))
    simp only [smul_eq_mul] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  exact hleft.symm.trans (heq.trans hright)

end Submission.Obl.Entropy__affine_limit_density
