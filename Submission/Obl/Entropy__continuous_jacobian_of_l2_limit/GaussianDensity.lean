import Submission.Obl.Entropy__centered_slack_transports.Transport
import Submission.Lib.GaussianTransport.GaussianModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

noncomputable def gaussianDensity (x : E) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

lemma gaussianDensity_pos (x : E) : 0 < gaussianDensity x := by
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ (by simp)

lemma continuous_gaussianDensity : Continuous (gaussianDensity : E → ℝ) := by
  apply continuous_finsetProd
  intro i _
  exact Submission.Lib.GaussianTransport.contDiff_normalPDF.continuous.comp
    (EuclideanSpace.proj i).continuous

lemma pi_gaussian_density :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : Fin m → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) volume :=
    Integrable.fintype_prod fun _ => integrable_gaussianPDFReal 0 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi.restrict
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i))]
  change ENNReal.ofReal (∫ x, ∏ i, gaussianPDFReal 0 1 (x i)
    ∂(Measure.pi fun _ : Fin m => (volume : Measure ℝ)).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  congr 1
  funext i
  exact (gaussianReal_apply_eq_integral 0 (by simp) (s i)).symm

lemma stdGaussian_eq_withDensity :
    stdGaussian E = volume.withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density]
  change Measure.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) _ = _
  rw [Submission.Obl.Entropy__centered_slack_transports.map_withDensity_equiv]
  rw [show Measure.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) volume = volume from
    (PiLp.volume_preserving_toLp (Fin m)).map_eq]
  rfl

lemma gaussian_absolutelyContinuous_volume : stdGaussian E ≪ volume := by
  rw [stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

lemma volume_absolutelyContinuous_gaussian : volume ≪ stdGaussian E := by
  rw [stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous'
    continuous_gaussianDensity.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (gaussianDensity_pos x)).ne')

end Submission.Obl.Entropy__continuous_jacobian_of_l2_limit
