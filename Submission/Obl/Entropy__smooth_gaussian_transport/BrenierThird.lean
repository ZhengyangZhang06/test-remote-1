import Submission.Obl.Entropy__smooth_gaussian_transport.ThirdRegularity

open MeasureTheory ProbabilityTheory Set

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_contDiff_three {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) : ContDiff ℝ 3 φ := by
  have hC2 := brenier_contDiff_two hm hV ha hH hφ hlaw
  apply transport_contDiff_three hC2
    (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff.log
      (fun x => (Submission.Lib.EntropyRemainder.gaussianDensity_pos x).ne')) hV
    (fun x => (brenier_positive_hessian hm hV ha hH hφ hlaw x).1)
    (brenier_log_det_equation hm hV ha hH hφ hlaw)
  intro K hK
  obtain ⟨α, C, hα, hα1, hC, hmod⟩ := brenier_hessian_compact_holder hm hV ha hH hφ hlaw hK
  obtain ⟨D, hD, hd⟩ := compact_hessian_holder_of_operator_holder hC2 hC.le hmod
  exact ⟨α, D, hα, hα1, hD, hd⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
