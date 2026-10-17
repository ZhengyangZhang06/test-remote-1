import Submission.Obl.Entropy__smooth_gaussian_transport.TransportSmooth
import Submission.Obl.Entropy__smooth_gaussian_transport.BrenierThird

open MeasureTheory ProbabilityTheory Set

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_contDiff_infty {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ := by
  have hV2 := smooth_finite_order hV 2
  have hC2 := brenier_contDiff_two hm hV2 ha hH hφ hlaw
  have hC3 := brenier_contDiff_three hm hV2 ha hH hφ hlaw
  have hU : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun x : E m => Real.log (Submission.Lib.EntropyRemainder.gaussianDensity x)) :=
    Submission.Lib.EntropyRemainder.gaussianDensity_contDiff.log
      (fun x => (Submission.Lib.EntropyRemainder.gaussianDensity_pos x).ne')
  have hpos := fun x => (brenier_positive_hessian hm hV2 ha hH hφ hlaw x).1
  have heq := brenier_log_det_equation hm hV2 ha hH hφ hlaw
  apply transport_smooth_from_third_holder hC3 hU hV hpos heq
  apply transport_third_holder hC2 (smooth_finite_order hU 2) hV2 hpos heq
  intro K hK
  obtain ⟨α, C, hα, hα1, hC, hmod⟩ := brenier_hessian_compact_holder hm hV2 ha hH hφ hlaw hK
  obtain ⟨D, hD, hd⟩ := compact_hessian_holder_of_operator_holder hC2 hC.le hmod
  exact ⟨α, D, hα, hα1, hD, hd⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
