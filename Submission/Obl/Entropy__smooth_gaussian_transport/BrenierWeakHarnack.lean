import Submission.Obl.Entropy__smooth_gaussian_transport.WeakHarnackPoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem operatorMatrix_id_posSemidef (m : ℕ) :
    (operatorMatrix (ContinuousLinearMap.id ℝ (E m))).PosSemidef := by
  apply operatorMatrix_posSemidef (fun _ _ => rfl)
  intro v
  exact real_inner_self_nonneg

theorem brenier_linearized_weakHarnack {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ u : E m → ℝ, ContDiff ℝ 1 u →
        (∃ L : NNReal, LipschitzWith L (gradient u)) →
        (∀ z ∈ Metric.closedBall (0 : E m) (m + 4), 0 ≤ u z) →
        (∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : E m) (m + 4) →
          linearizedTransport V φ u z ≤ 1) →
        HasWeakHarnackTail u Q θ := by
  obtain ⟨δ, Λ, M, hδ, hΛ, hM, hcoeff⟩ :=
    brenier_ae_linearized_bounds hm hV ha hH hφ hlaw
      (isCompact_closedBall (0 : E m) (m + 4))
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := exists_elliptic_weakHarnack hm hδ hΛ.le hM.le
  refine ⟨Q, θ, hQ, hθ, hθ1, ?_⟩
  intro u hu hLip hu0 hineq
  obtain ⟨L, hL⟩ := hLip
  apply hweak u L (fun z => fderiv ℝ (gradient φ) z)
    (fun z => gradient V (gradient φ z)) hu hL hu0 ?_ hineq
  filter_upwards [hcoeff] with z hc
  intro hz
  have hh := hc hz
  refine ⟨hh.1, fun B hB => (hh.2 B hB).1, ?_⟩
  exact (hh.2 _ (operatorMatrix_id_posSemidef m)).2.trans
    ((mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hΛ.le).trans_eq (mul_one Λ))

/-- Weak Harnack constants are uniform over the difference direction and
step size. The complement need only be nonnegative on the specified ball. -/
theorem brenier_local_complement_weakHarnack {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (h : E m), h ≠ 0 → ∀ M : ℝ,
        (∀ z ∈ Metric.closedBall (0 : E m) (m + 4), normalizedSecondDifference φ h z ≤ M) →
        HasWeakHarnackTail (fun z => M - normalizedSecondDifference φ h z) Q θ := by
  obtain ⟨Q, θ, hQ, hθ, hθ1, hweak⟩ := brenier_linearized_weakHarnack hm hV ha hH hφ hlaw
  refine ⟨Q, θ, hQ, hθ, hθ1, ?_⟩
  intro h hh M hlocal
  obtain ⟨hq, _, ⟨L, hL⟩, hqeq⟩ :=
    brenier_normalized_secondDifference_subsolution hm hV ha hH hφ hlaw hh
  have hc : ContDiff ℝ 1 (fun z => M - normalizedSecondDifference φ h z) := contDiff_const.sub hq
  apply hweak _ hc ?_ (fun z hz => sub_nonneg.mpr (hlocal z hz)) ?_
  · refine ⟨L, ?_⟩
    rw [funext (gradient_const_sub_of_differentiable hq.differentiable_one M)]
    exact hL.neg
  · filter_upwards [hqeq] with z hz
    intro _
    rw [linearizedTransport_const_sub V φ hq.differentiable_one hz.1]
    linarith [hz.2]

end Submission.Obl.Entropy__smooth_gaussian_transport
