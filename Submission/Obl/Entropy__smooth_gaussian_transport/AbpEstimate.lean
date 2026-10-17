import Submission.Obl.Entropy__smooth_gaussian_transport.ContactHessian
import Submission.Obl.Entropy__smooth_gaussian_transport.DeterminantBound
import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedEllipticity

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A contact-measure ABP estimate for a C¹ function with Lipschitz gradient
and an almost-everywhere linear elliptic inequality. Coefficients need not be
continuous. The constant in the determinant bound depends only on dimension. -/
theorem abp_contact_bound {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hdet : ∀ B : E m →L[ℝ] E m, |B.det| ≤ C * ‖B‖ ^ m)
    {u : E m → ℝ} (hu : ContDiff ℝ 1 u) {L : NNReal} (hLip : LipschitzWith L (gradient u))
    {K : Set (E m)} (hK : IsCompact K) (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {A : E m → E m →L[ℝ] E m} {b : E m → E m} {δ M F : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hcoeff : ∀ᵐ z ∂volume, z ∈ K →
      ‖b z‖ ≤ M ∧ ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (A z) B)
    (hineq : ∀ᵐ z ∂volume, z ∈ K →
      linearizedTrace (A z) (fderiv ℝ (gradient u) z) - inner ℝ (b z) (gradient u z) ≤ F)
    {x : E m} (hx : x ∈ K) {D r : ℝ} (hD : 0 < D)
    (hKD : K ⊆ Metric.closedBall x D) (hr : r ≤ -u x / D) :
    volume (Metric.ball (0 : E m) r) ≤
      ENNReal.ofReal (C * ((F + M * r) / δ) ^ m) * volume {z | z ∈ K ∧ u z < 0} := by
  let S : Set (E m) := {z | z ∈ lowerContactSet u K ∧ ‖gradient u z‖ < r}
  have hS : MeasurableSet S := (lowerContactSet_measurable hu K).inter
    ((isOpen_lt (continuous_gradient_of_contDiff_one hu).norm continuous_const).measurableSet)
  have hbound : ∀ᵐ z ∂volume.restrict S,
      |(fderiv ℝ (gradient u) z).det| ≤ C * ((F + M * r) / δ) ^ m := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hcoeff,
      ae_restrict_of_ae hineq, ae_restrict_of_ae (hLip.ae_differentiableAt (μ := volume))]
      with z hz hc hi hd
    have hzK : z ∈ K := interior_subset hz.1.1
    have hB := contact_hessian_posSemidef hu hz.1 hd
    have he := (hc hzK).2 _ hB
    have hb : inner ℝ (b z) (gradient u z) ≤ M * r := by
      calc
        _ ≤ ‖b z‖ * ‖gradient u z‖ := real_inner_le_norm _ _
        _ ≤ M * r := mul_le_mul (hc hzK).1 hz.2.le (norm_nonneg _) hM
    have hn : ‖fderiv ℝ (gradient u) z‖ ≤ (F + M * r) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hi' := hi hzK
      nlinarith
    exact (hdet _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hn m) hC)
  calc
    volume (Metric.ball (0 : E m) r) ≤
        ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ (gradient u) z).det| :=
      contact_jacobian_bound hu hLip hK hboundary hx hD hKD hr
    _ ≤ ∫⁻ _z in S, ENNReal.ofReal (C * ((F + M * r) / δ) ^ m) :=
      lintegral_mono_ae (hbound.mono (fun _ hz => ENNReal.ofReal_le_ofReal hz))
    _ = ENNReal.ofReal (C * ((F + M * r) / δ) ^ m) * volume S := by
      rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (C * ((F + M * r) / δ) ^ m) * volume {z | z ∈ K ∧ u z < 0} := by
      gcongr
      intro z hz
      exact ⟨interior_subset hz.1.1, hz.1.2.1⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
