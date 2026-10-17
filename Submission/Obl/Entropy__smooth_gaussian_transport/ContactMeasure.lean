import Submission.Obl.Entropy__smooth_gaussian_transport.MaximumPrinciple
import Submission.Obl.Entropy__smooth_gaussian_transport.InverseDifferentiability
import Submission.Obl.Entropy__smooth_gaussian_transport.SecondOrderExpansion

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The area inequality for a Lipschitz map, with derivatives required only
almost everywhere. In particular, injectivity is not a premise. -/
theorem volume_image_le_jacobian_of_lipschitz {m : ℕ} {f : E m → E m} {L : NNReal}
    (hf : LipschitzWith L f) {s : Set (E m)} (hs : MeasurableSet s) :
    volume (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| := by
  let D : Set (E m) := {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hDae : ∀ᵐ x ∂volume, x ∈ D := hf.ae_differentiableAt (μ := volume)
  have hN : volume (f '' Dᶜ) = 0 := volume_image_zero_of_lipschitz hf (by
    exact ae_iff.mp hDae)
  have he : (s ∩ D : Set (E m)) =ᵐ[volume] s := by
    filter_upwards [hDae] with x hx
    exact propext ⟨And.left, fun hs => ⟨hs, hx⟩⟩
  calc
    volume (f '' s) ≤ volume (f '' (s ∩ D) ∪ f '' Dᶜ) := by
      apply measure_mono
      rintro _ ⟨x, hx, rfl⟩
      by_cases hd : x ∈ D
      · exact Or.inl ⟨x, ⟨hx, hd⟩, rfl⟩
      · exact Or.inr ⟨x, hd, rfl⟩
    _ ≤ volume (f '' (s ∩ D)) + volume (f '' Dᶜ) := measure_union_le _ _
    _ = volume (f '' (s ∩ D)) := by rw [hN, add_zero]
    _ ≤ ∫⁻ x in s ∩ D, ENNReal.ofReal |(fderiv ℝ f x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume (hs.inter hD)
        (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt)
    _ = _ := by rw [Measure.restrict_congr_set he]

/-- Interior negative points with a supporting tangent plane over the region.
The function itself need not be convex. -/
def lowerContactSet {m : ℕ} (u : E m → ℝ) (K : Set (E m)) : Set (E m) :=
  {x | x ∈ interior K ∧ u x < 0 ∧
    ∀ y ∈ K, u x + inner ℝ (gradient u x) (y - x) ≤ u y}

theorem lowerContactSet_measurable {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) (K : Set (E m)) : MeasurableSet (lowerContactSet u K) := by
  have hg := continuous_gradient_of_contDiff_one hu
  have hc : IsClosed {x : E m | ∀ y ∈ K, u x + inner ℝ (gradient u x) (y - x) ≤ u y} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    exact isClosed_le (hu.continuous.add (hg.inner (continuous_const.sub continuous_id))) continuous_const
  exact isOpen_interior.measurableSet.inter
    ((isOpen_lt hu.continuous continuous_const).measurableSet.inter hc.measurableSet)

theorem strictPolar_subset_contact_gradient_image {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : E m} (hx : x ∈ K) :
    strictPolar K x (-u x) ⊆ gradient u '' lowerContactSet u K := by
  intro p hp
  have hcont : Continuous (fun z => u z - inner ℝ p z) :=
    hu.continuous.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hcont.continuousOn
  have hzneg : u z < 0 := by
    have h₁ := hp z hzK
    have h₂ := hzmin hx
    change u z - inner ℝ p z ≤ u x - inner ℝ p x at h₂
    rw [inner_sub_right] at h₁
    linarith
  have hzint : z ∈ interior K := by
    by_contra hn
    exact (hboundary z ⟨subset_closure hzK, hn⟩).not_gt hzneg
  have hlocal : IsLocalMin (fun y => u y - inner ℝ p y) z := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with y hy
    exact hzmin hy
  have hgrad : gradient u z = p := by
    have hzero := hlocal.hasFDerivAt_eq_zero
      ((hu.differentiable_one z).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt)
    apply (InnerProductSpace.toDual ℝ (E m)).injective
    rw [toDual_gradient]
    exact sub_eq_zero.mp hzero
  refine ⟨z, ⟨hzint, hzneg, ?_⟩, hgrad⟩
  intro y hy
  have hm := hzmin hy
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at hm
  rw [hgrad, inner_sub_right]
  linarith

/-- The geometric part of the ABP estimate: slopes in a ball are covered by
gradients at negative supporting contact points with correspondingly small
gradient. The Jacobian then bounds the volume of that ball. -/
theorem contact_jacobian_bound {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : NNReal} (hLip : LipschitzWith L (gradient u))
    {K : Set (E m)} (hK : IsCompact K) (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {x : E m} (hx : x ∈ K) {D r : ℝ} (hD : 0 < D)
    (hKD : K ⊆ Metric.closedBall x D) (hr : r ≤ -u x / D) :
    volume (Metric.ball (0 : E m) r) ≤
      ∫⁻ z in {z | z ∈ lowerContactSet u K ∧ ‖gradient u z‖ < r},
        ENNReal.ofReal |(fderiv ℝ (gradient u) z).det| := by
  have hsub : Metric.ball (0 : E m) r ⊆
      gradient u '' {z | z ∈ lowerContactSet u K ∧ ‖gradient u z‖ < r} := by
    intro p hp
    have hpPolar := ball_subset_strictPolar hD hKD (Metric.ball_subset_ball hr hp)
    obtain ⟨z, hz, hzp⟩ := strictPolar_subset_contact_gradient_image hu hK hboundary hx hpPolar
    refine ⟨z, ⟨hz, ?_⟩, hzp⟩
    rw [hzp]
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  have hs : MeasurableSet {z | z ∈ lowerContactSet u K ∧ ‖gradient u z‖ < r} :=
    (lowerContactSet_measurable hu K).inter
      ((isOpen_lt (continuous_gradient_of_contDiff_one hu).norm continuous_const).measurableSet)
  exact (measure_mono hsub).trans (volume_image_le_jacobian_of_lipschitz hLip hs)

end Submission.Obl.Entropy__smooth_gaussian_transport
