import Submission.Obl.Entropy__smooth_gaussian_transport.Sections

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem subgradient_of_min_on_neighborhood {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) {K : Set (E m)} {x p : E m}
    (hx : K ∈ 𝓝 x) (hmin : IsMinOn (fun z => u z - inner ℝ p z) K x) :
    IsSubgradient u x p := by
  have hlocal : IsLocalMin (fun z => u z - inner ℝ p z) x := by
    filter_upwards [hx] with z hz
    exact hmin hz
  have hconv : ConvexOn ℝ univ (fun z => u z - inner ℝ p z) :=
    hu.sub ((InnerProductSpace.toDual ℝ (E m) p).toLinearMap.concaveOn convex_univ)
  intro z
  have h := IsMinOn.of_isLocalMin_of_convex_univ hlocal hconv z
  change u x - inner ℝ p x ≤ u z - inner ℝ p z at h
  rw [inner_sub_right]
  linarith

/-- Comparing boundary values reverses the inclusion of subgradient images over the
strict comparison set. -/
theorem subgradientImage_comparison {m : ℕ} {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x) :
    subgradientImage v {x | x ∈ K ∧ u x < v x} ⊆
      subgradientImage u {x | x ∈ K ∧ u x < v x} := by
  rintro p ⟨x, ⟨hxK, hx⟩, hxp⟩
  have hcont : Continuous (fun z => u z - inner ℝ p z) :=
    hu.locallyLipschitz.continuous.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hzK, hz⟩ := hK.exists_isMinOn ⟨x, hxK⟩ hcont.continuousOn
  have hzlt : u z - inner ℝ p z < v x - inner ℝ p x := by
    exact (hz hxK).trans_lt (sub_lt_sub_right hx _)
  have hv (w : E m) : v x - inner ℝ p x ≤ v w - inner ℝ p w := by
    have h := hxp w
    rw [inner_sub_right] at h
    linarith
  have hzuv : u z < v z := by linarith [hv z]
  have hzint : z ∈ interior K := by
    by_contra hn
    have hzf : z ∈ frontier K := ⟨subset_closure hzK, hn⟩
    exact (hboundary z hzf).not_gt hzuv
  refine ⟨z, ⟨hzK, hzuv⟩, ?_⟩
  exact subgradient_of_min_on_neighborhood hu (mem_interior_iff_mem_nhds.mp hzint) hz

theorem isOpen_strict_comparison_set {m : ℕ} {u v : E m → ℝ}
    (hu : Continuous u) (hv : Continuous v) {K : Set (E m)}
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x) :
    IsOpen {x | x ∈ K ∧ u x < v x} := by
  have heq : {x | x ∈ K ∧ u x < v x} = interior K ∩ {x | u x < v x} := by
    ext x
    constructor
    · rintro ⟨hxK, hx⟩
      refine ⟨?_, hx⟩
      by_contra hn
      exact (hboundary x ⟨subset_closure hxK, hn⟩).not_gt hx
    · exact fun ⟨hxK, hx⟩ => ⟨interior_subset hxK, hx⟩
  rw [heq]
  exact isOpen_interior.inter (isOpen_lt hu hv)

theorem alexandrov_comparison {m : ℕ} {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x) :
    alexandrovMeasure v {x | x ∈ K ∧ u x < v x} ≤
      alexandrovMeasure u {x | x ∈ K ∧ u x < v x} := by
  have hs := (isOpen_strict_comparison_set hu.locallyLipschitz.continuous
    hv.locallyLipschitz.continuous hboundary).measurableSet
  rw [alexandrovMeasure_apply hv.locallyLipschitz.continuous hdv hs,
    alexandrovMeasure_apply hu.locallyLipschitz.continuous hdu hs]
  exact measure_mono (subgradientImage_comparison hu hK hboundary)

/-- A strict inequality of Monge–Ampère masses enforces comparison throughout a compact region. -/
theorem comparison_of_strict_mass {m : ℕ} {u v : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (hdu : conjugateDomain u = univ) (hdv : conjugateDomain v = univ)
    {K : Set (E m)} (hK : IsCompact K)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x)
    (hmass : ∀ s : Set (E m), MeasurableSet s → s ⊆ K → 0 < volume s →
      alexandrovMeasure u s < alexandrovMeasure v s) :
    ∀ x ∈ K, v x ≤ u x := by
  intro x hxK
  by_contra hn
  have hx : u x < v x := lt_of_not_ge hn
  have hs := isOpen_strict_comparison_set hu.locallyLipschitz.continuous
    hv.locallyLipschitz.continuous hboundary
  have hpos : 0 < volume {z | z ∈ K ∧ u z < v z} := hs.measure_pos volume ⟨x, hxK, hx⟩
  exact (hmass _ hs.measurableSet (fun _ h => h.1) hpos).not_ge
    (alexandrov_comparison hu hv hdu hdv hK hboundary)

theorem supporting_point_of_boundary_gap {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) {K : Set (E m)} (hK : IsCompact K) {x p : E m}
    (hx : x ∈ K) (hgap : ∀ z ∈ frontier K, u x + inner ℝ p (z - x) < u z) :
    ∃ z ∈ interior K, IsSubgradient u z p ∧
      u z - inner ℝ p z ≤ u x - inner ℝ p x := by
  have hcont : Continuous (fun z => u z - inner ℝ p z) :=
    hu.locallyLipschitz.continuous.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hzK, hz⟩ := hK.exists_isMinOn ⟨x, hx⟩ hcont.continuousOn
  have hzint : z ∈ interior K := by
    by_contra hn
    have hg := hgap z ⟨subset_closure hzK, hn⟩
    have hmin := hz hx
    rw [inner_sub_right] at hg
    change u z - inner ℝ p z ≤ u x - inner ℝ p x at hmin
    linarith
  exact ⟨z, hzint,
    subgradient_of_min_on_neighborhood hu (mem_interior_iff_mem_nhds.mp hzint) hz, hz hx⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
