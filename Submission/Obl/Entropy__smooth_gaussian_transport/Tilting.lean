import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticBarrier

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def tilt {m : ℕ} (u : E m → ℝ) (p : E m) (r : ℝ) (x : E m) : ℝ :=
  u x - inner ℝ p x - r

theorem tilt_continuous {m : ℕ} {u : E m → ℝ} (hu : Continuous u) (p : E m) (r : ℝ) :
    Continuous (tilt u p r) :=
  (hu.sub (continuous_const.inner continuous_id)).sub continuous_const

theorem tilt_convex {m : ℕ} {u : E m → ℝ} (hu : ConvexOn ℝ univ u) (p : E m) (r : ℝ) :
    ConvexOn ℝ univ (tilt u p r) :=
  (hu.sub ((InnerProductSpace.toDual ℝ (E m) p).toLinearMap.concaveOn
    convex_univ)).sub (concaveOn_const r convex_univ)

theorem tilt_subgradient_iff {m : ℕ} {u : E m → ℝ} (p : E m) (r : ℝ) (x q : E m) :
    IsSubgradient (tilt u p r) x q ↔ IsSubgradient u x (q + p) := by
  constructor <;> intro h z <;> have hz := h z
  · simp only [tilt, inner_sub_right] at hz
    simp only [inner_add_left, inner_sub_right]
    linarith
  · simp only [inner_add_left, inner_sub_right] at hz
    simp only [tilt, inner_sub_right]
    linarith

theorem tilt_subgradientImage {m : ℕ} (u : E m → ℝ) (p : E m) (r : ℝ) (s : Set (E m)) :
    subgradientImage (tilt u p r) s = (fun q => q + p) ⁻¹' subgradientImage u s := by
  ext q
  simp only [subgradientImage, mem_ofPred_eq, mem_preimage, tilt_subgradient_iff]

theorem tilt_conjugateDomain {m : ℕ} {u : E m → ℝ} (hdom : conjugateDomain u = univ)
    (p : E m) (r : ℝ) : conjugateDomain (tilt u p r) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨M, hM⟩ := bounded_conjugate_values hdom (q + p)
  refine ⟨M + r, ?_⟩
  rintro t ⟨x, rfl⟩
  have h := hM (mem_range_self x)
  change inner ℝ q x - (u x - inner ℝ p x - r) ≤ M + r
  change inner ℝ (q + p) x - u x ≤ M at h
  rw [inner_add_left] at h
  linarith

/-- Subtracting an affine function preserves the Alexandrov measure. -/
theorem tilt_alexandrovMeasure {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (p : E m) (r : ℝ) :
    alexandrovMeasure (tilt u p r) = alexandrovMeasure u := by
  ext s hs
  rw [alexandrovMeasure_apply (tilt_continuous hu p r) (tilt_conjugateDomain hdom p r) hs,
    alexandrovMeasure_apply hu hdom hs, tilt_subgradientImage,
    measure_preimage_add_right]

/-- The polar maximum principle applies to every compact section of a coercive convex potential. -/
theorem section_polar_bound {m : ℕ} {u : E m → ℝ} (hu : ConvexOn ℝ univ u)
    (hdom : conjugateDomain u = univ) (p : E m) (r : ℝ) {x : E m}
    (hx : u x - inner ℝ p x ≤ r) :
    volume (strictPolar {z | u z - inner ℝ p z ≤ r} x (r - (u x - inner ℝ p x))) ≤
      alexandrovMeasure u {z | u z - inner ℝ p z ≤ r} := by
  let K : Set (E m) := {z | u z - inner ℝ p z ≤ r}
  have hK := isCompact_tilted_sublevel_of_finite_conjugate hu.locallyLipschitz.continuous hdom p r
  have hc : Continuous (fun z => u z - inner ℝ p z) :=
    hu.locallyLipschitz.continuous.sub (continuous_const.inner continuous_id)
  have hb : ∀ z ∈ frontier K, 0 ≤ tilt u p r z := by
    intro z hz
    have he : u z - inner ℝ p z = r := frontier_le_subset_eq hc continuous_const hz
    simp only [tilt, he, sub_self, le_refl]
  have h := (alexandrov_polar_bound (tilt_convex hu p r) (tilt_conjugateDomain hdom p r)
    hK hb hx).trans (measure_mono (fun z hz => hz.1))
  rw [tilt_alexandrovMeasure hu.locallyLipschitz.continuous hdom p r] at h
  convert! h using 1
  congr 2
  simp only [tilt]
  ring

end Submission.Obl.Entropy__smooth_gaussian_transport
