import Submission.Obl.Entropy__smooth_gaussian_transport.SectionContraction

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def centeredPotential {m : ℕ} (u : E m → ℝ) (p q z : E m) : ℝ :=
  tilt (fun y => u (y + p)) q (u p) z

theorem centeredPotential_convex {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (p q : E m) : ConvexOn ℝ univ (centeredPotential u p q) :=
  tilt_convex (translate_convex hu p) q (u p)

theorem centeredPotential_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) (p q : E m) :
    conjugateDomain (centeredPotential u p q) = univ :=
  tilt_conjugateDomain (translate_conjugateDomain hdom p) q (u p)

theorem centeredPotential_nonneg {m : ℕ} {u : E m → ℝ} {p q : E m}
    (hp : IsSubgradient u p q) (z : E m) : 0 ≤ centeredPotential u p q z := by
  have h := hp (z + p)
  rw [add_sub_cancel_right] at h
  dsimp only [centeredPotential, tilt]
  linarith

theorem centeredPotential_zero {m : ℕ} (u : E m → ℝ) (p q : E m) :
    centeredPotential u p q 0 = 0 := by
  simp only [centeredPotential, tilt, zero_add, inner_zero_right, sub_zero, sub_self]

theorem centeredPotential_alexandrov {m : ℕ} {u : E m → ℝ}
    (hu : Continuous u) (hdom : conjugateDomain u = univ) (p q : E m)
    {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (centeredPotential u p q) s =
      alexandrovMeasure u ((fun z => z + p) '' s) := by
  change alexandrovMeasure (tilt (fun y => u (y + p)) q (u p)) s = _
  rw [tilt_alexandrovMeasure (u := fun y => u (y + p))
    (hu.comp (continuous_id.add continuous_const)) (translate_conjugateDomain hdom p) q (u p),
    translate_alexandrov hu hdom p hs]

theorem uniform_tilted_sublevel_bound {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) {R : ℝ} (hR : 0 ≤ R) (C : ℝ) :
    ∃ S : ℝ, 0 < S ∧ ∀ q y : E m, ‖q‖ ≤ R →
      u y - inner ℝ q y ≤ C → ‖y‖ ≤ S := by
  obtain ⟨B, hB⟩ := arbitrary_linear_minorant hdom (R := R + 1) (by positivity)
  refine ⟨max 1 (B + C), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q y hq hy
  have hi : inner ℝ q y ≤ R * ‖y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg y))
  have hn : ‖y‖ ≤ B + C := by nlinarith [hB y]
  exact hn.trans (le_max_right _ _)

/-- Compact families of centers and slopes have one bound for their unit sections
and one pair of Alexandrov density bounds on those sections. -/
theorem uniform_centered_section_bounds {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) {P Q : Set (E m)} (hP : IsCompact P) (hQ : IsCompact Q) :
    ∃ M l U : ℝ, 0 < M ∧ 0 < l ∧ l ≤ U ∧ ∀ p ∈ P, ∀ q ∈ Q,
      (∀ z : E m, centeredPotential u p q z ≤ 1 → ‖z‖ ≤ M) ∧
      (∀ s : Set (E m), MeasurableSet s → s ⊆ {z | centeredPotential u p q z ≤ 1} →
        ENNReal.ofReal l * volume s ≤ alexandrovMeasure (centeredPotential u p q) s ∧
          alexandrovMeasure (centeredPotential u p q) s ≤ ENNReal.ofReal U * volume s) := by
  obtain ⟨Rp, hRp, hbP⟩ := hP.isBounded.exists_pos_norm_le
  obtain ⟨Rq, hRq, hbQ⟩ := hQ.isBounded.exists_pos_norm_le
  obtain ⟨C, hC, hbC⟩ := (hP.image hu.locallyLipschitz.continuous).isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hbS⟩ := uniform_tilted_sublevel_bound hdom hRq.le (1 + C + Rq * Rp)
  let K := Metric.closedBall (0 : E m) S
  obtain ⟨l, U, hl, hlU, hbound⟩ := hMA K (isCompact_closedBall _ _)
  refine ⟨S + Rp, l, U, add_pos hS hRp, hl, hlU, ?_⟩
  intro p hp q hq
  have hsection : ∀ z : E m, centeredPotential u p q z ≤ 1 → z + p ∈ K := by
    intro z hz
    have hcp : u p ≤ C := (le_abs_self _).trans (hbC _ (mem_image_of_mem _ hp))
    have hip : -inner ℝ q p ≤ Rq * Rp := by
      calc
        -inner ℝ q p ≤ |inner ℝ q p| := neg_le_abs _
        _ ≤ ‖q‖ * ‖p‖ := abs_real_inner_le_norm _ _
        _ ≤ Rq * Rp := mul_le_mul (hbQ q hq) (hbP p hp) (norm_nonneg p) hRq.le
    have hv : u (z + p) - inner ℝ q (z + p) ≤ 1 + C + Rq * Rp := by
      change u (z + p) - inner ℝ q z - u p ≤ 1 at hz
      rw [inner_add_right]
      linarith
    change dist (z + p) 0 ≤ S
    rw [dist_zero_right]
    exact hbS q (z + p) (hbQ q hq) hv
  constructor
  · intro z hz
    have hzp : ‖z + p‖ ≤ S := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hsection z hz
    have hn := norm_sub_le (z + p) p
    rw [add_sub_cancel_right] at hn
    linarith [hbP p hp]
  · intro s hs hss
    have hs' : MeasurableSet ((fun z => z + p) '' s) :=
      (Homeomorph.addRight p).measurableEmbedding.measurableSet_image.mpr hs
    have hi : (fun z => z + p) '' s ⊆ K := by
      rintro _ ⟨z, hz, rfl⟩
      exact hsection z (hss hz)
    have hvol : volume ((fun z => z + p) '' s) = volume s := by
      rw [image_add_right, measure_preimage_add_right]
    rw [centeredPotential_alexandrov hu.locallyLipschitz.continuous hdom p q hs]
    simpa only [hvol] using hbound _ hs' hi

theorem uniform_centered_section_decay {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) {P Q : Set (E m)} (hP : IsCompact P) (hQ : IsCompact Q) :
    ∃ κ M : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < M ∧ ∀ p ∈ P, ∀ q ∈ Q,
      IsSubgradient u p q → ∀ n : ℕ, ∀ z : E m,
        centeredPotential u p q z ≤ (1 / 2 : ℝ) ^ n → ‖z‖ ≤ κ ^ n * M := by
  obtain ⟨M, l, U, hM, hl, hlU, hb⟩ := uniform_centered_section_bounds hu hdom hMA hP hQ
  obtain ⟨κ, hκ, hκ1, hc⟩ := exists_uniform_section_contraction hm hl hlU
  refine ⟨κ, M, hκ, hκ1, hM, ?_⟩
  intro p hp q hq hsub
  exact section_geometric_decay_of_contraction hκ
    (hc _ (centeredPotential_convex hu p q) (centeredPotential_conjugateDomain hdom p q)
      (centeredPotential_nonneg hsub) (centeredPotential_zero u p q) (hb p hp q hq).2)
    (hb p hp q hq).1

end Submission.Obl.Entropy__smooth_gaussian_transport
