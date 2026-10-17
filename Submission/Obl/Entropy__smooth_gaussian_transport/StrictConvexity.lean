import Submission.Obl.Entropy__smooth_gaussian_transport.StrictContact

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem zeroSet_subsingleton {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) (hnonneg : ∀ z, 0 ≤ u z) :
    ({z | u z = 0} : Set (E m)).Subsingleton := by
  intro x hx y hy
  change u x = 0 at hx
  change u y = 0 at hy
  by_contra hxy
  let e := y - x
  have hgap : inner ℝ e x < inner ℝ e y := by
    have hpos : 0 < inner ℝ e e := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    dsimp only [e] at hpos ⊢
    rw [inner_sub_right] at hpos
    linarith
  let Z := {z | u z ≤ 0}
  have hZ : IsCompact Z := by
    simpa only [inner_zero_left, sub_zero] using
      isCompact_tilted_sublevel_of_finite_conjugate hu.locallyLipschitz.continuous hdom 0 0
  have hxZ : x ∈ Z := hx.le
  have hyZ : y ∈ Z := hy.le
  obtain ⟨z₀, hz₀, hmax⟩ := hZ.exists_isMaxOn (f := fun z => inner ℝ e z) ⟨x, hxZ⟩
    (continuous_const.inner continuous_id).continuousOn
  have hz₀zero : u z₀ = 0 := le_antisymm hz₀ (hnonneg z₀)
  let v : E m → ℝ := fun z => u (z + z₀)
  have hv : ConvexOn ℝ univ v := translate_convex hu z₀
  have hvdom : conjugateDomain v = univ := translate_conjugateDomain hdom z₀
  have hvMA : LocalDensityBounds v :=
    localDensityBounds_translate hu.locallyLipschitz.continuous hdom hMA z₀
  have hvzero : v 0 = 0 := by simpa only [v, zero_add] using hz₀zero
  have hsupport : ∀ z, v z = 0 → inner ℝ e z ≤ 0 := by
    intro z hz
    have h : inner ℝ e (z + z₀) ≤ inner ℝ e z₀ := hmax (show z + z₀ ∈ Z from hz.le)
    rw [inner_add_right] at h
    linarith
  have hxzero : v (x - z₀) = 0 := by simpa only [v, sub_add_cancel] using hx
  have hxneg : inner ℝ e (x - z₀) < 0 := by
    have h : inner ℝ e y ≤ inner ℝ e z₀ := hmax hyZ
    rw [inner_sub_right]
    linarith
  exact zero_contact_no_negative_direction hm hv hvdom hvMA
    (fun z => hnonneg (z + z₀)) hvzero e hsupport (x - z₀) hxzero hxneg

/-- Positive locally bounded Alexandrov density and finite conjugate exclude
nontrivial contact sets throughout the full space. -/
theorem contactSet_subsingleton {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) (p : E m) : (contactSet u p).Subsingleton := by
  let v := tilt u p (-finiteConjugate u p)
  have hv : ConvexOn ℝ univ v := tilt_convex hu p _
  have hvdom : conjugateDomain v = univ := tilt_conjugateDomain hdom p _
  have hvMA : LocalDensityBounds v :=
    localDensityBounds_tilt hu.locallyLipschitz.continuous hdom hMA p _
  have hvnonneg : ∀ z, 0 ≤ v z := by
    intro z
    have h := fenchel_inequality hdom z p
    dsimp only [v, tilt]
    linarith
  have hsub := zeroSet_subsingleton hm hv hvdom hvMA hvnonneg
  intro x hx y hy
  apply hsub
  · have hx' := (show IsSubgradient u x p from hx).finiteConjugate_eq
    change v x = 0
    dsimp only [v, tilt]
    linarith
  · have hy' := (show IsSubgradient u y p from hy).finiteConjugate_eq
    change v y = 0
    dsimp only [v, tilt]
    linarith

theorem strictConvexOn_of_contactSet_subsingleton {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hcontact : ∀ p, (contactSet u p).Subsingleton) : StrictConvexOn ℝ univ u := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hle := hu.2 hx hy ha.le hb.le hab
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨p, hp⟩ := exists_subgradient hu hdom (a • x + b • y)
  let z := a • x + b • y
  have hpz : inner ℝ p z = a * inner ℝ p x + b * inner ℝ p y := by
    simp only [z, inner_add_right, real_inner_smul_right]
  have hpx := hp x
  have hpy := hp y
  rw [inner_sub_right] at hpx hpy
  change u z + (inner ℝ p x - inner ℝ p z) ≤ u x at hpx
  change u z + (inner ℝ p y - inner ℝ p z) ≤ u y at hpy
  change u z = a * u x + b * u y at heq
  have hconst : (a + b) * u z = u z := by rw [hab, one_mul]
  have hpconst : (a + b) * inner ℝ p z = inner ℝ p z := by rw [hab, one_mul]
  have hxplane : u z + inner ℝ p x - inner ℝ p z = u x := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hpy)]
  have hyplane : u z + inner ℝ p y - inner ℝ p z = u y := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hpx)]
  apply hxy
  apply hcontact p
  · intro t
    have ht := hp t
    rw [inner_sub_right] at ht ⊢
    linarith
  · intro t
    have ht := hp t
    rw [inner_sub_right] at ht ⊢
    linarith

theorem strictConvexOn_of_localDensityBounds {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) : StrictConvexOn ℝ univ u :=
  strictConvexOn_of_contactSet_subsingleton hu hdom (contactSet_subsingleton hm hu hdom hMA)

end Submission.Obl.Entropy__smooth_gaussian_transport
