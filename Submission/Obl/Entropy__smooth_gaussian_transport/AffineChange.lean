import Submission.Obl.Entropy__smooth_gaussian_transport.LinearChange

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem translate_subgradient_iff {m : ℕ} (u : E m → ℝ) (b x p : E m) :
    IsSubgradient (fun z => u (z + b)) x p ↔ IsSubgradient u (x + b) p := by
  constructor
  · intro h z
    have hz := h (z - b)
    simpa only [sub_add_cancel, sub_sub, add_comm b x] using hz
  · intro h z
    have hz := h (z + b)
    simpa only [add_sub_add_right_eq_sub] using hz

theorem translate_subgradientImage {m : ℕ} (u : E m → ℝ) (b : E m) (s : Set (E m)) :
    subgradientImage (fun z => u (z + b)) s =
      subgradientImage u ((fun z => z + b) '' s) := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x + b, mem_image_of_mem _ hx, (translate_subgradient_iff u b x p).mp hp⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hp⟩
    exact ⟨x, hx, (translate_subgradient_iff u b x p).mpr hp⟩

theorem translate_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) (b : E m) :
    conjugateDomain (fun z => u (z + b)) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨M, hM⟩ := bounded_conjugate_values hdom q
  refine ⟨M - inner ℝ q b, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : inner ℝ q (x + b) - u (x + b) ≤ M := hM (mem_range_self (x + b))
  change inner ℝ q x - u (x + b) ≤ M - inner ℝ q b
  rw [inner_add_right] at hx
  linarith

theorem translate_alexandrov {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (b : E m) {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (fun z => u (z + b)) s =
      alexandrovMeasure u ((fun z => z + b) '' s) := by
  have hs' : MeasurableSet ((fun z => z + b) '' s) :=
    (Homeomorph.addRight b).measurableEmbedding.measurableSet_image.mpr hs
  rw [alexandrovMeasure_apply (φ := fun z => u (z + b))
    (hu.comp (continuous_id.add continuous_const))
    (translate_conjugateDomain hdom b) hs, translate_subgradientImage,
    alexandrovMeasure_apply hu hdom hs']

theorem positiveScale_subgradient_iff {m : ℕ} (u : E m → ℝ) {a : ℝ} (ha : 0 < a)
    (x p : E m) :
    IsSubgradient (fun z => a * u z) x (a • p) ↔ IsSubgradient u x p := by
  constructor <;> intro h z <;> have hz := h z
  · simp only [real_inner_smul_left, ← mul_add] at hz
    exact (mul_le_mul_iff_right₀ ha).mp hz
  · change a * u x + inner ℝ (a • p) (z - x) ≤ a * u z
    rw [real_inner_smul_left, ← mul_add]
    exact mul_le_mul_of_nonneg_left hz ha.le

theorem positiveScale_subgradientImage {m : ℕ} (u : E m → ℝ) {a : ℝ} (ha : 0 < a)
    (s : Set (E m)) :
    subgradientImage (fun z => a * u z) s = a • subgradientImage u s := by
  ext q
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨a⁻¹ • q, ⟨x, hx, ?_⟩, ?_⟩
    · apply (positiveScale_subgradient_iff u ha x _).mp
      simpa only [smul_inv_smul₀ ha.ne'] using hp
    · exact smul_inv_smul₀ ha.ne' q
  · rintro ⟨p, ⟨x, hx, hp⟩, rfl⟩
    exact ⟨x, hx, (positiveScale_subgradient_iff u ha x p).mpr hp⟩

theorem positiveScale_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) {a : ℝ} (ha : 0 < a) :
    conjugateDomain (fun z => a * u z) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨M, hM⟩ := bounded_conjugate_values hdom (a⁻¹ • q)
  refine ⟨a * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : inner ℝ (a⁻¹ • q) x - u x ≤ M := hM (mem_range_self x)
  have hx' := mul_le_mul_of_nonneg_left hx ha.le
  simpa only [real_inner_smul_left, mul_sub, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    using hx'

/-- Multiplying a convex potential by a positive constant scales its Alexandrov measure
by that constant to the power of the dimension. -/
theorem positiveScale_alexandrov {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) {a : ℝ} (ha : 0 < a)
    {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (fun z => a * u z) s = ENNReal.ofReal (a ^ m) * alexandrovMeasure u s := by
  rw [alexandrovMeasure_apply (φ := fun z => a * u z)
    (continuous_const.mul hu) (positiveScale_conjugateDomain hdom ha) hs,
    positiveScale_subgradientImage u ha, Measure.addHaar_smul_of_nonneg volume ha.le,
    alexandrovMeasure_apply hu hdom hs]
  simp only [E, finrank_euclideanSpace_fin]

/-- The full affine covariance formula used to normalize sections and their heights. -/
theorem affineChange_alexandrov {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m) (b p : E m) (r : ℝ)
    {a : ℝ} (ha : 0 < a) {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (fun x => a * (u (L x + b) - inner ℝ p x - r)) s =
      ENNReal.ofReal (a ^ m * |L.toLinearMap.det|) *
        alexandrovMeasure u ((fun x => L x + b) '' s) := by
  let v := (fun z => u (z + b)) ∘ L
  have hv : Continuous v := (hu.comp (continuous_id.add continuous_const)).comp L.continuous
  have hdv : conjugateDomain v = univ :=
    linearChange_conjugateDomain (translate_conjugateDomain hdom b) L
  change alexandrovMeasure (fun x => a * tilt v p r x) s = _
  rw [positiveScale_alexandrov (tilt_continuous hv p r) (tilt_conjugateDomain hdv p r) ha hs,
    tilt_alexandrovMeasure hv hdv p r]
  dsimp only [v]
  rw [linearChange_alexandrov (u := fun z => u (z + b))
    (hu.comp (continuous_id.add continuous_const))
      (translate_conjugateDomain hdom b) L hs]
  have hs' : MeasurableSet (L '' s) :=
    L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  rw [translate_alexandrov hu hdom b hs', ENNReal.ofReal_mul (pow_nonneg ha.le m), mul_assoc]
  congr 2
  rw [image_image]

end Submission.Obl.Entropy__smooth_gaussian_transport
