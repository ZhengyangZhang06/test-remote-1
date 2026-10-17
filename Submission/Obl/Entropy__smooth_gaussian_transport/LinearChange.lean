import Submission.Obl.Entropy__smooth_gaussian_transport.Tilting

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem adjoint_symm_cancel {m : ℕ} (L : E m ≃L[ℝ] E m) (p : E m) :
    L.toContinuousLinearMap.adjoint (L.symm.toContinuousLinearMap.adjoint p) = p := by
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp

theorem linearChange_subgradient_iff {m : ℕ} (u : E m → ℝ)
    (L : E m ≃L[ℝ] E m) (x p : E m) :
    IsSubgradient (u ∘ L) x (L.toContinuousLinearMap.adjoint p) ↔
      IsSubgradient u (L x) p := by
  constructor
  · intro h z
    have hz := h (L.symm z)
    simpa only [Function.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, map_sub, L.apply_symm_apply] using hz
  · intro h z
    have hz := h (L z)
    simpa only [Function.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, map_sub] using hz

theorem linearChange_subgradientImage {m : ℕ} (u : E m → ℝ)
    (L : E m ≃L[ℝ] E m) (s : Set (E m)) :
    subgradientImage (u ∘ L) s =
      L.toContinuousLinearMap.adjoint '' subgradientImage u (L '' s) := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨L.symm.toContinuousLinearMap.adjoint q, ?_, adjoint_symm_cancel L q⟩
    refine ⟨L x, mem_image_of_mem L hx, ?_⟩
    apply (linearChange_subgradient_iff u L x _).mp
    simpa only [adjoint_symm_cancel] using hq
  · rintro ⟨p, ⟨_, ⟨x, hx, rfl⟩, hp⟩, rfl⟩
    exact ⟨x, hx, (linearChange_subgradient_iff u L x p).mpr hp⟩

theorem linearChange_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m) :
    conjugateDomain (u ∘ L) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨M, hM⟩ := bounded_conjugate_values hdom (L.symm.toContinuousLinearMap.adjoint q)
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := hM (mem_range_self (L x))
  simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe,
    L.symm_apply_apply, Function.comp_apply] using hx

theorem det_adjoint {m : ℕ} (L : E m →L[ℝ] E m) :
    L.adjoint.toLinearMap.det = L.toLinearMap.det := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    ← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.toMatrix_adjoint]
  simp

/-- The Alexandrov measure gains one determinant when the argument is changed linearly. -/
theorem linearChange_alexandrov {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m)
    {s : Set (E m)} (hs : MeasurableSet s) :
    alexandrovMeasure (u ∘ L) s =
      ENNReal.ofReal |L.toLinearMap.det| * alexandrovMeasure u (L '' s) := by
  have hs' : MeasurableSet (L '' s) :=
    L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  rw [alexandrovMeasure_apply (hu.comp L.continuous) (linearChange_conjugateDomain hdom L) hs,
    linearChange_subgradientImage, Measure.addHaar_image_continuousLinearMap, det_adjoint,
    alexandrovMeasure_apply hu hdom hs']
  rfl

/-- Pointwise density bounds gain two determinants, including the volume change. -/
theorem linearChange_mass_bounds {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (L : E m ≃L[ℝ] E m)
    {K : Set (E m)} {l r : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hb : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s ∧
        alexandrovMeasure u s ≤ ENNReal.ofReal r * volume s)
    {s : Set (E m)} (hs : MeasurableSet s) (hsK : s ⊆ L ⁻¹' K) :
    ENNReal.ofReal (l * |L.toLinearMap.det| ^ 2) * volume s ≤
        alexandrovMeasure (u ∘ L) s ∧
      alexandrovMeasure (u ∘ L) s ≤
        ENNReal.ofReal (r * |L.toLinearMap.det| ^ 2) * volume s := by
  have hs' : MeasurableSet (L '' s) :=
    L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  obtain ⟨hlo, hhi⟩ := hb (L '' s) hs' (image_subset_iff.mpr hsK)
  rw [linearChange_alexandrov hu hdom L hs]
  rw [Measure.addHaar_image_continuousLinearEquiv volume] at hlo hhi
  constructor
  · convert! mul_le_mul_right hlo (ENNReal.ofReal |L.toLinearMap.det|) using 1
    simp only [ENNReal.ofReal_mul hl,
      ENNReal.ofReal_pow (abs_nonneg L.toLinearMap.det)]
    ring
  · convert! mul_le_mul_right hhi (ENNReal.ofReal |L.toLinearMap.det|) using 1
    simp only [ENNReal.ofReal_mul hr,
      ENNReal.ofReal_pow (abs_nonneg L.toLinearMap.det)]
    ring

end Submission.Obl.Entropy__smooth_gaussian_transport
