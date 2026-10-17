import Submission.Obl.Entropy__smooth_gaussian_transport.DensityNormalization
import Submission.Obl.Entropy__smooth_gaussian_transport.SmallSections

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A supporting hyperplane of a compact zero set cannot separate two of its
points when the Alexandrov density is locally bounded above and below. -/
theorem zero_contact_no_negative_direction {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ) (hMA : LocalDensityBounds u)
    (hnonneg : ∀ z, 0 ≤ u z) (hzero : u 0 = 0) (e : E m)
    (hsupport : ∀ z, u z = 0 → inner ℝ e z ≤ 0)
    (y : E m) (hy : u y = 0) (hyneg : inner ℝ e y < 0) : False := by
  let δ : ℝ := -2 * inner ℝ e y
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let K := smallSection u e δ 1
  have hK : IsCompact K := smallSection_isCompact hu.locallyLipschitz.continuous hdom e δ 1
  obtain ⟨l, U, hl, hlU, hbound⟩ := hMA K hK
  let r : ℝ := 1 / ((m : ℝ) * (m + 1))
  let R : ℝ := (m : ℝ) + 1
  let c : E m := simplexCenter m
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨ρ, hρ, hdist⟩ := normalized_supporting_distance m hr hR (2 * U / l)
  let η : ℝ := min δ (ρ * (-inner ℝ e y) / (2 * R))
  have hη : 0 < η := lt_min hδ
    (div_pos (mul_pos hρ (neg_pos.mpr hyneg)) (mul_pos (by norm_num) hR))
  obtain ⟨ε₀, hε₀, hε₀1, hsmall⟩ := smallSection_support_bound
    hu.locallyLipschitz.continuous hdom hnonneg hzero e hsupport hδ hη
  let ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hεsmall : ε < ε₀ := half_lt_self hε₀
  have hε1 : ε ≤ 1 := hεsmall.le.trans hε₀1
  let S₀ := smallSection u e δ ε
  have hS₀K : S₀ ⊆ K := smallSection_subset_fixed hnonneg e δ hε hε1
  have hS₀ : IsCompact S₀ := smallSection_isCompact hu.locallyLipschitz.continuous hdom e δ ε
  have h0 : (0 : E m) ∈ S₀ := by
    change u 0 ≤ ε * (δ + inner ℝ e 0)
    simp only [hzero, inner_zero_right, add_zero]
    positivity
  have hyS : y ∈ S₀ := by
    change u y ≤ ε * (δ + inner ℝ e y)
    rw [hy]
    dsimp [δ]
    nlinarith
  have hsup : ∀ z ∈ S₀, inner ℝ e z ≤ η := hsmall ε hε hεsmall
  obtain ⟨L, hinner, houter⟩ := section_ball_normalization hm hu hdom (ε • e)
    (r := ε * δ) (by rw [hzero]; positivity)
  rw [← smallSection_eq_sublevel u e δ ε] at hinner houter
  let S := L '' S₀
  have hS : IsCompact S := hS₀.image L.continuous
  have h0S : (0 : E m) ∈ S := ⟨0, h0, L.map_zero⟩
  have hyS' : L y ∈ S := mem_image_of_mem L hyS
  let v := L.symm.toContinuousLinearMap.adjoint e
  have hqv (z : E m) : inner ℝ v z = inner ℝ e (L.symm z) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  have hyNorm : ‖L y‖ ≤ 2 * R := by
    have hyo : dist (L y) c ≤ R := houter hyS'
    have hzo : dist (0 : E m) c ≤ R := houter h0S
    have htri := dist_triangle (L y) c 0
    rw [dist_zero_right, dist_comm c 0] at htri
    linarith
  have hqnorm : -inner ℝ e y ≤ ‖v‖ * (2 * R) := by
    have h := neg_le_abs (inner ℝ v (L y))
    have hi := abs_real_inner_le_norm v (L y)
    have hm' := mul_le_mul_of_nonneg_left hyNorm (norm_nonneg v)
    rw [hqv, L.symm_apply_apply] at h hi
    linarith
  have hvpos : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  have hηnorm : η ≤ ρ * ‖v‖ := by
    have hη' := min_le_right δ (ρ * (-inner ℝ e y) / (2 * R))
    have hmul := mul_le_mul_of_nonneg_left hqnorm hρ.le
    dsimp only [η]
    apply hη'.trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * R)).mpr
    nlinarith
  let uε := tilt u (ε • e) (ε * δ)
  have huc : Continuous uε := tilt_continuous hu.locallyLipschitz.continuous _ _
  have hucv : ConvexOn ℝ univ uε := tilt_convex hu _ _
  have hudom : conjugateDomain uε = univ := tilt_conjugateDomain hdom _ _
  have hbε : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure uε s ∧
        alexandrovMeasure uε s ≤ ENNReal.ofReal U * volume s := by
    intro s hs hsK
    simpa only [uε, tilt_alexandrovMeasure hu.locallyLipschitz.continuous hdom] using hbound s hs hsK
  obtain ⟨a, ha, hab⟩ := exists_density_normalizing_scale hm huc hudom L.symm hl hlU hbε
  let w : E m → ℝ := fun z => a * uε (L.symm z)
  have hw : ConvexOn ℝ univ w := by
    convert! (hucv.comp_linearMap L.symm.toLinearMap).smul ha.le using 1
  have hwdom : conjugateDomain w = univ :=
    positiveScale_conjugateDomain (linearChange_conjugateDomain hudom L.symm) ha
  have hsource : ∀ z ∈ S, L.symm z ∈ S₀ := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [L.symm_apply_apply] using hz
  have hSeq : S = {z | uε (L.symm z) ≤ 0} := by
    ext z
    have heq : uε (L.symm z) ≤ 0 ↔ L.symm z ∈ S₀ := by
      simp only [uε, tilt, S₀, smallSection, mem_ofPred_eq, real_inner_smul_left]
      constructor <;> intro h <;> nlinarith
    change z ∈ S ↔ uε (L.symm z) ≤ 0
    rw [heq]
    constructor
    · exact hsource z
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
  have hnonpos : ∀ z ∈ S, w z ≤ 0 := by
    intro z hz
    have hz' : uε (L.symm z) ≤ 0 := by
      change z ∈ {z | uε (L.symm z) ≤ 0}
      rwa [← hSeq]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hz'
  have hboundary : ∀ z ∈ frontier S, 0 ≤ w z := by
    intro z hz
    rw [hSeq] at hz
    have heq : uε (L.symm z) = 0 :=
      frontier_le_subset_eq (huc.comp L.symm.continuous) continuous_const hz
    change 0 ≤ a * uε (L.symm z)
    rw [heq, mul_zero]
  have hwMass : ∀ s : Set (E m), MeasurableSet s → s ⊆ S →
      (2 : ℝ≥0∞) * volume s ≤ alexandrovMeasure w s ∧
        alexandrovMeasure w s ≤ ENNReal.ofReal (2 * U / l) * volume s := by
    intro s hs hsS
    exact hab s hs (fun z hz => hS₀K (hsource z (hsS hz)))
  have hcS : c ∈ S := hinner (Metric.mem_closedBall_self hr.le)
  have hcenter : 2 * uε 0 ≤ uε (L.symm c) := by
    have hq := hsup (L.symm c) (hsource c hcS)
    have hqδ : inner ℝ e (L.symm c) ≤ δ := hq.trans (min_le_left _ _)
    have hn := hnonneg (L.symm c)
    dsimp only [uε, tilt]
    simp only [hzero, inner_zero_right, zero_sub, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hqδ hε.le]
  have hwcenter : 2 * w 0 ≤ w c := by
    have h := mul_le_mul_of_nonneg_left hcenter ha.le
    simpa only [w, map_zero, mul_assoc, mul_left_comm] using h
  let e' : E m := ‖v‖⁻¹ • v
  have he' : ‖e'‖ = 1 := by
    simp only [e', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvpos,
      inv_mul_cancel₀ hvpos.ne']
  have hsupport' : ∀ z ∈ S, inner ℝ e' (z - 0) ≤ η / ‖v‖ := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left (hsup _ (hsource z hz)) (inv_nonneg.mpr hvpos.le)
    simpa only [e', sub_zero, real_inner_smul_left, hqv, div_eq_mul_inv, mul_comm] using h
  have hfar := hdist w hw hwdom S hS c hinner houter hnonpos hboundary hwMass
    0 e' h0S hwcenter he' (η / ‖v‖) (div_nonneg hη.le hvpos.le) hsupport'
  exact (not_lt_of_ge ((div_le_iff₀ hvpos).mpr hηnorm)) hfar

end Submission.Obl.Entropy__smooth_gaussian_transport
