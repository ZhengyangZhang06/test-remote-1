import Submission.Obl.Entropy__smooth_gaussian_transport.StrictContact

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem dilate_mem_of_supporting_distance {m : ℕ} {K : Set (E m)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (h0 : (0 : E m) ∈ K)
    {x : E m} (hx : x ∈ K) {D κ ρ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hκρ : (1 - κ) * D ≤ ρ) (hKD : ∀ z ∈ K, ‖z‖ ≤ D)
    (hdist : ∀ e : E m, ‖e‖ = 1 → ∀ d : ℝ, 0 ≤ d →
      (∀ z ∈ K, inner ℝ e (z - x) ≤ d) → ρ < d) : κ⁻¹ • x ∈ K := by
  by_contra hout
  obtain ⟨f, t, hsep, htx⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hout
  have hfne : f ≠ 0 := by
    intro hf
    have h := (hsep 0 h0).trans htx
    simp only [hf, zero_apply, lt_self_iff_false] at h
  let v := (InnerProductSpace.toDual ℝ (E m)).symm f
  have hvapply (z : E m) : inner ℝ v z = f z := by
    change ((InnerProductSpace.toDual ℝ (E m)) v) z = f z
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hvne : v ≠ 0 := by
    intro hv
    apply hfne
    ext z
    simpa only [hv, inner_zero_left, zero_apply] using (hvapply z).symm
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvpos,
      inv_mul_cancel₀ hvpos.ne']
  have heapply (z : E m) : inner ℝ e z = ‖v‖⁻¹ * f z := by
    simp only [e, real_inner_smul_left, hvapply]
  obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn (f := fun z => inner ℝ e z)
    ⟨0, h0⟩ (continuous_const.inner continuous_id).continuousOn
  have hmaxx : inner ℝ e x ≤ inner ℝ e z₀ := hmax hx
  have hsupport : ∀ z ∈ K, inner ℝ e (z - x) ≤ inner ℝ e z₀ - inner ℝ e x := by
    intro z hz
    rw [inner_sub_right]
    exact sub_le_sub_right (hmax hz) _
  have hρd := hdist e he (inner ℝ e z₀ - inner ℝ e x) (sub_nonneg.mpr hmaxx) hsupport
  have hsep' : inner ℝ e z₀ < inner ℝ e (κ⁻¹ • x) := by
    rw [heapply, heapply]
    exact mul_lt_mul_of_pos_left ((hsep z₀ hz₀).trans htx) (inv_pos.mpr hvpos)
  rw [real_inner_smul_right] at hsep'
  have hsepk : κ * inner ℝ e z₀ < inner ℝ e x := by
    have h := mul_lt_mul_of_pos_left hsep' hκ
    simpa only [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] using h
  have hbound : inner ℝ e z₀ ≤ D := by
    have h := real_inner_le_norm e z₀
    rw [he, one_mul] at h
    exact h.trans (hKD z₀ hz₀)
  have hmul := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hκ1.le)
  nlinarith

/-- The contraction factor depends only on the dimension and density bounds,
so the same factor works for a family of normalized potentials. -/
theorem exists_uniform_section_contraction {m : ℕ} (hm : 1 ≤ m)
    {l U : ℝ} (hl : 0 < l) (hlU : l ≤ U) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ u : E m → ℝ,
      ConvexOn ℝ univ u → conjugateDomain u = univ →
      (∀ z, 0 ≤ u z) → u 0 = 0 →
      (∀ s : Set (E m), MeasurableSet s → s ⊆ {z | u z ≤ 1} →
        ENNReal.ofReal l * volume s ≤ alexandrovMeasure u s ∧
          alexandrovMeasure u s ≤ ENNReal.ofReal U * volume s) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∀ x : E m, u x ≤ h / 2 → u (κ⁻¹ • x) ≤ h := by
  let r : ℝ := 1 / ((m : ℝ) * (m + 1))
  let R : ℝ := (m : ℝ) + 1
  let c : E m := simplexCenter m
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨ρ, hρ, hdist⟩ := normalized_supporting_distance m hr hR (2 * U / l)
  let κ : ℝ := 1 - min ρ R / (2 * R)
  have hκ : 0 < κ := by
    have hq : min ρ R / (2 * R) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * R)).mpr
      nlinarith [min_le_right ρ R]
    dsimp only [κ]
    linarith
  have hκ1 : κ < 1 := by
    have hq : 0 < min ρ R / (2 * R) := div_pos (lt_min hρ hR) (by positivity)
    dsimp only [κ]
    linarith
  have hκρ : (1 - κ) * (2 * R) ≤ ρ := by
    dsimp only [κ]
    have heq : (1 - (1 - min ρ R / (2 * R))) * (2 * R) = min ρ R := by
      field_simp
      ring
    rw [heq]
    exact min_le_left _ _
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro u hu hdom hnonneg hzero hbound h hh hh1 x hx
  let K := {z | u z ≤ 1}
  let S₀ := {z | u z ≤ h}
  have hS₀ : IsCompact S₀ := isCompact_sublevel_of_finite_conjugate hu.locallyLipschitz.continuous hdom h
  have hS₀K : S₀ ⊆ K := fun _ hz => hz.trans hh1
  have h0 : (0 : E m) ∈ S₀ := by change u 0 ≤ h; rw [hzero]; exact hh.le
  have hxS : x ∈ S₀ := hx.trans (half_le_self hh.le)
  obtain ⟨L, hinner, houter⟩ := section_ball_normalization hm hu hdom 0 (r := h)
    (by rw [hzero]; exact hh)
  simp only [inner_zero_left, sub_zero] at hinner houter
  let S := L '' S₀
  have hS : IsCompact S := hS₀.image L.continuous
  have hSconv : Convex ℝ S := by
    have hc₀ : Convex ℝ S₀ := by
      simpa only [mem_univ, true_and] using hu.convex_le h
    exact hc₀.linear_image L.toLinearMap
  have h0S : (0 : E m) ∈ S := ⟨0, h0, L.map_zero⟩
  have hxS' : L x ∈ S := mem_image_of_mem L hxS
  have hsource : ∀ z ∈ S, L.symm z ∈ S₀ := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [L.symm_apply_apply] using hz
  let v := tilt u 0 h
  have hv : Continuous v := tilt_continuous hu.locallyLipschitz.continuous _ _
  have hvc : ConvexOn ℝ univ v := tilt_convex hu _ _
  have hvdom : conjugateDomain v = univ := tilt_conjugateDomain hdom _ _
  have hbv : ∀ s : Set (E m), MeasurableSet s → s ⊆ K →
      ENNReal.ofReal l * volume s ≤ alexandrovMeasure v s ∧
        alexandrovMeasure v s ≤ ENNReal.ofReal U * volume s := by
    intro s hs hsK
    simpa only [v, tilt_alexandrovMeasure hu.locallyLipschitz.continuous hdom] using hbound s hs hsK
  obtain ⟨a, ha, hab⟩ := exists_density_normalizing_scale hm hv hvdom L.symm hl hlU hbv
  let w : E m → ℝ := fun z => a * v (L.symm z)
  have hw : ConvexOn ℝ univ w := by
    convert! (hvc.comp_linearMap L.symm.toLinearMap).smul ha.le using 1
  have hwdom : conjugateDomain w = univ :=
    positiveScale_conjugateDomain (linearChange_conjugateDomain hvdom L.symm) ha
  have hSeq : S = {z | u (L.symm z) ≤ h} := by
    ext z
    constructor
    · exact hsource z
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
  have hnonpos : ∀ z ∈ S, w z ≤ 0 := by
    intro z hz
    have hz' : u (L.symm z) ≤ h := hsource z hz
    simpa only [w, v, tilt, inner_zero_left, sub_zero] using
      mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hz')
  have hboundary : ∀ z ∈ frontier S, 0 ≤ w z := by
    intro z hz
    rw [hSeq] at hz
    have heq : u (L.symm z) = h := frontier_le_subset_eq
      (hu.locallyLipschitz.continuous.comp L.symm.continuous) continuous_const hz
    simp only [w, v, tilt, inner_zero_left, sub_zero, heq, sub_self, mul_zero, le_refl]
  have hwMass : ∀ s : Set (E m), MeasurableSet s → s ⊆ S →
      (2 : ℝ≥0∞) * volume s ≤ alexandrovMeasure w s ∧
        alexandrovMeasure w s ≤ ENNReal.ofReal (2 * U / l) * volume s := by
    intro s hs hsS
    exact hab s hs (fun z hz => hS₀K (hsource z (hsS hz)))
  have hdepth : 2 * w (L x) ≤ w c := by
    have hnonneg' := hnonneg (L.symm c)
    simp only [w, v, tilt, inner_zero_left, sub_zero, L.symm_apply_apply]
    nlinarith
  have hnormS : ∀ z ∈ S, ‖z‖ ≤ 2 * R := by
    intro z hz
    have hz' : dist z c ≤ R := houter hz
    have h0' : dist (0 : E m) c ≤ R := houter h0S
    have ht := dist_triangle z c 0
    rw [dist_zero_right, dist_comm c 0] at ht
    linarith
  have hd : κ⁻¹ • L x ∈ S := dilate_mem_of_supporting_distance hS hSconv h0S hxS'
    hκ hκ1 hκρ hnormS (fun e he d hd hs =>
      hdist w hw hwdom S hS c hinner houter hnonpos hboundary hwMass
        (L x) e hxS' hdepth he d hd hs)
  have hz := hsource _ hd
  change u (L.symm (κ⁻¹ • L x)) ≤ h at hz
  simpa only [map_smul, L.symm_apply_apply] using hz

/-- For locally controlled Alexandrov densities, successive sections contract
by a fixed factor around their minimum. -/
theorem exists_section_contraction {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) (hnonneg : ∀ z, 0 ≤ u z) (hzero : u 0 = 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ x : E m, u x ≤ h / 2 → u (κ⁻¹ • x) ≤ h := by
  have hK : IsCompact {z | u z ≤ 1} :=
    isCompact_sublevel_of_finite_conjugate hu.locallyLipschitz.continuous hdom 1
  obtain ⟨l, U, hl, hlU, hb⟩ := hMA _ hK
  obtain ⟨κ, hκ, hκ1, hc⟩ := exists_uniform_section_contraction hm hl hlU
  exact ⟨κ, hκ, hκ1, hc u hu hdom hnonneg hzero hb⟩

theorem section_geometric_decay_of_contraction {m : ℕ} {u : E m → ℝ}
    {κ M : ℝ} (hκ : 0 < κ)
    (hc : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : E m, u x ≤ h / 2 → u (κ⁻¹ • x) ≤ h)
    (hM : ∀ x : E m, u x ≤ 1 → ‖x‖ ≤ M) :
    ∀ n : ℕ, ∀ x : E m, u x ≤ (1 / 2 : ℝ) ^ n → ‖x‖ ≤ κ ^ n * M := by
  have hiter : ∀ n : ℕ, ∀ x : E m,
      u x ≤ (1 / 2 : ℝ) ^ n → u ((κ⁻¹) ^ n • x) ≤ 1 := by
    intro n
    induction n with
    | zero => intro x hx; simpa only [pow_zero, one_smul] using hx
    | succ n ih =>
      intro x hx
      have hn : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
      have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hx' : u x ≤ (1 / 2 : ℝ) ^ n / 2 := by
        simpa only [pow_succ, div_eq_mul_inv, one_mul] using hx
      have hd := hc _ hn hn1 x hx'
      have hi := ih (κ⁻¹ • x) hd
      simpa only [pow_succ, mul_smul] using hi
  intro n x hx
  have hbound : ‖(κ⁻¹) ^ n • x‖ ≤ M := hM _ (hiter n x hx)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.mpr hκ) n)] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (pow_nonneg hκ.le n)
  simpa only [← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hκ.ne'), one_mul] using h

theorem exists_section_geometric_decay {m : ℕ} (hm : 1 ≤ m) {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hMA : LocalDensityBounds u) (hnonneg : ∀ z, 0 ≤ u z) (hzero : u 0 = 0) :
    ∃ κ M : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < M ∧ ∀ n : ℕ, ∀ x : E m,
      u x ≤ (1 / 2 : ℝ) ^ n → ‖x‖ ≤ κ ^ n * M := by
  obtain ⟨κ, hκ, hκ1, hcontract⟩ := exists_section_contraction hm hu hdom hMA hnonneg hzero
  obtain ⟨M₀, hM₀⟩ := (isCompact_sublevel_of_finite_conjugate
    hu.locallyLipschitz.continuous hdom 1).isBounded.exists_norm_le
  let M : ℝ := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hiter : ∀ n : ℕ, ∀ x : E m,
      u x ≤ (1 / 2 : ℝ) ^ n → u ((κ⁻¹) ^ n • x) ≤ 1 := by
    intro n
    induction n with
    | zero => intro x hx; simpa only [pow_zero, one_smul] using hx
    | succ n ih =>
      intro x hx
      have hn : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
      have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hx' : u x ≤ (1 / 2 : ℝ) ^ n / 2 := by
        simpa only [pow_succ, div_eq_mul_inv, one_mul] using hx
      have hd := hcontract _ hn hn1 x hx'
      have hi := ih (κ⁻¹ • x) hd
      simpa only [pow_succ, mul_smul] using hi
  refine ⟨κ, M, hκ, hκ1, hM, ?_⟩
  intro n x hx
  have hbound : ‖(κ⁻¹) ^ n • x‖ ≤ M := (hM₀ _ (hiter n x hx)).trans (le_max_right _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.mpr hκ) n)] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (pow_nonneg hκ.le n)
  simpa only [← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hκ.ne'), one_mul] using h

end Submission.Obl.Entropy__smooth_gaussian_transport
