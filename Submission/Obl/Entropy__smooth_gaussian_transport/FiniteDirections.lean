import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedEllipticity

open Set Filter
open scoped Topology RealInnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem isClosed_symmetric_operators {m : ℕ} :
    IsClosed {B : E m →L[ℝ] E m | B.toLinearMap.IsSymmetric} := by
  change IsClosed {B : E m →L[ℝ] E m | ∀ v w, inner ℝ (B v) w = inner ℝ v (B w)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- A nonzero symmetric increment with nonnegative elliptic trace has a
strictly positive quadratic direction. -/
theorem exists_positive_direction_of_trace_nonneg {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : B.toLinearMap.IsSymmetric)
    (hB0 : B ≠ 0) (htrace : 0 ≤ linearizedTrace A B) :
    ∃ v : E m, ‖v‖ = 1 ∧ 0 < inner ℝ (B v) v := by
  have hex : ∃ w : E m, 0 < inner ℝ (B w) w := by
    by_contra hn
    push Not at hn
    have hneg : (operatorMatrix ((-1 : ℝ) • B)).PosSemidef := by
      apply operatorMatrix_posSemidef (LinearMap.IsSymmetric.smul (by rfl) hB)
      intro v
      simpa only [smul_apply, real_inner_smul_left, neg_one_mul] using neg_nonneg.mpr (hn v)
    have hne : (-1 : ℝ) • B ≠ 0 := by
      intro he
      apply hB0
      have hn := congrArg norm he
      rw [norm_smul] at hn
      norm_num at hn
      exact hn
    have hh := linearizedTrace_pos hA hneg hne
    rw [linearizedTrace_smul] at hh
    linarith
  obtain ⟨w, hw⟩ := hex
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hwn.ne'
  · simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr hwn) (mul_pos (inv_pos.mpr hwn) hw)

/-- A compact family of elliptic traces admits a single finite collection
of unit directions that controls every symmetric increment of nonnegative
trace. The constants are uniform in the base Hessian. -/
theorem finite_directions_trace_control {m : ℕ} {S : Set (E m →L[ℝ] E m)}
    (hS : IsCompact S) (hpos : ∀ A ∈ S, (operatorMatrix A).PosDef) :
    ∃ F : Finset (E m), (∀ v ∈ F, ‖v‖ = 1) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ A ∈ S, ∀ B : E m →L[ℝ] E m, B.toLinearMap.IsSymmetric →
        0 ≤ linearizedTrace A B →
        ‖B‖ ≤ C * ∑ v ∈ F, max 0 (inner ℝ (B v) v) := by
  classical
  let T : Set (E m →L[ℝ] E m) := {B | ‖B‖ = 1 ∧ B.toLinearMap.IsSymmetric}
  have hT : IsCompact T := by
    convert! (isCompact_sphere (0 : E m →L[ℝ] E m) 1).inter_right
      isClosed_symmetric_operators using 1
    ext B
    simp only [T, Metric.mem_sphere, dist_zero_right, mem_inter_iff, mem_ofPred_eq]
  let trace : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) → ℝ :=
    fun z => linearizedTrace z.1 z.2
  have htrace : ContinuousOn trace (S ×ˢ T) := fun z hz =>
    (linearizedTrace_continuousAt (by
      simpa only [operatorMatrix_det] using (hpos z.1 hz.1).det_pos.ne')).continuousWithinAt
  let K := (S ×ˢ T) ∩ trace ⁻¹' Ici 0
  have hK : IsCompact K := (hS.prod hT).of_isClosed_subset
    (htrace.preimage_isClosed_of_isClosed (hS.prod hT).isClosed isClosed_Ici) inter_subset_left
  let U (v : {v : E m // ‖v‖ = 1}) : Set ((E m →L[ℝ] E m) × (E m →L[ℝ] E m)) :=
    {z | 0 < inner ℝ (z.2 v.1) v.1}
  have hU (v : {v : E m // ‖v‖ = 1}) : IsOpen (U v) :=
    isOpen_lt continuous_const (by fun_prop)
  have hcover : K ⊆ ⋃ v, U v := by
    intro z hz
    have hB0 : z.2 ≠ 0 := by
      intro he
      have hn := hz.1.2.1
      rw [he, norm_zero] at hn
      norm_num at hn
    obtain ⟨v, hv, hvpos⟩ := exists_positive_direction_of_trace_nonneg
      (hpos z.1 hz.1.1) hz.1.2.2 hB0 hz.2
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hvpos⟩
  obtain ⟨G, hG⟩ := hK.elim_finite_subcover U hU hcover
  let F : Finset (E m) := G.image Subtype.val
  have hF (v : E m) (hv : v ∈ F) : ‖v‖ = 1 := by
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  let q : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) → ℝ :=
    fun z => ∑ v ∈ F, max 0 (inner ℝ (z.2 v) v)
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hqpos (z) (hz : z ∈ K) : 0 < q z := by
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hG hz)
    apply Finset.sum_pos' (fun _ _ => le_max_left _ _)
    exact ⟨w.1, Finset.mem_image.mpr ⟨w, hw, rfl⟩, lt_of_lt_of_le hzw (le_max_right _ _)⟩
  obtain ⟨κ, hκ, hbound⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ K, κ ≤ q z := by
    by_cases hne : K.Nonempty
    · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hq.continuousOn
      exact ⟨q z, hqpos z hz, fun w hw => hmin hw⟩
    · exact ⟨1, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  refine ⟨F, hF, κ⁻¹, inv_pos.mpr hκ, ?_⟩
  intro A hA B hB htr
  by_cases hB0 : B = 0
  · simp [hB0]
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hnorm : ‖‖B‖⁻¹ • B‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hsym : (‖B‖⁻¹ • B).toLinearMap.IsSymmetric :=
    LinearMap.IsSymmetric.smul (by rfl) hB
  have ht : 0 ≤ linearizedTrace A (‖B‖⁻¹ • B) := by
    rw [linearizedTrace_smul]
    exact mul_nonneg (inv_nonneg.mpr hn.le) htr
  have hb := hbound (A, ‖B‖⁻¹ • B) ⟨⟨hA, hnorm, hsym⟩, ht⟩
  have he : q (A, ‖B‖⁻¹ • B) =
      ‖B‖⁻¹ * ∑ v ∈ F, max 0 (inner ℝ (B v) v) := by
    dsimp only [q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [smul_apply, real_inner_smul_left]
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hn.le), mul_zero]
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_left hb hn.le
  have hc : ‖B‖ * (‖B‖⁻¹ * ∑ v ∈ F, max 0 (inner ℝ (B v) v)) =
      ∑ v ∈ F, max 0 (inner ℝ (B v) v) := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  rw [hc] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hκ.le)
  convert! hh' using 1 <;> field_simp

end Submission.Obl.Entropy__smooth_gaussian_transport
