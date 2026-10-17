import Submission.Obl.Entropy__smooth_gaussian_transport.DensityBounds

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- At a differentiability point, the gradient of a convex function is a supporting vector. -/
theorem convex_gradient_support {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {x : E m} (hx : DifferentiableAt ℝ φ x) (y : E m) :
    φ x + inner ℝ (gradient φ x) (y - x) ≤ φ y := by
  have hc : ConvexOn ℝ univ (fun t : ℝ => φ (x + t • (y - x))) := by
    simpa only [Function.comp_def, preimage_univ, AffineMap.lineMap_apply_module', add_comm]
      using hφ.comp_affineMap (AffineMap.lineMap x y)
  have hp : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hx' : DifferentiableAt ℝ φ (x + (0 : ℝ) • (y - x)) := by simpa using hx
  have hd : HasDerivAt (fun t : ℝ => φ (x + t • (y - x))) (fderiv ℝ φ x (y - x)) 0 := by
    convert! hx'.hasFDerivAt.comp_hasDerivAt 0 hp using 1
    simp
  have hs := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num) hd
  simp only [slope, one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero,
    inv_one, vsub_eq_sub] at hs
  change φ x + (InnerProductSpace.toDual ℝ (E m) (gradient φ x)) (y - x) ≤ φ y
  rw [toDual_gradient]
  linarith

/-- The effective domain of the convex conjugate. -/
def conjugateDomain {m : ℕ} (φ : E m → ℝ) : Set (E m) :=
  {y | BddAbove (range (fun x => inner ℝ y x - φ x))}

theorem conjugateDomain_convex {m : ℕ} (φ : E m → ℝ) :
    Convex ℝ (conjugateDomain φ) := by
  intro y hy z hz a b ha hb hab
  obtain ⟨A, hA⟩ := hy
  obtain ⟨B, hB⟩ := hz
  refine ⟨a * A + b * B, ?_⟩
  rintro w ⟨x, rfl⟩
  change inner ℝ (a • y + b • z) x - φ x ≤ a * A + b * B
  calc
    _ = a * (inner ℝ y x - φ x) + b * (inner ℝ z x - φ x) := by
      simp only [inner_add_left, real_inner_smul_left]
      linear_combination (φ x) * hab
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hA (mem_range_self x)) ha)
      (mul_le_mul_of_nonneg_left (hB (mem_range_self x)) hb)

theorem gradient_mem_conjugateDomain {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {x : E m} (hx : DifferentiableAt ℝ φ x) :
    gradient φ x ∈ conjugateDomain φ := by
  refine ⟨inner ℝ (gradient φ x) x - φ x, ?_⟩
  rintro z ⟨y, rfl⟩
  have h := convex_gradient_support hφ hx y
  rw [inner_sub_right] at h
  linarith

/-- A convex transport to a full-support law has a finite conjugate everywhere. -/
theorem conjugateDomain_eq_univ_of_transport {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {μ : Measure (E m)} (hμ : μ ≪ volume)
    (hsupp : (Measure.map (gradient φ) μ).support = univ) :
    conjugateDomain φ = univ := by
  have hmeas := Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient φ
  have hae : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x :=
    hμ.ae_le (Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hφ volume)
  have hs : (Measure.map (gradient φ) μ).support ⊆ closure (conjugateDomain φ) := by
    apply Measure.support_subset_of_isClosed isClosed_closure
    apply (ae_map_iff hmeas.aemeasurable isClosed_closure.measurableSet).mpr
    filter_upwards [hae] with x hx
    exact subset_closure (gradient_mem_conjugateDomain hφ hx)
  apply Submission.Lib.Brenier.CyclicPotential.convex_dense_eq_univ (conjugateDomain_convex φ)
  rw [dense_iff_closure_eq]
  exact eq_univ_of_univ_subset (hsupp ▸ hs)

noncomputable def finiteConjugate {m : ℕ} (φ : E m → ℝ) (y : E m) : ℝ :=
  sSup (range (fun x => inner ℝ y x - φ x))

theorem bounded_conjugate_values {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) (y : E m) :
    BddAbove (range (fun x => inner ℝ y x - φ x)) := by
  change y ∈ conjugateDomain φ
  rw [hdom]
  exact mem_univ y

theorem finiteConjugate_convex {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) : ConvexOn ℝ univ (finiteConjugate φ) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ a b ha hb hab
  apply csSup_le (range_nonempty _)
  rintro w ⟨x, rfl⟩
  change inner ℝ (a • y + b • z) x - φ x ≤ a * finiteConjugate φ y + b * finiteConjugate φ z
  calc
    _ = a * (inner ℝ y x - φ x) + b * (inner ℝ z x - φ x) := by
      simp only [inner_add_left, real_inner_smul_left]
      linear_combination (φ x) * hab
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (le_csSup (bounded_conjugate_values hdom y) (mem_range_self x)) ha)
      (mul_le_mul_of_nonneg_left (le_csSup (bounded_conjugate_values hdom z) (mem_range_self x)) hb)

theorem fenchel_inequality {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) (x y : E m) :
    inner ℝ y x ≤ φ x + finiteConjugate φ y := by
  have h := le_csSup (bounded_conjugate_values hdom y) (mem_range_self x)
  change inner ℝ y x - φ x ≤ finiteConjugate φ y at h
  linarith

theorem finiteConjugate_gradient {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {x : E m} (hx : DifferentiableAt ℝ φ x) :
    finiteConjugate φ (gradient φ x) = inner ℝ (gradient φ x) x - φ x := by
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro z ⟨y, rfl⟩
    have h := convex_gradient_support hφ hx y
    rw [inner_sub_right] at h
    linarith
  · exact le_csSup (gradient_mem_conjugateDomain hφ hx) (mem_range_self x)

theorem conjugate_support_at_gradient {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hdom : conjugateDomain φ = univ)
    {x : E m} (hx : DifferentiableAt ℝ φ x) (y : E m) :
    finiteConjugate φ (gradient φ x) + inner ℝ x (y - gradient φ x) ≤
      finiteConjugate φ y := by
  rw [finiteConjugate_gradient hφ hx, inner_sub_right,
    real_inner_comm y x, real_inner_comm (gradient φ x) x]
  linarith [fenchel_inequality hdom x y]

/-- The conjugate gradient inverts the transport almost everywhere when both laws are
absolutely continuous and the target has full support. -/
theorem inverse_gradient_ae {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {μ : Measure (E m)} (hμ : μ ≪ volume)
    (hν : Measure.map (gradient φ) μ ≪ volume)
    (hsupp : (Measure.map (gradient φ) μ).support = univ) :
    ∀ᵐ x ∂μ, gradient (finiteConjugate φ) (gradient φ x) = x := by
  have hdom := conjugateDomain_eq_univ_of_transport hφ hμ hsupp
  have hψ := finiteConjugate_convex hdom
  have hφdiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x :=
    hμ.ae_le (Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hφ volume)
  have hψdiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ (finiteConjugate φ) (gradient φ x) := by
    apply ae_of_ae_map
      (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient φ).aemeasurable
    exact hν.ae_le (Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hψ volume)
  filter_upwards [hφdiff, hψdiff] with x hx hψx
  exact Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support hψx
    (conjugate_support_at_gradient hφ hdom hx)

theorem inverse_gradient_law {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) {μ : Measure (E m)} (hμ : μ ≪ volume)
    (hν : Measure.map (gradient φ) μ ≪ volume)
    (hsupp : (Measure.map (gradient φ) μ).support = univ) :
    Measure.map (gradient (finiteConjugate φ)) (Measure.map (gradient φ) μ) = μ := by
  rw [Measure.map_map (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _)
    (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _)]
  change Measure.map (fun x => gradient (finiteConjugate φ) (gradient φ x)) μ = μ
  rw [Measure.map_congr (inverse_gradient_ae hφ hμ hν hsupp)]
  change Measure.map (id : E m → E m) μ = μ
  exact Measure.map_id

/-- Finiteness of the conjugate gives lower bounds with any prescribed nonnegative linear growth. -/
theorem arbitrary_linear_minorant {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, ∀ x, R * ‖x‖ - M ≤ φ x := by
  have hc := (finiteConjugate_convex hdom).locallyLipschitz.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E m) R).bddAbove_image hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    have hb : finiteConjugate φ (0 : E m) ≤ M :=
      hM (mem_image_of_mem _ (by simpa using hR))
    have hf := fenchel_inequality hdom (0 : E m) 0
    simp only [norm_zero, mul_zero, inner_zero_right] at hf ⊢
    linarith
  · let y := (R / ‖x‖) • x
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hy : y ∈ Metric.closedBall (0 : E m) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hR (norm_nonneg x)), div_mul_cancel₀ _ hn]
      exact le_rfl
    have hb : finiteConjugate φ y ≤ M := hM (mem_image_of_mem _ hy)
    have hf := fenchel_inequality hdom x y
    have hi : inner ℝ y x = R * ‖x‖ := by
      simp only [y, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hi] at hf
    linarith

theorem tendsto_atTop_of_finite_conjugate {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) : Tendsto φ (cocompact (E m)) atTop := by
  obtain ⟨M, hM⟩ := arbitrary_linear_minorant hdom (R := 1) (by norm_num)
  apply tendsto_atTop_mono hM
  simpa only [one_mul, sub_eq_add_neg] using
    tendsto_atTop_add_const_right (cocompact (E m)) (-M) tendsto_norm_cocompact_atTop

theorem isCompact_sublevel_of_finite_conjugate {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (r : ℝ) :
    IsCompact {x | φ x ≤ r} := by
  have he := (tendsto_atTop_of_finite_conjugate hdom).eventually (eventually_gt_atTop r)
  obtain ⟨K, hK, hsub⟩ := mem_cocompact'.mp he
  apply hK.of_isClosed_subset (isClosed_le hφ continuous_const)
  intro x hx
  exact hsub (by simpa only [mem_compl_iff, mem_ofPred_eq, not_lt] using hx)

/-- Subtracting any linear functional preserves coercivity when the conjugate is finite. -/
theorem tendsto_tilted_atTop_of_finite_conjugate {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) (p : E m) :
    Tendsto (fun x => φ x - inner ℝ p x) (cocompact (E m)) atTop := by
  obtain ⟨M, hM⟩ := arbitrary_linear_minorant hdom (R := ‖p‖ + 1) (by positivity)
  have hl (x : E m) : ‖x‖ - M ≤ φ x - inner ℝ p x := by
    nlinarith [hM x, real_inner_le_norm p x]
  apply tendsto_atTop_mono hl
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right (cocompact (E m)) (-M) tendsto_norm_cocompact_atTop

theorem isCompact_tilted_sublevel_of_finite_conjugate {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (p : E m) (r : ℝ) :
    IsCompact {x | φ x - inner ℝ p x ≤ r} := by
  have he := (tendsto_tilted_atTop_of_finite_conjugate hdom p).eventually (eventually_gt_atTop r)
  obtain ⟨K, hK, hsub⟩ := mem_cocompact'.mp he
  apply hK.of_isClosed_subset (isClosed_le (hφ.sub (continuous_const.inner continuous_id))
    continuous_const)
  intro x hx
  apply hsub
  change ¬r < φ x - inner ℝ p x
  exact not_lt.mpr hx

/-- The Brenier potential has compact sublevel sets when the smooth target has full support. -/
theorem brenier_compact_sublevels {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∀ r : ℝ, IsCompact {x | φ x ≤ r} := by
  apply isCompact_sublevel_of_finite_conjugate hφ.locallyLipschitz.continuous
  apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
  rw [hlaw]
  exact target_support hV

theorem brenier_compact_sections {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∀ (p : E m) (r : ℝ), IsCompact {x | φ x - inner ℝ p x ≤ r} := by
  apply isCompact_tilted_sublevel_of_finite_conjugate hφ.locallyLipschitz.continuous
  apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
  rw [hlaw]
  exact target_support hV

theorem brenier_dual_transport {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ConvexOn ℝ univ (finiteConjugate φ) ∧ Continuous (finiteConjugate φ) ∧
      Measure.map (gradient (finiteConjugate φ))
        (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) = stdGaussian (E m) ∧
      ∀ᵐ x ∂stdGaussian (E m), gradient (finiteConjugate φ) (gradient φ x) = x := by
  have hsupp : (Measure.map (gradient φ) (stdGaussian (E m))).support = univ := by
    rw [hlaw]
    exact target_support hV
  have hν : Measure.map (gradient φ) (stdGaussian (E m)) ≪ volume := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hψ := finiteConjugate_convex
    (conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m) hsupp)
  refine ⟨hψ, hψ.locallyLipschitz.continuous, ?_,
    inverse_gradient_ae hφ (stdGaussian_absolutelyContinuous m) hν hsupp⟩
  rw [← hlaw]
  exact inverse_gradient_law hφ (stdGaussian_absolutelyContinuous m) hν hsupp

end Submission.Obl.Entropy__smooth_gaussian_transport
