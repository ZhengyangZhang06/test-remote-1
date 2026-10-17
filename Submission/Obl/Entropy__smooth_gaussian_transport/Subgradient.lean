import Submission.Obl.Entropy__smooth_gaussian_transport.Fenchel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A supporting vector for a finite convex function. -/
def IsSubgradient {m : ℕ} (φ : E m → ℝ) (x y : E m) : Prop :=
  ∀ z, φ x + inner ℝ y (z - x) ≤ φ z

/-- The image of a set under the subgradient relation. -/
def subgradientImage {m : ℕ} (φ : E m → ℝ) (s : Set (E m)) : Set (E m) :=
  {y | ∃ x ∈ s, IsSubgradient φ x y}

theorem subgradientImage_mono {m : ℕ} {φ : E m → ℝ} {s t : Set (E m)}
    (hst : s ⊆ t) : subgradientImage φ s ⊆ subgradientImage φ t := by
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, hst hx, hxy⟩

theorem IsSubgradient.finiteConjugate_eq {m : ℕ} {φ : E m → ℝ} {x y : E m}
    (hxy : IsSubgradient φ x y) : finiteConjugate φ y = inner ℝ y x - φ x := by
  have hbound (z : E m) : inner ℝ y z - φ z ≤ inner ℝ y x - φ x := by
    have h := hxy z
    rw [inner_sub_right] at h
    linarith
  have hb : BddAbove (range (fun z => inner ℝ y z - φ z)) := by
    refine ⟨inner ℝ y x - φ x, ?_⟩
    rintro w ⟨z, rfl⟩
    exact hbound z
  apply le_antisymm
  · exact csSup_le (range_nonempty _) (by rintro w ⟨z, rfl⟩; exact hbound z)
  · exact le_csSup hb (mem_range_self x)

theorem IsSubgradient.conjugate {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) {x y : E m} (hxy : IsSubgradient φ x y) :
    IsSubgradient (finiteConjugate φ) y x := by
  intro z
  rw [hxy.finiteConjugate_eq, inner_sub_right, real_inner_comm z x,
    real_inner_comm y x]
  linarith [fenchel_inequality hdom x z]

/-- Every slope has a contact point when all tilted potentials are coercive. -/
theorem exists_subgradient_contact {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (y : E m) :
    ∃ x, IsSubgradient φ x y := by
  obtain ⟨x, hx⟩ := (hφ.sub (continuous_const.inner continuous_id)).exists_forall_le
    (tendsto_tilted_atTop_of_finite_conjugate hdom y)
  refine ⟨x, fun z => ?_⟩
  have h := hx z
  change φ x - inner ℝ y x ≤ φ z - inner ℝ y z at h
  rw [inner_sub_right]
  linarith

/-- At a differentiability point of the conjugate, its gradient is the unique contact point. -/
theorem subgradient_iff_eq_conjugate_gradient {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) {x y : E m}
    (hy : DifferentiableAt ℝ (finiteConjugate φ) y) :
    IsSubgradient φ x y ↔ x = gradient (finiteConjugate φ) y := by
  constructor
  · intro hxy
    exact (Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support hy
      (hxy.conjugate hdom)).symm
  · intro hx
    obtain ⟨z, hz⟩ := exists_subgradient_contact hφ hdom y
    have hzg := Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support hy
      (hz.conjugate hdom)
    simpa only [hx, hzg] using hz

/-- Subgradient images agree almost everywhere with preimages of the conjugate gradient. -/
theorem subgradientImage_ae_eq_preimage {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (s : Set (E m)) :
    subgradientImage φ s =ᵐ[volume] (gradient (finiteConjugate φ)) ⁻¹' s := by
  filter_upwards [Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex
    (finiteConjugate_convex hdom) volume] with y hy
  apply propext
  constructor
  · rintro ⟨x, hx, hxy⟩
    change gradient (finiteConjugate φ) y ∈ s
    rwa [← (subgradient_iff_eq_conjugate_gradient hφ hdom hy).mp hxy]
  · intro hy'
    exact ⟨gradient (finiteConjugate φ) y, hy',
      (subgradient_iff_eq_conjugate_gradient hφ hdom hy).mpr rfl⟩

/-- Supporting vectors over bounded sets are uniformly bounded. -/
theorem isBounded_subgradientImage {m : ℕ} {φ : E m → ℝ} (hφ : Continuous φ)
    {s : Set (E m)} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (subgradientImage φ s) := by
  obtain ⟨R, hR⟩ := hs.exists_norm_le
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : E m) (R + 1)).image hφ).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max 0 (2 * M), ?_⟩
  rintro y ⟨x, hx, hxy⟩
  by_cases hy : y = 0
  · simp [hy]
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let u := ‖y‖⁻¹ • y
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hny]
  have hxball : x ∈ Metric.closedBall (0 : E m) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [hR x hx]
  have hzball : x + u ∈ Metric.closedBall (0 : E m) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le _ _
      _ ≤ R + 1 := by rw [hu]; linarith [hR x hx]
  have hxM := hM (φ x) (mem_image_of_mem φ hxball)
  have hzM := hM (φ (x + u)) (mem_image_of_mem φ hzball)
  have hinner : inner ℝ y u = ‖y‖ := by
    simp only [u, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h := hxy (x + u)
  rw [add_sub_cancel_left, hinner] at h
  apply le_trans _ (le_max_right _ _)
  have hxM' := (abs_le.mp hxM).1
  have hzM' := (abs_le.mp hzM).2
  linarith

theorem isClosed_subgradient_graph {m : ℕ} {φ : E m → ℝ} (hφ : Continuous φ) :
    IsClosed {p : E m × E m | IsSubgradient φ p.1 p.2} := by
  simp only [IsSubgradient, ofPred_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_le ((hφ.comp continuous_fst).add
    (continuous_snd.inner (continuous_const.sub continuous_fst))) continuous_const

/-- The subgradient image of a compact set is compact. -/
theorem isCompact_subgradientImage {m : ℕ} {φ : E m → ℝ} (hφ : Continuous φ)
    {s : Set (E m)} (hs : IsCompact s) : IsCompact (subgradientImage φ s) := by
  obtain ⟨R, hR⟩ := (isBounded_subgradientImage hφ hs.isBounded).exists_norm_le
  let K := (s ×ˢ Metric.closedBall (0 : E m) R) ∩
    {p : E m × E m | IsSubgradient φ p.1 p.2}
  have hK : IsCompact K :=
    (hs.prod (isCompact_closedBall _ _)).inter_right (isClosed_subgradient_graph hφ)
  have heq : Prod.snd '' K = subgradientImage φ s := by
    ext y
    constructor
    · rintro ⟨⟨x, y⟩, ⟨⟨hx, _⟩, hxy⟩, rfl⟩
      exact ⟨x, hx, hxy⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨(x, y), ⟨⟨hx, by simpa using hR y ⟨x, hx, hxy⟩⟩, hxy⟩, rfl⟩
  rw [← heq]
  exact hK.image continuous_snd

theorem subgradientImage_nullMeasurableSet {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ)
    {s : Set (E m)} (hs : MeasurableSet s) :
    NullMeasurableSet (subgradientImage φ s) volume := by
  apply (hs.preimage (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _)).nullMeasurableSet.congr
  exact (subgradientImage_ae_eq_preimage hφ hdom s).symm

/-- The inverse gradient law is the weighted Alexandrov mass identity. -/
theorem measure_subgradientImage {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ)
    {μ ν : Measure (E m)} (hν : ν ≪ volume)
    (hlaw : Measure.map (gradient (finiteConjugate φ)) ν = μ)
    {s : Set (E m)} (hs : MeasurableSet s) : ν (subgradientImage φ s) = μ s := by
  rw [measure_congr (hν.ae_le (subgradientImage_ae_eq_preimage hφ hdom s)), ← hlaw]
  exact (Measure.map_apply
    (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _) hs).symm

theorem brenier_subgradient_mass {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {s : Set (E m)} (hs : MeasurableSet s) :
    (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
      (subgradientImage φ s) = stdGaussian (E m) s := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  exact measure_subgradientImage hφ.locallyLipschitz.continuous hdom
    (withDensity_absolutelyContinuous _ _) (brenier_dual_transport hV hφ hlaw).2.2.1 hs

theorem brenier_weak_mongeAmpere {m : ℕ} {V φ : E m → ℝ} (hV : Continuous V)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {s : Set (E m)} (hs : MeasurableSet s) :
    ∫⁻ y in subgradientImage φ s, ENNReal.ofReal (Real.exp (-V y)) =
      ∫⁻ x in s, ENNReal.ofReal (Submission.Lib.EntropyRemainder.gaussianDensity x) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  rw [← withDensity_apply₀ _
    (subgradientImage_nullMeasurableSet hφ.locallyLipschitz.continuous hdom hs),
    brenier_subgradient_mass hV hφ hlaw hs,
    Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity, withDensity_apply _ hs]

end Submission.Obl.Entropy__smooth_gaussian_transport
