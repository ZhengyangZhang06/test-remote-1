import Submission.Obl.Entropy__smooth_gaussian_transport.Alexandrov

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem conjugateDomain_finiteConjugate {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) : conjugateDomain (finiteConjugate φ) = univ := by
  apply eq_univ_of_forall
  intro x
  refine ⟨φ x, ?_⟩
  rintro t ⟨y, rfl⟩
  have h := fenchel_inequality hdom x y
  change inner ℝ x y - finiteConjugate φ y ≤ φ x
  rw [real_inner_comm y x]
  linarith

theorem finiteConjugate_involutive {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hdom : conjugateDomain φ = univ) :
    finiteConjugate (finiteConjugate φ) = φ := by
  have hdom' := conjugateDomain_finiteConjugate hdom
  have hle (x : E m) : finiteConjugate (finiteConjugate φ) x ≤ φ x := by
    apply csSup_le (range_nonempty _)
    rintro t ⟨y, rfl⟩
    have h := fenchel_inequality hdom x y
    change inner ℝ x y - finiteConjugate φ y ≤ φ x
    rw [real_inner_comm y x]
    linarith
  have hae : finiteConjugate (finiteConjugate φ) =ᵐ[volume] φ := by
    filter_upwards [Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hφ volume]
      with x hx
    apply (hle x).antisymm
    have h := fenchel_inequality hdom' (gradient φ x) x
    rw [finiteConjugate_gradient hφ hx, real_inner_comm x (gradient φ x)] at h
    linarith
  exact Measure.eq_of_ae_eq hae
    (finiteConjugate_convex hdom').locallyLipschitz.continuous hφ.locallyLipschitz.continuous

theorem subgradient_conjugate_iff {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hdom : conjugateDomain φ = univ) {x y : E m} :
    IsSubgradient φ x y ↔ IsSubgradient (finiteConjugate φ) y x := by
  constructor
  · exact fun h => h.conjugate hdom
  · intro h
    have h' := h.conjugate (conjugateDomain_finiteConjugate hdom)
    rwa [finiteConjugate_involutive hφ hdom] at h'

theorem exists_subgradient {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hdom : conjugateDomain φ = univ) (x : E m) :
    ∃ y, IsSubgradient φ x y := by
  obtain ⟨y, hy⟩ := exists_subgradient_contact
    (finiteConjugate_convex hdom).locallyLipschitz.continuous
    (conjugateDomain_finiteConjugate hdom) x
  exact ⟨y, (subgradient_conjugate_iff hφ hdom).mpr hy⟩

/-- Points at which a prescribed supporting plane touches the potential. -/
def contactSet {m : ℕ} (φ : E m → ℝ) (p : E m) : Set (E m) :=
  {x | IsSubgradient φ x p}

theorem contactSet_eq_sublevel {m : ℕ} {φ : E m → ℝ}
    (hdom : conjugateDomain φ = univ) (p : E m) :
    contactSet φ p = {x | φ x - inner ℝ p x ≤ -finiteConjugate φ p} := by
  ext x
  constructor
  · intro hx
    have he := (show IsSubgradient φ x p from hx).finiteConjugate_eq
    change φ x - inner ℝ p x ≤ -finiteConjugate φ p
    linarith
  · intro hx z
    have h := fenchel_inequality hdom z p
    change φ x - inner ℝ p x ≤ -finiteConjugate φ p at hx
    rw [inner_sub_right]
    linarith

theorem contactSet_nonempty {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (p : E m) :
    (contactSet φ p).Nonempty := exists_subgradient_contact hφ hdom p

theorem isCompact_contactSet {m : ℕ} {φ : E m → ℝ}
    (hφ : Continuous φ) (hdom : conjugateDomain φ = univ) (p : E m) :
    IsCompact (contactSet φ p) := by
  rw [contactSet_eq_sublevel hdom]
  exact isCompact_tilted_sublevel_of_finite_conjugate hφ hdom p _

theorem convex_contactSet {m : ℕ} {φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hdom : conjugateDomain φ = univ) (p : E m) :
    Convex ℝ (contactSet φ p) := by
  rw [contactSet_eq_sublevel hdom]
  have ht : ConvexOn ℝ univ (fun x => φ x - inner ℝ p x) := by
    exact hφ.sub ((InnerProductSpace.toDual ℝ (E m) p).toLinearMap.concaveOn convex_univ)
  simpa only [mem_univ, true_and] using ht.convex_le (-finiteConjugate φ p)

theorem volume_absolutelyContinuous_stdGaussian (m : ℕ) :
    (volume : Measure (E m)) ≪ stdGaussian (E m) := by
  rw [Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity]
  apply withDensity_absolutelyContinuous'
    Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable.ennreal_ofReal.aemeasurable
  filter_upwards with x
  exact ENNReal.ofReal_ne_zero_iff.mpr (Submission.Lib.EntropyRemainder.gaussianDensity_pos x)

/-- A contact set cannot have positive volume, since its differentiability points all
map to the same target point. -/
theorem brenier_contactSet_volume_zero {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (p : E m) :
    volume (contactSet φ p) = 0 := by
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  apply volume_absolutelyContinuous_stdGaussian m
  have hsub : contactSet φ p ≤ᵐ[stdGaussian (E m)] (gradient φ) ⁻¹' {p} := by
    filter_upwards [(stdGaussian_absolutelyContinuous m).ae_le
      (Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hφ volume)] with x hx
    intro hxp
    change gradient φ x = p
    exact Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support hx hxp
  apply measure_mono_null_ae hsub
  rw [← Measure.map_apply (Submission.Lib.Brenier.ConvexGradientLaw.measurable_gradient _)
    (measurableSet_singleton p), hlaw]
  exact measure_singleton p

end Submission.Obl.Entropy__smooth_gaussian_transport
