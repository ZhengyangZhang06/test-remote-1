import Submission.Obl.Entropy__smooth_gaussian_transport.LipschitzTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem positive_inner_of_nonnegative_invertible {m : ℕ} {A : E m →L[ℝ] E m}
    (hs : A.toLinearMap.IsSymmetric) (hp : ∀ v, 0 ≤ inner ℝ (A v) v)
    (hd : A.det ≠ 0) {v : E m} (hv : v ≠ 0) : 0 < inner ℝ (A v) v := by
  by_contra hn
  have hz : inner ℝ (A v) v = 0 := le_antisymm (not_lt.mp hn) (hp v)
  have hcross : inner ℝ (A (A v)) v = ‖A v‖ ^ 2 := by
    rw [hs.apply_clm (A v) v, real_inner_self_eq_norm_sq]
  have hdisc : discrim (inner ℝ (A (A v)) (A v)) (2 * ‖A v‖ ^ 2) 0 ≤ 0 := by
    apply discrim_le_zero
    intro t
    have hh := hp (v + t • A v)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hz, hcross, real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh]
  rw [discrim] at hdisc
  have hsq : (2 * ‖A v‖ ^ 2) ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    simpa only [mul_zero, sub_zero] using hdisc
  have hzero := sq_eq_zero_iff.mp hsq
  have hAv : A v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (A v)])
  apply hv
  have hk : LinearMap.ker A.toLinearMap = ⊥ :=
    not_ne_iff.mp (fun hk => hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  apply (LinearMap.ker_eq_bot.mp hk)
  change A v = A 0
  rw [map_zero]
  exact hAv

/-- Bounded nonnegative symmetric operators with determinant bounded away
from zero share a positive lower quadratic bound. -/
theorem uniform_positive_lower_bound {m : ℕ} {l L : ℝ} (hl : 0 < l) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : E m →L[ℝ] E m,
      ‖A‖ ≤ L → A.toLinearMap.IsSymmetric → (∀ v, 0 ≤ inner ℝ (A v) v) →
      l ≤ A.det → ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ (A v) v := by
  let S : Set (E m →L[ℝ] E m) :=
    {A | ‖A‖ ≤ L ∧ A.toLinearMap.IsSymmetric ∧ (∀ v, 0 ≤ inner ℝ (A v) v) ∧ l ≤ A.det}
  have hsymclosed : IsClosed {A : E m →L[ℝ] E m | A.toLinearMap.IsSymmetric} := by
    change IsClosed {A : E m →L[ℝ] E m | ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro w
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hposclosed : IsClosed {A : E m →L[ℝ] E m | ∀ v, 0 ≤ inner ℝ (A v) v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (by fun_prop)
  have hclosed : IsClosed S :=
    (isClosed_le continuous_norm continuous_const).inter
      (hsymclosed.inter (hposclosed.inter (isClosed_le continuous_const ContinuousLinearMap.continuous_det)))
  have hS : IsCompact S := (isCompact_closedBall (0 : E m →L[ℝ] E m) L).of_isClosed_subset hclosed
    (fun A hA => by simpa only [Metric.mem_closedBall, dist_zero_right] using hA.1)
  let Q : (E m →L[ℝ] E m) × E m → ℝ := fun z => inner ℝ (z.1 z.2) z.2
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hunitpos (z : (E m →L[ℝ] E m) × E m) (hz : z ∈ S ×ˢ Metric.sphere 0 1) : 0 < Q z := by
    have hv : z.2 ≠ 0 := by
      have hh : ‖z.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
      intro he
      rw [he, norm_zero] at hh
      norm_num at hh
    exact positive_inner_of_nonnegative_invertible hz.1.2.1 hz.1.2.2.1
      (hl.trans_le hz.1.2.2.2).ne' hv
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ S ×ˢ Metric.sphere 0 1, δ ≤ Q z := by
    by_cases hne : (S ×ˢ Metric.sphere (0 : E m) 1).Nonempty
    · obtain ⟨z, hz, hzmin⟩ := (hS.prod (isCompact_sphere (0 : E m) 1)).exists_isMinOn hne hQ.continuousOn
      exact ⟨Q z, hunitpos z hz, fun y hy => hzmin hy⟩
    · exact ⟨1, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  refine ⟨δ, hδ, fun A hnorm hsym hpos hdet v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖‖v‖⁻¹ • v‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hvnorm.ne'
  have hb := hbound (A, ‖v‖⁻¹ • v)
    ⟨⟨hnorm, hsym, hpos, hdet⟩, by simpa only [Metric.mem_sphere, dist_zero_right] using he⟩
  dsimp only [Q] at hb
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hb
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)
  have hcancel : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * inner ℝ (A v) v)) = inner ℝ (A v) v := by
    field_simp
  rw [hcancel] at hh
  simpa only [mul_comm] using hh

/-- On each compact set the almost-everywhere transport Hessian is uniformly
positive definite. Its upper bound comes from the global Lipschitz estimate. -/
theorem brenier_ae_uniform_ellipticity {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ᵐ x ∂volume, x ∈ K →
      DifferentiableAt ℝ (gradient φ) x ∧
      ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient φ) x v) v ∧
        inner ℝ (fderiv ℝ (gradient φ) x v) v ≤ L * ‖v‖ ^ 2 := by
  let L := 10 * (1 / Real.sqrt a)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hnorm (x : E m) : ‖fderiv ℝ (gradient φ) x‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨l, U, hl, _, hb⟩ := density_bounds_on_compact
    (brenier_alexandrov_continuous_density hm hV.continuous hφ hlaw)
    (fun x => mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)) hK
  obtain ⟨δ, hδ, hδbound⟩ := uniform_positive_lower_bound (L := L) hl
  refine ⟨δ, L, hδ, hL, ?_⟩
  filter_upwards [brenier_ae_positive_hessian hm hV.continuous hφ hlaw,
    brenier_ae_hessian_structure hm hV.continuous hφ hlaw] with x hx hx'
  intro hxK
  refine ⟨hx.1, fun v => ⟨?_, ?_⟩⟩
  · apply hδbound _ (hnorm x) hx'.2.1 hx'.2.2.1
    rw [hx.2.2]
    exact (hb x hxK).1
  · calc
      inner ℝ (fderiv ℝ (gradient φ) x v) v ≤ ‖fderiv ℝ (gradient φ) x v‖ * ‖v‖ :=
        real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ (gradient φ) x‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (gradient φ) x).le_opNorm v) (norm_nonneg v)
      _ ≤ (L * ‖v‖) * ‖v‖ := by gcongr; exact hnorm x
      _ = L * ‖v‖ ^ 2 := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
