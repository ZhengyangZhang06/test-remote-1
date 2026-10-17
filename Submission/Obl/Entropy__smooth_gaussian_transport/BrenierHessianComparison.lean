import Submission.Obl.Entropy__smooth_gaussian_transport.HessianComparison

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- On a compact spatial set, the almost-everywhere Hessians range in a
compact set of positive definite operators. -/
theorem brenier_ae_compact_hessians {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ S : Set (E m →L[ℝ] E m), IsCompact S ∧
      (∀ A ∈ S, (operatorMatrix A).PosDef) ∧
      ∀ᵐ x ∂volume, x ∈ K → fderiv ℝ (gradient φ) x ∈ S := by
  let L := 10 * (1 / Real.sqrt a)
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hnorm (x : E m) : ‖fderiv ℝ (gradient φ) x‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨l, U, hl, _, hb⟩ := density_bounds_on_compact
    (brenier_alexandrov_continuous_density hm hV.continuous hφ hlaw)
    (fun x => mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)) hK
  let S : Set (E m →L[ℝ] E m) := {A | ‖A‖ ≤ L ∧ (operatorMatrix A).PosSemidef ∧ l ≤ A.det}
  have hS : IsCompact S := by
    convert! (isCompact_closedBall (0 : E m →L[ℝ] E m) L).inter_right
      (isClosed_nonnegative_operators.inter
        (isClosed_le (continuous_const (y := l)) ContinuousLinearMap.continuous_det)) using 1
    ext A
    simp only [S, Metric.mem_closedBall, dist_zero_right, mem_inter_iff, mem_ofPred_eq]
  refine ⟨S, hS, ?_, ?_⟩
  · intro A hA
    apply hA.2.1.posDef_iff_det_ne_zero.mpr
    rw [operatorMatrix_det]
    exact (hl.trans_le hA.2.2).ne'
  · filter_upwards [brenier_ae_positive_hessian hm hV.continuous hφ hlaw] with x hx
    intro hxK
    refine ⟨hnorm x, hx.2.1.posSemidef, ?_⟩
    rw [hx.2.2]
    exact (hb x hxK).1

/-- Smooth functions of position and a Lipschitz gradient are Lipschitz on
compact sets, with a constant independent of the two selected points. -/
theorem smooth_composition_compact_lipschitz {m : ℕ} {g : E m → E m}
    {L : NNReal} (hg : LipschitzWith L g) {F : E m × E m → ℝ}
    (hF : ContDiff ℝ 1 F) {K : Set (E m)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      |F (y, g y) - F (x, g x)| ≤ C * ‖y - x‖ := by
  let f : E m → E m × E m := fun x => (x, g x)
  have hf : Continuous f := continuous_id.prodMk hg.continuous
  obtain ⟨D, hD⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hK.image hf) hF.locallyLipschitz.locallyLipschitzOn
  refine ⟨((D : ℝ) + 1) * (1 + (L : ℝ)), by positivity, ?_⟩
  intro x hx y hy
  have hdist : dist (f y) (f x) ≤ (1 + (L : ℝ)) * ‖y - x‖ := by
    change max (dist y x) (dist (g y) (g x)) ≤ _
    apply max_le
    · rw [dist_eq_norm]
      nlinarith [norm_nonneg (y - x), L.coe_nonneg]
    · have hh := hg.dist_le_mul y x
      rw [dist_eq_norm y x] at hh
      nlinarith [norm_nonneg (y - x)]
  calc
    _ = dist (F (f y)) (F (f x)) := (Real.dist_eq _ _).symm
    _ ≤ (D : ℝ) * dist (f y) (f x) :=
      hD.dist_le_mul _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hx)
    _ ≤ (D : ℝ) * ((1 + (L : ℝ)) * ‖y - x‖) := mul_le_mul_of_nonneg_left hdist D.coe_nonneg
    _ ≤ (((D : ℝ) + 1) * (1 + (L : ℝ))) * ‖y - x‖ := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 1 + (L : ℝ)) (norm_nonneg (y - x))]

/-- The equation compares Hessians at two almost-everywhere points using
only finitely many directional second derivatives and a linear spatial error. -/
theorem brenier_ae_hessian_comparison {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ F : Finset (E m), (∀ v ∈ F, ‖v‖ = 1) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᵐ x ∂volume, ∀ᵐ y ∂volume, x ∈ K → y ∈ K →
        ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤
          C * ((∑ v ∈ F, max 0
            (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
              inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) + ‖y - x‖) := by
  obtain ⟨S, hS, hpos, hmem⟩ := brenier_ae_compact_hessians hm hV ha hH hφ hlaw hK
  obtain ⟨F, hF, C, hC, hcomp⟩ := finite_directions_hessian_comparison hm hS hpos
  let f : E m × E m → ℝ := fun z =>
    Real.log (Submission.Lib.EntropyRemainder.gaussianDensity z.1) + V z.2
  have hf : ContDiff ℝ 1 f := by
    apply ContDiff.add
    · exact (Submission.Lib.EntropyRemainder.gaussianDensity_contDiff.comp contDiff_fst).log
        (fun z => (Submission.Lib.EntropyRemainder.gaussianDensity_pos z.1).ne')
    · exact (hV.of_le (by norm_num)).comp contDiff_snd
  obtain ⟨D, hD, hlog⟩ := smooth_composition_compact_lipschitz
    (brenier_gradient_lipschitz hm hV ha hH hφ hlaw) hf hK
  refine ⟨F, hF, C * (D + 1), mul_pos hC (by linarith), ?_⟩
  have hAE := brenier_ae_positive_hessian hm hV.continuous hφ hlaw
  filter_upwards [hmem, hAE] with x hx hxeq
  filter_upwards [hmem, hAE] with y hy hyeq
  intro hxK hyK
  have hh := hcomp _ (hx hxK) _ (hy hyK)
  have hl := hlog x hxK y hyK
  have hlogeq (z : E m) (hz : (fderiv ℝ (gradient φ) z).det =
      Submission.Lib.EntropyRemainder.gaussianDensity z * Real.exp (V (gradient φ z))) :
      Real.log (fderiv ℝ (gradient φ) z).det = f (z, gradient φ z) := by
    rw [hz, Real.log_mul (Submission.Lib.EntropyRemainder.gaussianDensity_pos _).ne'
      (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogeq y hyeq.2.2, hlogeq x hxeq.2.2] at hh
  let P : ℝ := ∑ v ∈ F, max 0
    (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
      inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  calc
    _ ≤ C * (P + |f (y, gradient φ y) - f (x, gradient φ x)|) := hh
    _ ≤ C * (P + D * ‖y - x‖) := by gcongr
    _ ≤ C * ((D + 1) * (P + ‖y - x‖)) := by
      gcongr
      nlinarith [mul_nonneg hD.le hP, norm_nonneg (y - x)]
    _ = _ := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
