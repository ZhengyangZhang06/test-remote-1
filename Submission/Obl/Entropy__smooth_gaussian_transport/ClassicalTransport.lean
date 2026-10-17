import Submission.Obl.Entropy__smooth_gaussian_transport.HessianHolder

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_positive_hessian {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    (operatorMatrix (fderiv ℝ (gradient φ) x)).PosDef ∧
      (fderiv ℝ (gradient φ) x).det =
        Submission.Lib.EntropyRemainder.gaussianDensity x * Real.exp (V (gradient φ x)) := by
  have hC2 := brenier_contDiff_two hm hV ha hH hφ hlaw
  have hd := hC2.differentiable (by norm_num)
  have hgd := (contDiff_one_gradient_of_contDiff_two hC2).differentiable_one
  have hp := operatorMatrix_posDef (symmetric_gradient_derivative hd (hgd x).hasFDerivAt)
    (nonneg_gradient_derivative hφ hd (hgd x).hasFDerivAt)
    (brenier_det_fderiv_gradient_ne_zero_of_contDiff_two hm hV.continuous hφ hC2 hlaw x)
  refine ⟨hp, ?_⟩
  have he := brenier_classical_density_of_contDiff_two hm hV.continuous hφ hC2 hlaw x
  rwa [abs_of_pos (by simpa only [operatorMatrix_det] using hp.det_pos)] at he

/-- The logarithmic Monge–Ampère equation holds at every point. -/
theorem brenier_log_det_equation {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (x : E m) :
    Real.log (fderiv ℝ (gradient φ) x).det =
      Real.log (Submission.Lib.EntropyRemainder.gaussianDensity x) + V (gradient φ x) := by
  rw [(brenier_positive_hessian hm hV ha hH hφ hlaw x).2,
    Real.log_mul (Submission.Lib.EntropyRemainder.gaussianDensity_pos x).ne' (Real.exp_pos _).ne',
    Real.log_exp]

/-- The classical linearized equation has uniform ellipticity and bounded
drift on each compact set. -/
theorem brenier_linearized_bounds {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ δ Λ M : ℝ, 0 < δ ∧ 0 < Λ ∧ 0 < M ∧ ∀ x ∈ K,
      ‖gradient V (gradient φ x)‖ ≤ M ∧
      ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (fderiv ℝ (gradient φ) x) B ∧
        linearizedTrace (fderiv ℝ (gradient φ) x) B ≤ Λ * ‖B‖ := by
  have hc := brenier_hessian_continuous hm hV ha hH hφ hlaw
  obtain ⟨δ, Λ, hδ, hΛ, hb⟩ := uniform_linearizedTrace_bounds (hK.image hc) (by
    rintro A ⟨x, hx, rfl⟩
    exact (brenier_positive_hessian hm hV ha hH hφ hlaw x).1)
  have hcont : Continuous (fun x => gradient V (gradient φ x)) :=
    (continuous_gradient_of_contDiff_one (hV.of_le (by norm_num))).comp
      (brenier_gradient_lipschitz hm hV ha hH hφ hlaw).continuous
  obtain ⟨M, hM, hMb⟩ := (hK.image hcont).isBounded.exists_pos_norm_le
  exact ⟨δ, Λ, M, hδ, hΛ, hM, fun x hx =>
    ⟨hMb _ (mem_image_of_mem _ hx), hb _ (mem_image_of_mem _ hx)⟩⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
