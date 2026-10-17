import Submission.Obl.Entropy__smooth_gaussian_transport.SmoothLogDet
import Submission.Obl.Entropy__smooth_gaussian_transport.ClassicalTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem compact_c1_lipschitz {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} {S : Set X}
    (hS : IsCompact S) (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) :
    ∃ C : NNReal, LipschitzOnWith C f S := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  intro x hx
  obtain ⟨C, U, hU, hfU⟩ := (hf x hx).exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hfU⟩

/-- Dependence of the linearized trace on its base Hessian is Lipschitz on a
compact set of invertible operators, uniformly over unit increments. -/
theorem compact_linearizedTrace_lipschitz {m : ℕ} {S : Set (E m →L[ℝ] E m)}
    (hS : IsCompact S) (hdet : ∀ A ∈ S, A.det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ∈ S, ∀ A' ∈ S, ∀ B : E m →L[ℝ] E m,
      |linearizedTrace A B - linearizedTrace A' B| ≤ C * ‖A - A'‖ * ‖B‖ := by
  obtain ⟨C, hC⟩ := compact_c1_lipschitz
    (hS.prod (isCompact_closedBall (0 : E m →L[ℝ] E m) 1))
    (fun z hz => linearizedTrace_contDiffAt (n := 1) (hdet z.1 hz.1))
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro A hA A' hA' B
  by_cases hB : B = 0
  · simp only [hB, linearizedTrace_zero, sub_self, abs_zero, norm_zero, mul_zero, le_refl]
  have hnorm : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hunit : ‖‖B‖⁻¹ • B‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hnorm.ne'
  have hb : ‖B‖⁻¹ • B ∈ Metric.closedBall (0 : E m →L[ℝ] E m) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, hunit, le_refl]
  have hh := hC.dist_le_mul (x := (A, ‖B‖⁻¹ • B)) ⟨hA, hb⟩
    (y := (A', ‖B‖⁻¹ • B)) ⟨hA', hb⟩
  simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd, sub_self, norm_zero, max_eq_left (norm_nonneg (A - A')),
    Real.norm_eq_abs, linearizedTrace_smul, ← mul_sub, abs_mul, abs_inv, abs_norm] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hnorm.le
  have he : ‖B‖ * (‖B‖⁻¹ * |linearizedTrace A B - linearizedTrace A' B|) =
      |linearizedTrace A B - linearizedTrace A' B| := by rw [← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul]
  rw [he] at hh'
  calc
    _ ≤ ‖B‖ * ((C : ℝ) * ‖A - A'‖) := hh'
    _ ≤ ((C : ℝ) + 1) * ‖A - A'‖ * ‖B‖ := by nlinarith [norm_nonneg (A - A')]

/-- The principal coefficients of the classical linearized transport equation
are Hölder continuous on compact sets. -/
theorem brenier_linearized_compact_holder {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ∀ B : E m →L[ℝ] E m,
        |linearizedTrace (fderiv ℝ (gradient φ) y) B -
          linearizedTrace (fderiv ℝ (gradient φ) x) B| ≤ C * ‖y - x‖ ^ α * ‖B‖ := by
  obtain ⟨α, C, hα, hα1, hC, hholder⟩ := brenier_hessian_compact_holder hm hV ha hH hφ hlaw hK
  obtain ⟨L, hL, hb⟩ := compact_linearizedTrace_lipschitz
    (hK.image (brenier_hessian_continuous hm hV ha hH hφ hlaw)) (by
      rintro A ⟨x, hx, rfl⟩
      simpa only [operatorMatrix_det] using
        (brenier_positive_hessian hm hV ha hH hφ hlaw x).1.det_pos.ne')
  refine ⟨α, L * C, hα, hα1, mul_pos hL hC, ?_⟩
  intro x hx y hy B
  calc
    _ ≤ L * ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ * ‖B‖ :=
      hb _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hx) B
    _ ≤ L * (C * ‖y - x‖ ^ α) * ‖B‖ := by gcongr; exact hholder x hx y hy
    _ = _ := by ring

end Submission.Obl.Entropy__smooth_gaussian_transport
