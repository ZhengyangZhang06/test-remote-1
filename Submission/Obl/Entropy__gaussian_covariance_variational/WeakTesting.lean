import Submission.Obl.Entropy__gaussian_covariance_variational.Cutoff

open MeasureTheory Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_covariance_variational

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Extending compact smooth tests to smooth Gaussian H1 tests by dilated cutoffs. -/
theorem weak_h1_testing {μ : Measure E} {h : E → ℝ} {b : Fin m → E → ℝ}
    (hh : MemLp h 2 μ) (hb : ∀ r, MemLp (b r) 2 μ)
    (hw : ∀ z : E → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z →
      HasCompactSupport z → (∫ x, h x * z x ∂μ) =
        ∑ r, ∫ x, b r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)
    (z : E → ℝ) (hz : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z)
    (hz2 : MemLp z 2 μ)
    (hdz2 : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 μ) :
    (∫ x, h x * z x ∂μ) =
      ∑ r, ∫ x, b r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ := by
  let Z (n : ℕ) (x : E) := cutoff n x * z x
  have hZ (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Z n) :=
    (cutoff_contDiff n).mul hz
  have hdZ (n : ℕ) (x v : E) : fderiv ℝ (Z n) x v =
      fderiv ℝ (cutoff n) x v * z x + cutoff n x * fderiv ℝ z x v := by
    rw [fderiv_fun_mul ((cutoff_contDiff n).differentiable (by simp) x)
      (hz.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hcNorm (n : ℕ) (x : E) : ‖cutoff n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_bounds n x).1]
    exact (cutoff_bounds n x).2
  have hl : Tendsto (fun n => ∫ x, h x * Z n x ∂μ) atTop
      (𝓝 (∫ x, h x * z x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖h x * z x‖)
      (fun n => hh.aestronglyMeasurable.mul (hZ n).continuous.aestronglyMeasurable)
      (hh.integrable_mul hz2).norm
    · intro n
      exact Eventually.of_forall fun x => by
        dsimp [Z]
        calc
          ‖h x * (cutoff n x * z x)‖ = ‖h x * z x‖ * ‖cutoff n x‖ := by
            rw [← norm_mul]; congr 1; ring
          _ ≤ ‖h x * z x‖ := mul_le_of_le_one_right (norm_nonneg _) (hcNorm n x)
    · exact Eventually.of_forall fun x => by
        simpa [Z] using tendsto_const_nhds.mul ((cutoff_tendsto x).mul_const (z x))
  obtain ⟨C, hC, hbound, hlim⟩ := cutoff_derivative_bounds (m := m)
  have hr (r : Fin m) : Tendsto
      (fun n => ∫ x, b r x * fderiv ℝ (Z n) x (PiLp.single 2 r (1 : ℝ)) ∂μ) atTop
      (𝓝 (∫ x, b r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)) := by
    let v : E := PiLp.single 2 r (1 : ℝ)
    apply tendsto_integral_of_dominated_convergence
      (fun x => C * ‖v‖ * ‖b r x * z x‖ + ‖b r x * fderiv ℝ z x v‖)
      (fun n => (hb r).aestronglyMeasurable.mul
        (((hZ n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
      (((hb r).integrable_mul hz2).norm.const_mul (C * ‖v‖) |>.add
        ((hb r).integrable_mul (hdz2 r)).norm)
    · intro n
      exact Eventually.of_forall fun x => by
        simp only [Pi.mul_apply]
        change ‖b r x * fderiv ℝ (Z n) x v‖ ≤ _
        rw [hdZ]
        calc
          _ ≤ ‖b r x‖ * (‖fderiv ℝ (cutoff n) x v * z x‖ +
            ‖cutoff n x * fderiv ℝ z x v‖) := by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
          _ ≤ C * ‖v‖ * ‖b r x * z x‖ + ‖b r x * fderiv ℝ z x v‖ := by
            simp only [norm_mul]
            have h1 := hbound n x v
            have h2 := hcNorm n x
            have h3 := norm_nonneg (b r x)
            have h4 := norm_nonneg (z x)
            have h5 := norm_nonneg (fderiv ℝ z x v)
            nlinarith [mul_le_mul_of_nonneg_right h1 h4,
              mul_le_mul_of_nonneg_right h2 h5]
    · exact Eventually.of_forall fun x => by
        simp_rw [hdZ]
        simpa using (tendsto_const_nhds (x := b r x)).mul
          (((hlim x v).mul_const (z x)).add ((cutoff_tendsto x).mul_const (fderiv ℝ z x v)))
  have hseq (n : ℕ) := hw (Z n) (hZ n) (cutoff_compact n).mul_right
  exact tendsto_nhds_unique hl ((tendsto_finsetSum _ fun r _ => hr r).congr (fun n => (hseq n).symm))

end Submission.Obl.Entropy__gaussian_covariance_variational
