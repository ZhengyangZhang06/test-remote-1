/-
Adapted from: here:o006

Original proofs by session x0062.
-/

import Submission.Lib.EntropyRemainder.WeakDivergence
import Submission.Lib.EntropyRemainder.CompactApprox

/-! # C1 test functions for Gaussian weak divergence -/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

/-- Mollification upgrades a compactly supported C1 function to an admissible test. -/
theorem weak_divergence_c1_compact {m : ℕ} {μ : Measure (E m)}
    {F : E m → ℝ} {v : Fin m → E m → ℝ}
    (hF : Integrable F μ) (hv : ∀ r, Integrable (v r) μ)
    (hweak : ∀ z : E m → ℝ,
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
      (∫ x, F x * z x ∂μ) =
        ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)
    {z : E m → ℝ} (hz : ContDiff ℝ 1 z) (hzc : HasCompactSupport z) :
    (∫ x, F x * z x ∂μ) =
      ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ := by
  obtain ⟨C₀, C₁, h₀, h₁⟩ := compactApprox_bounds hz hzc
  have hleft : Tendsto (fun n => ∫ x, F x * compactApprox n z x ∂μ) atTop
      (𝓝 (∫ x, F x * z x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖ * C₀)
    · intro n
      exact hF.aestronglyMeasurable.mul (compactApprox_contDiff n hz.continuous).continuous.aestronglyMeasurable
    · exact hF.norm.mul_const C₀
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h₀ n x) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (compactApprox_tendsto hz.continuous x).const_mul (F x)
  have hright : Tendsto (fun n => ∑ r, ∫ x, v r x *
      fderiv ℝ (compactApprox n z) x (PiLp.single 2 r (1 : ℝ)) ∂μ) atTop
      (𝓝 (∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)) := by
    apply tendsto_finsetSum
    intro r _
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖v r x‖ * (C₁ * ‖(PiLp.single 2 r (1 : ℝ) : E m)‖))
    · intro n
      exact (hv r).aestronglyMeasurable.mul
        (((compactApprox_contDiff n hz.continuous).continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable
    · exact (hv r).norm.mul_const _
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (h₁ n x) (norm_nonneg _))
    · exact Eventually.of_forall fun x =>
        (((ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 r (1 : ℝ) : E m)).continuous.tendsto
          (fderiv ℝ z x)).comp (compactApprox_fderiv_tendsto hz hzc x)).const_mul (v r x)
  have he := funext fun n => hweak (compactApprox n z)
    (compactApprox_contDiff n hz.continuous) (compactApprox_hasCompactSupport n hzc)
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Compact smooth tests determine the pairing against every C1 H1 function. -/
theorem weak_divergence_c1_test {m : ℕ} {μ : Measure (E m)} [IsFiniteMeasure μ]
    {F : E m → ℝ} {v : Fin m → E m → ℝ}
    (hF : MemLp F 2 μ) (hv : ∀ r, MemLp (v r) 2 μ)
    (hweak : ∀ z : E m → ℝ,
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
      (∫ x, F x * z x ∂μ) =
        ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)
    {z : E m → ℝ} (hz : ContDiff ℝ 1 z) (hzL : MemLp z 2 μ)
    (hzD : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 μ) :
    (∫ x, F x * z x ∂μ) =
      ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ := by
  apply weak_divergence_test_of_compact_test (k := 1) (by norm_num) hF hv _ hz hzL hzD
  intro w hw hwc
  exact weak_divergence_c1_compact (hF.integrable (by norm_num))
    (fun r => (hv r).integrable (by norm_num)) hweak hw hwc

/-- C1 functional-calculus fields can be tested without any higher regularity premise. -/
theorem WeakDivergence.c1_test {m : ℕ} {F : E m → Mat m} {v : Fin m → E m → Mat m}
    (h : WeakDivergence F v) (hF : SquareIntegrable F) (hv : ∀ r, SquareIntegrable (v r))
    {z : E m → ℝ} (hz : ContDiff ℝ 1 z) (hzL : MemLp z 2 (stdGaussian (E m)))
    (hzD : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))
      2 (stdGaussian (E m))) (i j : Fin m) :
    expectation (fun x => F x i j * z x) =
      ∑ r, expectation (fun x => v r x i j *
        fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) :=
  weak_divergence_c1_test (hF i j) (fun r => hv r i j) (h i j) hz hzL hzD

end Submission.Lib.EntropyRemainder
