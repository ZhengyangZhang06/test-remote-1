import Submission.Obl.Entropy__normalized_remainder.SmoothCutoff
import Submission.Obl.Entropy__normalized_remainder.Interfaces

/-!
# Extending the weak divergence identity beyond compact tests

Smooth cutoffs extend the distributional identity to any smooth test whose
value and coordinate derivatives are square-integrable. No boundedness
assumption on the test is necessary.
-/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__normalized_remainder

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

lemma integrable_mul_smoothCutoff {m : ℕ} {μ : Measure (E m)} {f : E m → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (fun x => f x * smoothCutoff n x) μ :=
  hf.mul_bdd (smoothCutoff_contDiff n (k := 1)).continuous.aestronglyMeasurable
    (Eventually.of_forall (smoothCutoff_norm_le n))

lemma integral_mul_smoothCutoff_tendsto {m : ℕ} {μ : Measure (E m)} {f : E m → ℝ}
    (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, f x * smoothCutoff n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (integrable_mul_smoothCutoff hf n).aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (smoothCutoff_norm_le n x)
  · exact Eventually.of_forall fun x => by
      simpa using (smoothCutoff_tendsto x).const_mul (f x)

lemma integrable_mul_fderiv_smoothCutoff {m : ℕ} {μ : Measure (E m)} {f : E m → ℝ}
    (hf : Integrable f μ) (n : ℕ) (v : E m) :
    Integrable (fun x => f x * fderiv ℝ (smoothCutoff n) x v) μ := by
  obtain ⟨C, _, hC⟩ := fderiv_smoothCutoff_bound m
  apply hf.mul_bdd
    (((smoothCutoff_contDiff n (k := 1)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).aestronglyMeasurable
  exact Eventually.of_forall fun x => hC n x v

lemma integral_mul_fderiv_smoothCutoff_tendsto {m : ℕ} {μ : Measure (E m)} {f : E m → ℝ}
    (hf : Integrable f μ) (v : E m) :
    Tendsto (fun n => ∫ x, f x * fderiv ℝ (smoothCutoff n) x v ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := fderiv_smoothCutoff_bound m
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n x => f x * fderiv ℝ (smoothCutoff n) x v)
    (f := fun _ => (0 : ℝ)) (fun x => ‖f x‖ * (C * ‖v‖))
    (fun n => (integrable_mul_fderiv_smoothCutoff hf n v).aestronglyMeasurable)
    (hf.norm.mul_const _) (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC n x v) (norm_nonneg _))
    (Eventually.of_forall fun x => by
      simpa using (fderiv_smoothCutoff_tendsto x v).const_mul (f x))
  simpa only [integral_zero] using ht

/-- Density of compact tests in the smooth Gaussian H1 class, at the level of pairings. -/
theorem weak_divergence_smooth_test {m : ℕ} {μ : Measure (E m)}
    {F : E m → ℝ} {v : Fin m → E m → ℝ}
    (hF : MemLp F 2 μ) (hv : ∀ r, MemLp (v r) 2 μ)
    (hweak : ∀ z : E m → ℝ,
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
      (∫ x, F x * z x ∂μ) =
        ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)
    {z : E m → ℝ} (hz : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z)
    (hzL : MemLp z 2 μ)
    (hzD : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 μ) :
    (∫ x, F x * z x ∂μ) =
      ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ := by
  let zn (n : ℕ) (x : E m) := z x * smoothCutoff n x
  have hzn (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (zn n) :=
    hz.mul (smoothCutoff_contDiff n)
  have hzc (n : ℕ) : HasCompactSupport (zn n) := (smoothCutoff_hasCompactSupport n).mul_left
  have hleft : Tendsto (fun n => ∫ x, F x * zn n x ∂μ) atTop
      (𝓝 (∫ x, F x * z x ∂μ)) := by
    simpa only [zn, Pi.mul_apply, mul_assoc] using! integral_mul_smoothCutoff_tendsto (hF.integrable_mul hzL)
  have hexpand (n : ℕ) (x e : E m) : fderiv ℝ (zn n) x e =
      fderiv ℝ z x e * smoothCutoff n x + z x * fderiv ℝ (smoothCutoff n) x e := by
    have hd := hz.differentiable (by simp)
    have hc := (smoothCutoff_contDiff (m := m) n (k := 1)).differentiable (by norm_num)
    dsimp [zn]
    erw [fderiv_mul (hd x) (hc x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hright : Tendsto (fun n => ∑ r, ∫ x, v r x *
      fderiv ℝ (zn n) x (PiLp.single 2 r (1 : ℝ)) ∂μ) atTop
      (𝓝 (∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂μ)) := by
    apply tendsto_finsetSum
    intro r _
    have hi₁ := (hv r).integrable_mul (hzD r)
    have hi₂ := (hv r).integrable_mul hzL
    have he (n : ℕ) : (∫ x, v r x * fderiv ℝ (zn n) x (PiLp.single 2 r (1 : ℝ)) ∂μ) =
        (∫ x, (v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) * smoothCutoff n x ∂μ) +
        (∫ x, (v r x * z x) * fderiv ℝ (smoothCutoff n) x (PiLp.single 2 r (1 : ℝ)) ∂μ) := by
      simp_rw [hexpand, mul_add, ← mul_assoc]
      exact integral_add (integrable_mul_smoothCutoff hi₁ n)
        (integrable_mul_fderiv_smoothCutoff hi₂ n _)
    simp_rw [he]
    simpa only [add_zero] using! (integral_mul_smoothCutoff_tendsto hi₁).add
      (integral_mul_fderiv_smoothCutoff_tendsto hi₂ (PiLp.single 2 r (1 : ℝ)))
  have he := funext (fun n => hweak (zn n) (hzn n) (hzc n))
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The frozen matrix weak-divergence interface admits all smooth H1 scalar tests. -/
theorem WeakDivergence.smooth_test {m : ℕ} {F : E m → Mat m} {v : Fin m → E m → Mat m}
    (h : WeakDivergence F v) (hF : SquareIntegrable F) (hv : ∀ r, SquareIntegrable (v r))
    {z : E m → ℝ} (hz : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z)
    (hzL : MemLp z 2 (stdGaussian (E m)))
    (hzD : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))
      2 (stdGaussian (E m))) (i j : Fin m) :
    expectation (fun x => F x i j * z x) =
      ∑ r, expectation (fun x => v r x i j *
        fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) :=
  weak_divergence_smooth_test (hF i j) (fun r => hv r i j) (h i j) hz hzL hzD

end Submission.Obl.Entropy__normalized_remainder
