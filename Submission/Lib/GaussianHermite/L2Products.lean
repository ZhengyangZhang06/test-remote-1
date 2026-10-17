/- Adapted from: here:o022. Original proofs by session x0047. -/
import Mathlib

open MeasureTheory Filter
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

theorem inner_toLp_real {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

theorem integral_mul_sq_le {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [inner_toLp_real, pow_two] using h

theorem memLp_prod_mul {f : α → ℝ} {g : β → ℝ} [SFinite μ] [SFinite ν]
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    ((hf.aestronglyMeasurable.comp_fst).mul (hg.aestronglyMeasurable.comp_snd))).mpr
  convert hf.integrable_sq.mul_prod hg.integrable_sq using 1
  ext z
  exact mul_pow _ _ 2

theorem memLp_section_right [SFinite μ] [SFinite ν] {f : α × β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) : ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with x hx hx2
  exact (memLp_two_iff_integrable_sq hx).mpr hx2

theorem memLp_integral_mul_right [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α × β → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, f (x, y) * g y ∂ν) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun z : α × β => f z * g z.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.mul (hg.comp_snd μ).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas.integral_prod_right').mpr
  apply (hf.integrable_sq.integral_prod_left.mul_const (∫ y, g y ^ 2 ∂ν)).mono'
    (hmeas.integral_prod_right'.pow 2)
  filter_upwards [memLp_section_right hf] with x hx
  change |(∫ y, f (x, y) * g y ∂ν) ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  exact integral_mul_sq_le hx hg

/-- Completeness of two countable scalar L2 systems passes to their products. -/
theorem ae_eq_zero_of_product_system
    {ι κ : Type*} [Countable κ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {u : ι → α → ℝ} {v : κ → β → ℝ}
    (hu : ∀ i, MemLp (u i) 2 μ) (hv : ∀ j, MemLp (v j) 2 ν)
    (huc : ∀ f : α → ℝ, MemLp f 2 μ →
      (∀ i, (∫ x, f x * u i x ∂μ) = 0) → f =ᵐ[μ] 0)
    (hvc : ∀ f : β → ℝ, MemLp f 2 ν →
      (∀ j, (∫ y, f y * v j y ∂ν) = 0) → f =ᵐ[ν] 0)
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (horth : ∀ i j, (∫ z, f z * (u i z.1 * v j z.2) ∂μ.prod ν) = 0) :
    f =ᵐ[μ.prod ν] 0 := by
  have hj (j : κ) : (fun x => ∫ y, f (x,y) * v j y ∂ν) =ᵐ[μ] 0 := by
    apply huc _ (memLp_integral_mul_right hf (hv j))
    intro i
    have hint : Integrable (fun z : α × β => f z * (u i z.1 * v j z.2)) (μ.prod ν) :=
      hf.integrable_mul (memLp_prod_mul (hu i) (hv j))
    have horthij := horth i j
    rw [integral_prod _ hint] at horthij
    convert horthij using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← integral_mul_const]
    congr 1
    ext y
    ring
  have hsections : ∀ᵐ x ∂μ, (fun y => f (x,y)) =ᵐ[ν] 0 := by
    filter_upwards [memLp_section_right hf, ae_all_iff.mpr hj] with x hx hxi
    exact hvc _ hx hxi
  have hm := hf.aestronglyMeasurable
  have he := Measure.ae_ae_of_ae_prod hm.ae_eq_mk
  have heq : hm.mk f =ᵐ[μ.prod ν] 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm.stronglyMeasurable_mk.measurable measurable_const)).mpr
    filter_upwards [hsections, he] with x hx he'
    filter_upwards [hx, he'] with y hy hxy
    exact hxy.symm.trans hy
  exact hm.ae_eq_mk.trans heq

end Submission.Lib.GaussianHermite
