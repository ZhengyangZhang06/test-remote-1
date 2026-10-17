import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientConvergence

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem tendstoUniformly_clm_cutoff {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {l : Filter ι} {F : ι → X → Y} {g : X → Y} {K : Set X} {T : X → Y →L[ℝ] Z}
    (hF : TendstoUniformlyOn F g l K) (hK : IsCompact K) (hT : Continuous T)
    (hzero : ∀ x, x ∉ K → T x = 0) :
    TendstoUniformly (fun i x => T x (F i x)) (fun x => T x (g x)) l := by
  obtain ⟨M, hM, hb⟩ := (hK.image hT).isBounded.exists_pos_norm_le
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF (ε / (M + 1)) (by positivity)] with i hi
  intro x
  by_cases hx : x ∈ K
  · rw [dist_eq_norm, ← map_sub]
    have hMx : ‖T x‖ ≤ M := hb _ (mem_image_of_mem _ hx)
    have hh : ‖g x - F i x‖ < ε / (M + 1) := by simpa only [dist_eq_norm] using hi x hx
    calc
      _ ≤ ‖T x‖ * ‖g x - F i x‖ := (T x).le_opNorm _
      _ ≤ (M + 1) * ‖g x - F i x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hh (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  · simpa only [hzero x hx, zero_apply, dist_self] using hε

theorem fderiv_directional_derivative {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 2 f) (v x : X) :
    fderiv ℝ (fun z => fderiv ℝ f z v) x = fderiv ℝ (fderiv ℝ f) x v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh := ((ContinuousLinearMap.apply ℝ Y v).hasFDerivAt.comp x (hd.differentiable_one x).hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hh
  rw [hh]
  apply ContinuousLinearMap.ext
  intro w
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) w v

/-- Local uniform convergence of the zeroth and first quotient jets gives
global C¹ convergence after multiplication by a fixed compact cutoff. -/
theorem cutoff_quotient_fderiv_tendstoUniformly {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f χ : X → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {h : ℕ → ℝ} (v : X)
    (h0 : TendstoUniformlyOn (fun n => directionalQuotient f (h n) v)
      (fun x => fderiv ℝ f x v) atTop (tsupport χ))
    (h1 : TendstoUniformlyOn (fun n => directionalQuotient (fderiv ℝ f) (h n) v)
      (fun x => fderiv ℝ (fderiv ℝ f) x v) atTop (tsupport χ)) :
    TendstoUniformly (fun n => fderiv ℝ (fun x => χ x * directionalQuotient f (h n) v x))
      (fderiv ℝ (fun x => χ x * fderiv ℝ f x v)) atTop := by
  let T₁ : X → (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
    fun x => χ x • ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ)
  let T₀ : X → ℝ →L[ℝ] (X →L[ℝ] ℝ) :=
    fun x => (ContinuousLinearMap.id ℝ ℝ).smulRight (fderiv ℝ χ x)
  have hT₁ : Continuous T₁ := hχ.continuous.smul continuous_const
  have hT₀ : Continuous T₀ := ((ContinuousLinearMap.smulRightL ℝ ℝ (X →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)).continuous).comp (hχ.continuous_fderiv (by norm_num))
  have hz₁ (x : X) (hx : x ∉ tsupport χ) : T₁ x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [T₁, image_eq_zero_of_notMem_tsupport hx]
  have hz₀ (x : X) (hx : x ∉ tsupport χ) : T₀ x = 0 := by
    simp only [T₀, fderiv_of_notMem_tsupport ℝ hx, ContinuousLinearMap.smulRight_zero]
  have hU₁ := tendstoUniformly_clm_cutoff h1 hχc hT₁ hz₁
  have hU₀ := tendstoUniformly_clm_cutoff h0 hχc hT₀ hz₀
  have hreg : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).clm_apply contDiff_const
  have he (n : ℕ) : fderiv ℝ (fun x => χ x * directionalQuotient f (h n) v x) =
      fun x => T₁ x (directionalQuotient (fderiv ℝ f) (h n) v x) +
        T₀ x (directionalQuotient f (h n) v x) := by
    funext x
    rw [fderiv_fun_mul (hχ.differentiable_one x)
      ((directionalQuotient_contDiff hf (h n) v).differentiable (by norm_num) x),
      directionalQuotient_fderiv (hf.differentiable (by norm_num))]
    rfl
  have he' : fderiv ℝ (fun x => χ x * fderiv ℝ f x v) =
      fun x => T₁ x (fderiv ℝ (fderiv ℝ f) x v) + T₀ x (fderiv ℝ f x v) := by
    funext x
    rw [fderiv_fun_mul (hχ.differentiable_one x) (hreg.differentiable_one x), fderiv_directional_derivative hf]
    rfl
  simp only [he, he']
  convert! hU₁.add hU₀ using 1

end Submission.Obl.Entropy__smooth_gaussian_transport
