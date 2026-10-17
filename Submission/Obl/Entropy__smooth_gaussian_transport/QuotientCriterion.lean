import Submission.Obl.Entropy__smooth_gaussian_transport.CutoffConvergence
import Submission.Obl.Entropy__smooth_gaussian_transport.SchauderLimit
import Submission.Obl.Entropy__smooth_gaussian_transport.UniformBoundedHolder

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem cutoff_directionalDerivative_contDiff_two {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f χ : X → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    {h : ℕ → ℝ} (v : X) {α : ℝ} (hα : 0 < α)
    (h0 : TendstoUniformlyOn (fun n => directionalQuotient f (h n) v)
      (fun x => fderiv ℝ f x v) atTop (tsupport χ))
    (h1 : TendstoUniformlyOn (fun n => directionalQuotient (fderiv ℝ f) (h n) v)
      (fun x => fderiv ℝ (fderiv ℝ f) x v) atTop (tsupport χ))
    (hbound : UniformBoundedHolder α
      (fun n => iteratedFDeriv ℝ 2 (fun x => χ x * directionalQuotient f (h n) v x))) :
    ContDiff ℝ 2 (fun x => χ x * fderiv ℝ f x v) ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun x => χ x * fderiv ℝ f x v)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hbound
  have hreg : ContDiff ℝ 1 (fun x => χ x * fderiv ℝ f x v) :=
    (hχ.of_le (by norm_num)).mul
      ((hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).clm_apply contDiff_const)
  obtain ⟨hres, hmod⟩ := contDiff_two_of_uniform_limit_hessian_holder
    (fun n => hχ.mul (directionalQuotient_contDiff hf (h n) v)) hreg hC hα
    (cutoff_quotient_fderiv_tendstoUniformly hf (hχ.of_le (by norm_num)) hχc v h0 h1) hm
  have hc : HasCompactSupport (fun x => χ x * fderiv ℝ f x v) := hχc.mul_right
  obtain ⟨N, hN, hNb⟩ := ((hc.iteratedFDeriv 2).isCompact_range
    (hres.continuous_iteratedFDeriv (by norm_num))).isBounded.exists_pos_norm_le
  exact ⟨hres, N, C, hN.le, hC, fun _ x => hNb _ (mem_range_self x), fun _ => hmod⟩

theorem contDiff_three_of_local_directional_derivatives {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ 1 f)
    (hlocal : ∀ x v, ∃ χ : X → ℝ, (∀ᶠ y in nhds x, χ y = 1) ∧
      ContDiff ℝ 2 (fun y => χ y * fderiv ℝ f y v)) : ContDiff ℝ 3 f := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 2)).mpr
  refine ⟨fderiv ℝ f, contDiff_clm_apply_iff.mpr ?_, fun x => (hf.differentiable_one x).hasFDerivAt⟩
  intro v
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨χ, hχ, hreg⟩ := hlocal x v
  apply hreg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hχ] with y hy
  simp only [hy, one_mul]

end Submission.Obl.Entropy__smooth_gaussian_transport
