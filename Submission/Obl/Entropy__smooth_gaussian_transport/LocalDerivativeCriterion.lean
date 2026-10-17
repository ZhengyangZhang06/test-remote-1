import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientCriterion

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem contDiffAt_clm_apply_iff {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {n : WithTop ENat} {x : X} :
    ContDiffAt ℝ n f x ↔ ∀ v, ContDiffAt ℝ n (fun y => f y v) x := by
  refine ⟨fun h v => h.clm_apply contDiffAt_const, fun h => ?_⟩
  let d := Module.finrank ℝ Y
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : Z ≃L[ℝ] Z)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr fun i => h _)

theorem contDiffAt_three_of_local_directional_derivatives {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ 1 f) (x : X)
    (hlocal : ∀ v, ∃ χ : X → ℝ, (∀ᶠ y in nhds x, χ y = 1) ∧
      ContDiff ℝ 2 (fun y => χ y * fderiv ℝ f y v)) : ContDiffAt ℝ 3 f x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 2)).mpr
  refine ⟨fderiv ℝ f, ⟨univ, univ_mem, fun y _ => (hf.differentiable_one y).hasFDerivAt⟩,
    contDiffAt_clm_apply_iff.mpr ?_⟩
  intro v
  obtain ⟨χ, hχ, hreg⟩ := hlocal v
  apply hreg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hχ] with y hy
  simp only [hy, one_mul]

end Submission.Obl.Entropy__smooth_gaussian_transport
