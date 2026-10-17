import Submission.Obl.Entropy__smooth_gaussian_transport.HolderRegularCalculus
import Submission.Obl.Entropy__smooth_gaussian_transport.LocalDerivativeCriterion

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem UniformHolderAt.clm_apply_iff {X Y Z : Type*}
    [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {α : ℝ} {x : X} :
    UniformHolderAt α f x ↔ ∀ v, UniformHolderAt α (fun y => f y v) x := by
  refine ⟨fun hf v => hf.mapCLM (ContinuousLinearMap.apply ℝ Z v), fun h => ?_⟩
  let d := Module.finrank ℝ Y
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : Z ≃L[ℝ] Z)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have hh : (fun p : X × X => e₂ (f p.1 - f p.2)) =O[nhds (x, x)] (fun p => ‖p.1 - p.2‖ ^ α) := by
    rw [Asymptotics.isBigO_pi]
    intro i
    convert! h (e₁.symm (Pi.single i 1)) using 1
  exact (e₂.isBigO_comp_rev (fun p : X × X => f p.1 - f p.2) (nhds (x, x))).trans hh

theorem HolderRegularAt.mapCLM {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {n : ℕ} {α : ℝ} {x : X}
    (hf : HolderRegularAt n α f x) (hα : 0 ≤ α) (hα1 : α ≤ 1) (L : Y →L[ℝ] Z) :
    HolderRegularAt n α (fun y => L (f y)) x := hf.comp_smooth hα hα1 L.contDiff.contDiffAt

theorem HolderRegularAt.clm_apply {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {g : X → Y} {n : ℕ} {α : ℝ} {x : X}
    (hf : HolderRegularAt n α f x) (hg : HolderRegularAt n α g x)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt n α (fun y => f y (g y)) x :=
  (hf.prodMk hg).comp_smooth hα hα1 (contDiffAt_fst.clm_apply contDiffAt_snd)

theorem HolderRegularAt.congr {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : X → Y} {n : ℕ} {α : ℝ} {x : X}
    (hf : HolderRegularAt n α f x) (he : f =ᶠ[nhds x] g) : HolderRegularAt n α g x :=
  ⟨hf.contDiffAt.congr_of_eventuallyEq he.symm, hf.holder.congr (he.iteratedFDeriv ℝ n)⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
