import Submission.Obl.Entropy__smooth_gaussian_transport.HolderDerivatives

open Set Filter Asymptotics
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem UniformHolderAt.comp_linear {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z]
    {f : Y → Z} {α : ℝ} (hα : 0 ≤ α) (L : X →L[ℝ] Y) (x : X)
    (hf : UniformHolderAt α f (L x)) : UniformHolderAt α (fun y => f (L y)) x := by
  have hcont : Tendsto (fun p : X × X => (L p.1, L p.2)) (nhds (x, x)) (nhds (L x, L x)) :=
    ((L.continuous.comp continuous_fst).prodMk (L.continuous.comp continuous_snd)).tendsto (x, x)
  have hh := hf.comp_tendsto hcont
  apply hh.trans
  apply Asymptotics.IsBigO.of_bound (‖L‖ ^ α)
  apply Filter.Eventually.of_forall
  intro p
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have he : ‖L p.1 - L p.2‖ ≤ ‖L‖ * ‖p.1 - p.2‖ := by rw [← map_sub]; exact L.le_opNorm _
  exact (Real.rpow_le_rpow (norm_nonneg _) he hα).trans_eq (Real.mul_rpow (norm_nonneg _) (norm_nonneg _))

theorem iteratedFDeriv_comp_equiv {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X ≃L[ℝ] Y) (f : Y → Z) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n (fun y => f (L y)) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L.toContinuousLinearMap) := by
  have h := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (L x)) n
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  convert! h using 1

theorem HolderRegularAt.comp_linearEquiv {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z} {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (L : X ≃L[ℝ] Y) (x : X)
    (hf : HolderRegularAt n α f (L x)) : HolderRegularAt n α (fun y => f (L y)) x := by
  refine ⟨hf.contDiffAt.comp x L.contDiff.contDiffAt, ?_⟩
  have hh := (hf.holder.comp_linear hα L.toContinuousLinearMap x).mapCLM
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := Z) (fun _ : Fin n => L.toContinuousLinearMap))
  convert! hh using 1
  funext y
  exact iteratedFDeriv_comp_equiv L f n y

end Submission.Obl.Entropy__smooth_gaussian_transport
