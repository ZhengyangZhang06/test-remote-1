import Submission.Obl.Entropy__smooth_gaussian_transport.HolderLinearChange

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem HolderRegularAt.iteratedFDeriv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {k n : ℕ} {α : ℝ}
    (hf : HolderRegularAt (k + n) α f x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt k α (_root_.iteratedFDeriv ℝ n f) x := by
  induction n generalizing k with
  | zero =>
    simp only [Nat.add_zero] at hf
    rw [iteratedFDeriv_zero_eq_comp]
    exact hf.comp_smooth hα hα1 (continuousMultilinearCurryFin0 ℝ X Y).symm.toContinuousLinearEquiv.contDiff.contDiffAt
  | succ n ih =>
    have hn : HolderRegularAt ((k + 1) + n) α f x := by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    have hder := (ih hn).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left]
    let L : (X →L[ℝ] (X [×n]→L[ℝ] Y)) →L[ℝ] (X [×(n + 1)]→L[ℝ] Y) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) Y).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hLc : ContDiffAt ℝ (k + 1) L (_root_.fderiv ℝ (_root_.iteratedFDeriv ℝ n f) x) := by
      exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := X →L[ℝ] (X [×n]→L[ℝ] Y)) (F := X [×(n + 1)]→L[ℝ] Y) L).contDiffAt
    convert! hder.comp_smooth hα hα1 hLc using 1

theorem HolderRegularAt.sub {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : X → Y} {x : X} {n : ℕ} {α : ℝ}
    (hf : HolderRegularAt n α f x) (hg : HolderRegularAt n α g x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt n α (fun y => f y - g y) x :=
  (hf.prodMk hg).comp_smooth hα hα1 (contDiffAt_fst.sub contDiffAt_snd)

theorem HolderRegularAt.add {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : X → Y} {x : X} {n : ℕ} {α : ℝ}
    (hf : HolderRegularAt n α f x) (hg : HolderRegularAt n α g x) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderRegularAt n α (fun y => f y + g y) x :=
  (hf.prodMk hg).comp_smooth hα hα1 (contDiffAt_fst.add contDiffAt_snd)

end Submission.Obl.Entropy__smooth_gaussian_transport
