import Submission.Obl.Entropy__smooth_gaussian_transport.HolderCutoff
import Submission.Obl.Entropy__smooth_gaussian_transport.CutoffHessian

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem compact_holder_cutoff {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {χ : X → ℝ} {α : ℝ}
    (hf : Continuous f) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hmod : ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    UniformBoundedHolder α (fun (_ : Unit) x => χ x • f x) := by
  obtain ⟨R, hR, hb⟩ := hc.isBounded.exists_pos_norm_le
  let K := Metric.closedBall (0 : X) (R + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M, hM, hMb⟩ := (hK.image hf).isBounded.exists_pos_norm_le
  obtain ⟨C, hC, hmod⟩ := hmod K hK
  apply uniformBoundedHolder_cutoff_bilinear hχ hc hα hα1 (by norm_num : (0 : ℝ) < 1)
    hM.le hC _ (fun (_ : Unit) x hx => hMb _ (mem_image_of_mem _ hx)) (fun (_ : Unit) => hmod)
    (ContinuousLinearMap.lsmul ℝ ℝ)
  intro x hx y hy
  change dist y 0 ≤ R + 1
  rw [dist_zero_right]
  have he : y = x - (x - y) := by abel
  calc
    ‖y‖ = ‖x - (x - y)‖ := congrArg norm he
    _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
    _ ≤ R + 1 := add_le_add (hb x hx) hy.le

theorem compact_hessian_holder_mul {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f χ : X → ℝ} {α : ℝ} (hf : ContDiff ℝ 2 f)
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hmod : ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖ ^ α) :
    UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun x => χ x * f x)) := by
  have hmain := compact_holder_cutoff (hf.continuous_iteratedFDeriv (by norm_num))
    (hχ.of_le (by norm_num)) hc hα hα1 hmod
  have hother : UniformBoundedHolder α
      (fun (_ : Unit) x => f x • iteratedFDeriv ℝ 2 χ x) :=
    .of_compact_c1 ((hf.of_le (by norm_num)).smul (hχ.iteratedFDeriv_right (by norm_num)))
      (hc.iteratedFDeriv 2).smul_left hα hα1
  have hcross : ContDiff ℝ 1 (fun x => productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x)) :=
    ContDiff.comp (f := fun x => (fderiv ℝ χ x, fderiv ℝ f x))
      (productHessianCross_contDiff (X := X) (n := 1))
      ((hχ.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 3)).prodMk
        (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)))
  have hcrossc : HasCompactSupport (fun x => productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hc.fderiv ℝ)
    intro x hx
    apply subset_closure
    contrapose! hx
    simp only [Function.notMem_support] at hx
    rw [Function.notMem_support]
    change productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x) = 0
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [productHessianCross_apply, hx, zero_apply, zero_mul, mul_zero, add_zero]
  convert! (hmain.add hother).add (UniformBoundedHolder.of_compact_c1 hcross hcrossc hα hα1) using 1
  funext i x
  exact iteratedFDeriv_two_mul (hχ.of_le (by norm_num)) hf x

theorem compact_hessian_holder_mul_of_cutoff {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {f χ : X → ℝ} {α : ℝ} (hf : ContDiff ℝ 2 f)
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hmain : UniformBoundedHolder α (fun (_ : Unit) x => χ x • iteratedFDeriv ℝ 2 f x)) :
    UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun x => χ x * f x)) := by
  have hother : UniformBoundedHolder α
      (fun (_ : Unit) x => f x • iteratedFDeriv ℝ 2 χ x) :=
    .of_compact_c1 ((hf.of_le (by norm_num)).smul (hχ.iteratedFDeriv_right (by norm_num)))
      (hc.iteratedFDeriv 2).smul_left hα hα1
  have hcross : ContDiff ℝ 1 (fun x => productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x)) :=
    ContDiff.comp (f := fun x => (fderiv ℝ χ x, fderiv ℝ f x))
      (productHessianCross_contDiff (X := X) (n := 1))
      ((hχ.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 3)).prodMk
        (hf.fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)))
  have hcrossc : HasCompactSupport (fun x => productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hc.fderiv ℝ)
    intro x hx
    apply subset_closure
    contrapose! hx
    simp only [Function.notMem_support] at hx
    rw [Function.notMem_support]
    change productHessianCross (fderiv ℝ χ x) (fderiv ℝ f x) = 0
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [productHessianCross_apply, hx, zero_apply, zero_mul, mul_zero, add_zero]
  convert! (hmain.add hother).add (UniformBoundedHolder.of_compact_c1 hcross hcrossc hα hα1) using 1
  funext i x
  exact iteratedFDeriv_two_mul (hχ.of_le (by norm_num)) hf x

end Submission.Obl.Entropy__smooth_gaussian_transport
