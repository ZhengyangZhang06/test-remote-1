import Submission.Obl.Entropy__smooth_gaussian_transport.LinearRegularity
import Submission.Obl.Entropy__smooth_gaussian_transport.LogEquationDerivative
import Submission.Obl.Entropy__smooth_gaussian_transport.TransportThirdHolder

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem smooth_finite_order {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) (n : ℕ) :
    ContDiff ℝ n f :=
  hf.of_le (WithTop.coe_le_coe.mpr (le_top : (n : ENat) ≤ ⊤))

theorem transport_smooth_from_third_holder {m : ℕ} {φ U V : E m → ℝ}
    (hφ : ContDiff ℝ 3 φ)
    (hU : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) U)
    (hV : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V)
    (hpos : ∀ x, (operatorMatrix (fderiv ℝ (gradient φ) x)).PosDef)
    (heq : ∀ x, Real.log (fderiv ℝ (gradient φ) x).det = U x + V (gradient φ x))
    (hthird : ∀ x, ∃ α : ℝ, 0 < α ∧ α < 1 ∧ HolderRegularAt 3 α φ x) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨α, hα, hα1, hstart⟩ := hthird x
  let A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun y => principalHessian (fderiv ℝ (gradient φ) y)
  let q : E m → ℝ := fun y => U y + V (gradient φ y)
  have heqD (v : E m) : ∀ᶠ y in nhds x,
      A y (iteratedFDeriv ℝ 2 (fun z => fderiv ℝ φ z v) y) = fderiv ℝ q y v :=
    Filter.Eventually.of_forall (differentiate_log_det_equation hφ hpos heq v)
  have hnormal : ∃ L : E m ≃L[ℝ] E m, ∀ B, A x (untransformHessian L B) = hessianTrace m B := by
    obtain ⟨L, hL⟩ := exists_principal_hessian_normalizer (hpos x)
    exact ⟨L, hL⟩
  have hall (k : ℕ) : HolderRegularAt (k + 3) α φ x := by
    induction k with
    | zero => exact hstart
    | succ k ih =>
      have hH : HolderRegularAt (k + 1) α (iteratedFDeriv ℝ 2 φ) x :=
        ih.iteratedFDeriv (k := k + 1) (n := 2) hα.le hα1.le
      have hOp : HolderRegularAt (k + 1) α (fderiv ℝ (gradient φ)) x := by
        have hh := hH.mapCLM hα.le hα1.le (hessianOperator m)
        have he : (fun y => hessianOperator m (iteratedFDeriv ℝ 2 φ y)) = fderiv ℝ (gradient φ) :=
          funext (hessianOperator_iteratedFDeriv (hφ.of_le (by norm_num)))
        rwa [he] at hh
      have hA : HolderRegularAt (k + 1) α A x :=
        hOp.comp_smooth hα.le hα1.le (principalHessian_contDiffAt
          (by simpa only [operatorMatrix_det] using (hpos x).det_pos.ne'))
      have hgrad : HolderRegularAt (k + 2) α (gradient φ) x := by
        have hd : HolderRegularAt ((k + 2) + 1) α φ x := ih
        convert! hd.fderiv.mapCLM hα.le hα1.le
          (InnerProductSpace.toDual ℝ (E m)).symm.toContinuousLinearEquiv.toContinuousLinearMap using 1
      have hq : HolderRegularAt (k + 2) α q x :=
        (HolderRegularAt.of_contDiffAt (smooth_finite_order hU (k + 3)).contDiffAt hα.le hα1.le).add
          (hgrad.comp_smooth hα.le hα1.le (smooth_finite_order hV (k + 3)).contDiffAt) hα.le hα1.le
      change HolderRegularAt ((k + 3) + 1) α φ x
      apply HolderRegularAt.of_directional_derivatives hα.le hα1.le
        (Filter.Eventually.of_forall (fun y => hφ.differentiable (by norm_num) y))
      intro v
      have hu : HolderRegularAt 2 α (fun y => fderiv ℝ φ y v) x :=
        hstart.fderiv.mapCLM hα.le hα1.le (ContinuousLinearMap.apply ℝ ℝ v)
      have hg : HolderRegularAt (k + 1) α (fun y => fderiv ℝ q y v) x :=
        hq.fderiv.mapCLM hα.le hα1.le (ContinuousLinearMap.apply ℝ ℝ v)
      exact linear_schauder_bootstrap hα hα1 (k + 1) hu hg hA hnormal (heqD v)
  apply contDiffAt_infty.mpr
  intro n
  exact ((hall n).of_order_le hα.le hα1.le (by omega)).contDiffAt

end Submission.Obl.Entropy__smooth_gaussian_transport
