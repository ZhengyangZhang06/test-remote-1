import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianPotentialRegularity
import Submission.Obl.Entropy__smooth_gaussian_transport.BoundedSmoothing

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The global Schauder estimate for compact C² functions, with explicit
constants furnished by Gaussian moments. -/
theorem hessian_holder_of_laplacian_holder {m : ℕ} {f : E m → ℝ} {M C α : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ M) (hα : 0 < α) (hα1 : α < 1)
    (hmod : ∀ x y, |laplacian f x - laplacian f y| ≤ C * ‖x - y‖ ^ α)
    (x y : E m) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
      (M * (gaussianHolderMoment m 3 0 + 2 * gaussianHolderMoment m 2 0) +
        C * (2 * gaussianHolderMoment m 2 α / α + gaussianHolderMoment m 3 α / (1 - α))) * ‖x - y‖ ^ α := by
  have hg := laplacian_continuous hf
  have hgc := laplacian_hasCompactSupport hfc
  obtain ⟨hP, hPD⟩ := gaussianPotential_contDiff_two hα hα1.le hC hg hgc hmod
  have hS : ContDiff ℝ 2 (gaussianSmoothing 1 f) :=
    (gaussianSmoothing_contDiff 1 hf.continuous.locallyIntegrable hfc).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))
  have he : f = gaussianSmoothing 1 f - gaussianPotential (laplacian f) :=
    funext (gaussian_heat_representation hf hfc)
  have hD (z : E m) : iteratedFDeriv ℝ 2 f z =
      iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) z - gaussianPotentialHessian (laplacian f) z := by
    calc
      _ = iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f - gaussianPotential (laplacian f)) z := congrArg (fun u => iteratedFDeriv ℝ 2 u z) he
      _ = _ := by rw [iteratedFDeriv_sub_apply hS.contDiffAt hP.contDiffAt, hPD]
  have hSbound := gaussianSmoothing_one_hessian_holder hf.continuous hfc hM hb hα hα1.le x y
  have hPbound := gaussianPotentialHessian_holder hα hα1 hC hg hgc hmod x y
  rw [hD x, hD y]
  have halg : (iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) x - gaussianPotentialHessian (laplacian f) x) -
      (iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) y - gaussianPotentialHessian (laplacian f) y) =
      (iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) x - iteratedFDeriv ℝ 2 (gaussianSmoothing 1 f) y) -
        (gaussianPotentialHessian (laplacian f) x - gaussianPotentialHessian (laplacian f) y) := by abel
  rw [halg]
  exact (norm_sub_le _ _).trans ((add_le_add hSbound hPbound).trans_eq (by ring))

theorem exists_laplacian_schauder_constant (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : E m → ℝ) (M C : ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ M → 0 ≤ C →
      (∀ x, ‖f x‖ ≤ M) →
      (∀ x y, |laplacian f x - laplacian f y| ≤ C * ‖x - y‖ ^ α) →
      ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
        K * (M + C) * ‖x - y‖ ^ α := by
  let A : ℝ := gaussianHolderMoment m 3 0 + 2 * gaussianHolderMoment m 2 0
  let B : ℝ := 2 * gaussianHolderMoment m 2 α / α + gaussianHolderMoment m 3 α / (1 - α)
  have hA : 0 ≤ A := by
    have h2 := gaussianHolderMoment_nonneg m 2 0
    have h3 := gaussianHolderMoment_nonneg m 3 0
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by
    have h2 := gaussianHolderMoment_nonneg m 2 α
    have h3 := gaussianHolderMoment_nonneg m 3 α
    have hh : 0 < 1 - α := by linarith
    dsimp only [B]
    positivity
  refine ⟨A + B + 1, by linarith, ?_⟩
  intro f M C hf hfc hM hC hb hmod x y
  have hh := hessian_holder_of_laplacian_holder hf hfc hM hC hb hα hα1 hmod x y
  apply hh.trans
  change (M * A + C * B) * ‖x - y‖ ^ α ≤ _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
  nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
