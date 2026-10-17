import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.ConvolutionLimit
import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit.LocalL1
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.continuous_jacobian_of_l2_limit`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__continuous_jacobian_of_l2_limit`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__continuous_jacobian_of_l2_limit/`
belong to this obligation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Convolution
open Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

theorem Submission.Entropy.continuous_jacobian_of_l2_limit : ∀ m : ℕ, ∀ Fseq : ℕ → (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ F : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ∀ J : (EuclideanSpace ℝ (Fin m)) → ((EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m))), (∀ n, ContDiff ℝ 1 (Fseq n)) → (∀ n, MeasureTheory.MemLp (Fseq n) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) → MeasureTheory.MemLp F 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → (∀ n, MeasureTheory.MemLp (fderiv ℝ (Fseq n)) 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) → MeasureTheory.MemLp J 2 (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) → Continuous J → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖Fseq n x - F x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → (Filter.Tendsto (fun n => MeasureTheory.integral (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) (fun x => ‖fderiv ℝ (Fseq n) x - J x‖ ^ 2)) Filter.atTop (nhds (0 : ℝ))) → ∃ G : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)), ContDiff ℝ 1 G ∧ Filter.EventuallyEq (MeasureTheory.ae (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) G F ∧ (∀ x, fderiv ℝ G x = J x) := by
  intro m Fseq F J hC hFn hF hDn hJ hJc hlim hdlim
  have hFloc : LocallyIntegrable F volume :=
    locallyIntegrable_of_integrable_gaussian (hF.integrable (by norm_num))
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) := fun n =>
    { rIn := (1 / ((n : ℝ) + 1)) / 2
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    filter_upwards with n
    dsimp [φ]
    linarith
  have hae : ∀ᵐ x ∂volume,
      Tendsto (fun n => mollify (φ n) F x) atTop (𝓝 (F x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφratio hFloc
  have hd : ∀ n x, HasFDerivAt (mollify (φ n) F) (mollify (φ n) J x) x := by
    intro n x
    exact mollify_limit_hasFDerivAt (φ n) hC hFloc hJc
      (localL1_of_gaussianL2 hFn hF hlim) (localL1_of_gaussianL2 hDn hJ hdlim) x
  obtain ⟨G, hGc, hGF, hGd⟩ := representative_of_locally_uniform_derivatives hd hJc
    (mollify_tendstoLocallyUniformly hφ hJc) hae
  exact ⟨G, hGc, gaussian_absolutelyContinuous_volume.ae_eq hGF, hGd⟩
