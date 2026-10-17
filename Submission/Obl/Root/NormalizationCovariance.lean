import Submission.Obl.Root.GaussianCovarianceUpper

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Submission.Obl.Root.GaussianCovariance

open Submission.Lib.EntropyTools Submission.Lib.GaussianTransport

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ

/-- A zero of the normalization map has a fixed positive covariance floor. -/
theorem covariance_floor_of_normalization
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F γ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {A : E → Mat} (hA : ∀ x, (A x).IsHermitian)
    (hAi : Integrable A γ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) γ)
    (hJ : ∀ i j, MemLp (fun x => cfc gaussianHazard (A x) i j) 2 γ)
    (hJF : ∀ x i j, cfc gaussianHazard (A x) i j =
      (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (hmean : ∀ i j, (∫ x, A x i j ∂γ) = 0) :
    gaussianHazard 0 ^ 2 • (1 : Mat) ≤ densityCovariance f (∫ x, f x • x) := by
  have hm := matrix_integral_eq_zero_of_entries hAi hmean
  have ha : ∀ᵐ x ∂γ, (A x).IsHermitian := Filter.Eventually.of_forall hA
  have hB := integral_gaussianHazard_posDef_of_mean_zero ha hAi hqi hm
  have he : (∫ x, cfc gaussianHazard (A x) ∂γ) =
      (Matrix.of fun i j => ∫ x, cfc gaussianHazard (A x) i j ∂γ) := by
    ext i j
    exact matrix_integral_apply hqi i j
  have hg := mean_jacobian_gram_le_covariance hf0 hf hf2 hF hlaw hJ hJF
  rw [← he, show (∫ x, cfc gaussianHazard (A x) ∂γ).transpose =
      (∫ x, cfc gaussianHazard (A x) ∂γ) by simpa using hB.isHermitian.eq,
    ← pow_two] at hg
  exact (integral_gaussianHazard_sq_ge_of_mean_zero ha hAi hqi hm).trans hg

/-- The affine upper hazard bound controls the trace of the mean Jacobian. -/
theorem mean_trace_le_of_normalization
    {A : E → Mat} (hA : ∀ x, (A x).IsHermitian)
    (hAi : Integrable A γ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) γ)
    (hmean : ∀ i j, (∫ x, A x i j ∂γ) = 0) {l : ℝ}
    (hl : ∀ x, ∀ a ∈ spectrum ℝ (A x), l ≤ a) :
    (∫ x, (cfc gaussianHazard (A x)).trace ∂γ) ≤
      (m : ℝ) * (gaussianHazard l - l) := by
  have h := integral_gaussianHazard_le_of_mean_zero
    (Filter.Eventually.of_forall hA) hAi hqi
    (matrix_integral_eq_zero_of_entries hAi hmean) (Filter.Eventually.of_forall hl)
  have ht := (Matrix.le_iff.mp h).trace_nonneg
  have he : (∫ x, (cfc gaussianHazard (A x)).trace ∂γ) =
      (∫ x, cfc gaussianHazard (A x) ∂γ).trace := by
    exact ((Matrix.traceLinearMap (Fin m) ℝ ℝ).toContinuousLinearMap.integral_comp_comm hqi)
  rw [he]
  simpa [Matrix.trace_sub, Matrix.trace_smul, sub_nonneg, mul_comm] using ht

/-- The upper covariance bound used to keep normalization zeros bounded. -/
theorem covariance_ceiling_of_normalization
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F γ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {A : E → Mat} (hA : ∀ x, (A x).IsHermitian)
    (hAi : Integrable A γ) (hqi : Integrable (fun x => cfc gaussianHazard (A x)) γ)
    (hJ : ∀ i j, MemLp (fun x => cfc gaussianHazard (A x) i j) 2 γ)
    (hJF : ∀ x i j, cfc gaussianHazard (A x) i j =
      (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (hmean : ∀ i j, (∫ x, A x i j ∂γ) = 0) {l L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x, ∀ a ∈ spectrum ℝ (A x), l ≤ a)
    (hbound : ∀ x, cfc gaussianHazard (A x) ≤ L • (1 : Mat)) :
    (densityCovariance f (∫ x, f x • x)).trace ≤
      L * ((m : ℝ) * (gaussianHazard l - l)) := by
  have hpos (x : E) : (cfc gaussianHazard (A x)).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun a _ => (gaussianHazard_pos a).le))
  exact (trace_covariance_le_bound_mul_mean_trace hf0 hf hf2 hF hlaw hJ hJF hpos hbound).trans
    (mul_le_mul_of_nonneg_left (mean_trace_le_of_normalization hA hAi hqi hmean hl) hL)

end Submission.Obl.Root.GaussianCovariance
