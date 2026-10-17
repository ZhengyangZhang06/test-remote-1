import Submission.Obl.Root.GaussianCovariance

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

namespace Submission.Obl.Root.GaussianCovariance

open Submission.Lib.EntropyTools
open Submission.Obl.Entropy__gaussian_covariance_variational

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ

/-- Sharp Gaussian Poincare in covariance-trace form. -/
theorem trace_covariance_le_jacobian_energy
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F γ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {J : E → Mat} (hJ : ∀ i j, MemLp (fun x => J x i j) 2 γ)
    (hJF : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i) :
    (densityCovariance f (∫ x, f x • x)).trace ≤
      ∫ x, ((J x).transpose * J x).trace ∂γ := by
  have h := covariance_of_scalar (scalar_covariance_bound m)
    hf0 hf hf2 F hF hlaw J J (fun _ _ => 0) hJ hJF hJ
    (fun _ _ _ => memLp_const 0) (by intros; simp) 1 Matrix.PosDef.one
  simpa using h

/-- On a positive spectral interval, the quadratic energy is bounded by a trace. -/
lemma trace_square_le_scalar_mul_trace {J : Mat} (hJ : J.PosSemidef) {L : ℝ}
    (hL : J ≤ L • (1 : Mat)) : (J * J).trace ≤ L * J.trace := by
  have hupper : ∀ a ∈ spectrum ℝ J, a ≤ L := by
    apply (cfc_le_algebraMap_iff (fun a : ℝ => a) L J
      continuous_id.continuousOn hJ.isHermitian.isSelfAdjoint).mp
    simpa only [cfc_id' ℝ J hJ.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one] using hL
  have hs := (cfc_le_iff (fun a : ℝ => a^2) (fun a : ℝ => L * a) J
    (by fun_prop) (by fun_prop) hJ.isHermitian.isSelfAdjoint).mpr (by
      intro a ha
      have ha0 : 0 ≤ a := spectrum_nonneg_of_nonneg hJ.nonneg ha
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hupper a ha) ha0)
  rw [cfc_pow_id J 2 hJ.isHermitian.isSelfAdjoint,
    cfc_const_mul_id L J hJ.isHermitian.isSelfAdjoint, pow_two] at hs
  have ht := (Matrix.le_iff.mp hs).trace_nonneg
  simpa only [trace_sub, trace_smul, smul_eq_mul, sub_nonneg] using ht

/-- The pointwise Jacobian ceiling and its mean trace bound the target covariance. -/
theorem trace_covariance_le_bound_mul_mean_trace
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F γ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {J : E → Mat} (hJ : ∀ i j, MemLp (fun x => J x i j) 2 γ)
    (hJF : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (hpos : ∀ x, (J x).PosSemidef) {L : ℝ}
    (hbound : ∀ x, J x ≤ L • (1 : Mat)) :
    (densityCovariance f (∫ x, f x • x)).trace ≤
      L * ∫ x, (J x).trace ∂γ := by
  have henergy : Integrable (fun x => ((J x).transpose * J x).trace) γ := by
    simp only [Submission.Lib.MatrixEntropy.trace_transpose_mul]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hJ i j).integrable_mul (hJ i j)
  have htrace : Integrable (fun x => (J x).trace) γ :=
    integrable_finsetSum _ fun i _ => (hJ i i).integrable (by norm_num)
  apply (trace_covariance_le_jacobian_energy hf0 hf hf2 hF hlaw hJ hJF).trans
  rw [← integral_const_mul]
  apply integral_mono henergy (htrace.const_mul L)
  intro x
  change ((J x).transpose * J x).trace ≤ L * (J x).trace
  have hsym : (J x).transpose = J x := by simpa using (hpos x).isHermitian.eq
  rw [hsym]
  exact trace_square_le_scalar_mul_trace (hpos x) (hbound x)

end Submission.Obl.Root.GaussianCovariance
