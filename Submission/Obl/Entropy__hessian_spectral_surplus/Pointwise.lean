import Submission.Obl.Entropy__hessian_spectral_surplus.MultiplierRotation
import Submission.Obl.Entropy__hessian_spectral_surplus.DiagonalEstimate
import Submission.Obl.Entropy__hessian_spectral_surplus.HessianSymmetry
import Submission.Obl.Entropy__hessian_spectral_surplus.CFCDerivative

open scoped BigOperators
open Matrix

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "E" => EuclideanSpace ℝ n
local notation "∞" => ((⊤ : ENat) : WithTop ENat)
open Submission.Lib.PairEstimate

lemma cfc_inverse_in_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ a, q a ≠ 0) :
    (hA.eigenvectorUnitary : Matrix n n ℝ).transpose * (cfc q A)⁻¹ * hA.eigenvectorUnitary =
      Matrix.diagonal (fun i => (q (hA.eigenvalues i))⁻¹) := by
  rw [Matrix.nonsing_inv_eq_ringInverse,
    ← cfc_inv q A (fun a _ => hq a) (A.finite_real_spectrum.continuousOn q) hA.isSelfAdjoint]
  exact cfc_in_eigenbasis hA _

lemma cfc_rotated_partial {A : E → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : E) (r i j : n) :
    let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
    rotateTensor U (fun s => matrixPartial (fun y => cfc f (A y)) s x) r i j =
      dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        rotateTensor U (fun s => matrixPartial A s x) r i j := by
  dsimp only
  rw [rotateTensor_entry, rotateTensor_entry]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hd := cfc_fderiv_in_eigenbasis hA hAc (hAd x) hf (PiLp.single 2 s (1 : ℝ)) i j
  change _ * ((hA x).eigenvectorUnitary.val.transpose *
    Matrix.of (fun i j => fderiv ℝ (fun y => cfc f (A y) i j) x (PiLp.single 2 s (1 : ℝ))) *
    (hA x).eigenvectorUnitary.val) i j = _
  rw [hd]
  dsimp only [matrixPartial]
  ring

noncomputable def multiplierDensity (J ka : E → Matrix n n ℝ) (x : E) : ℝ :=
  (∑ i, ∑ j, (ka x * ka x) i j *
    Matrix.trace ((J x)⁻¹ * matrixPartial J i x * (J x)⁻¹ * matrixPartial J j x)) +
  ∑ r, ∑ s, (J x)⁻¹ r s *
    Matrix.trace ((matrixPartial ka s x * ka x + ka x * matrixPartial ka s x) * matrixPartial J r x)

lemma pointwise_hessian_estimate {A : E → Matrix n n ℝ}
    (hA : ∀ x, (A x).IsHermitian) (hAc : Continuous A)
    (hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {q k : ℝ → ℝ} (hqdif : Differentiable ℝ q) (hkdif : Differentiable ℝ k)
    (hqpos : ∀ a, 0 < q a) (hqmono : StrictMono q)
    (hqd : ∀ a, deriv q a = q a * (q a - a)) (hgap : ∀ a, q a - a ≠ 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hJ : ∀ x i j, cfc q (A x) i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i)
    (hBs : ∀ a b, secantMultiplier q k a b = secantMultiplier q k b a)
    (hBm : ∀ b, Monotone (fun a => secantMultiplier q k a b))
    (S : ℝ → ℝ → ℝ)
    (hS : ∀ a b, 1 - (dslope k a b) ^ 2 + S a b ≤
      (dslope q a b) ^ 2 * secantMultiplier q k a b / (q a * q b))
    (x : E) :
    (∑ r, ∑ i, ∑ j, matrixPartial A r x i j ^ 2) -
      (∑ r, ∑ i, ∑ j, matrixPartial (fun y => cfc k (A y)) r x i j ^ 2) +
      (∑ r, ∑ i, ∑ j, S ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        (((hA x).eigenvectorUnitary : Matrix n n ℝ).transpose * matrixPartial A r x *
          (hA x).eigenvectorUnitary) i j ^ 2) ≤
      multiplierDensity (fun y => cfc q (A y)) (fun y => cfc k (A y)) x := by
  let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
  let J : E → Matrix n n ℝ := fun y => cfc q (A y)
  let ka : E → Matrix n n ℝ := fun y => cfc k (A y)
  let H : n → Matrix n n ℝ := fun r => matrixPartial J r x
  let Z : n → Matrix n n ℝ := fun r => matrixPartial A r x
  let K : n → Matrix n n ℝ := fun r => matrixPartial ka r x
  have hU : U * U.transpose = 1 := eigenbasis_mul_transpose_self (hA x)
  have hJs : ∀ y, (J y).IsHermitian := fun y => (cfc_predicate q (A y)).isHermitian
  obtain ⟨hH23, hH12⟩ := hessian_partial_symmetries hφ hJs hJ x
  have hT := cfc_rotated_partial hA hAc hAd hqdif x
  have hK' := cfc_rotated_partial hA hAc hAd hkdif x
  have hb := diagonal_multiplier_estimate ((hA x).eigenvalues) q k (secantMultiplier q k) S
    hqpos hqmono.monotone hBs hBm
    (secantMultiplier_coefficient_identity hqmono.injective hqd hgap) hS
    (rotateTensor U H) (rotateTensor U Z) (rotateTensor U K)
    (rotateTensor_symm_first U H hH12) (rotateTensor_symm_last U H hH23) hT hK'
  have hP : U.transpose * (ka x * ka x) * U = Matrix.diagonal (fun i => k ((hA x).eigenvalues i) ^ 2) := by
    have hk : U.transpose * ka x * U = Matrix.diagonal (fun i => k ((hA x).eigenvalues i)) :=
      cfc_in_eigenbasis (hA x) k
    rw [conjugate_mul _ _ _ hU, hk, Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  have hM : U.transpose * (J x)⁻¹ * U = Matrix.diagonal (fun i => (q ((hA x).eigenvalues i))⁻¹) :=
    cfc_inverse_in_eigenbasis (hA x) q (fun a => ne_of_gt (hqpos a))
  have hka : U.transpose * ka x * U = Matrix.diagonal (fun i => k ((hA x).eigenvalues i)) :=
    cfc_in_eigenbasis (hA x) k
  have hR : multiplierDensity J ka x =
      (∑ r, ∑ i, ∑ j, k ((hA x).eigenvalues r) ^ 2 * (q ((hA x).eigenvalues i))⁻¹ *
        (q ((hA x).eigenvalues j))⁻¹ * rotateTensor U H r i j ^ 2) +
      ∑ r, ∑ i, ∑ j, (q ((hA x).eigenvalues r))⁻¹ *
        (k ((hA x).eigenvalues i) + k ((hA x).eigenvalues j)) *
          rotateTensor U K r i j * rotateTensor U H r i j := by
    unfold multiplierDensity
    rw [first_multiplier_rotation U _ _ H hU _ _ hP hM hH23,
      second_multiplier_rotation U _ _ H K hU _ _ hM hka hH23]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hb
  rw [rotateTensor_energy U hU Z, rotateTensor_energy U hU K,
    rotateTensor_weighted_energy U hU Z, ← hR] at hb
  exact hb

end Submission.Obl.Entropy__hessian_spectral_surplus
