import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__hessian_spectral_surplus.Pointwise
import Submission.Obl.Entropy__hessian_spectral_surplus.Separation
import Submission.Obl.Entropy__hessian_spectral_surplus.Integration
import Submission.Lib.GaussianTransport.GaussianSlope
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.hessian_spectral_surplus`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__hessian_spectral_surplus`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__hessian_spectral_surplus/`
belong to this obligation.
-/

open scoped BigOperators
open MeasureTheory
open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__hessian_spectral_surplus

theorem Submission.Entropy.hessian_spectral_surplus : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) => (fun (L2 : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Prop) => (fun (d : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (J : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (ka : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (H : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (Z : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (K : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (I : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (N : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → ℝ) => (fun (R : (EuclideanSpace ℝ (Fin m)) → ℝ) => (fun (DD : (ℝ → ℝ) → ℝ → ℝ → ℝ) => (fun (B : ℝ → ℝ → ℝ) => (fun (δ : ℝ → ℝ → ℝ) => (fun (σ : ℝ → ℝ → ℝ) => (fun (U : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (S : (EuclideanSpace ℝ (Fin m)) → ℝ) => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → (∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → MeasureTheory.Integrable R γ → (∀ a b : ℝ, B a b = B b a) → (∀ b : ℝ, Monotone (fun a => B a b)) → (∀ a b : ℝ, 1 - (DD k a b)^2 + σ a b ≤ (DD q a b)^2 * B a b / (q a * q b)) → MeasureTheory.Integrable S γ ∧ Finset.sum Finset.univ (fun r : Fin m => N (Z r)) - Finset.sum Finset.univ (fun r : Fin m => N (K r)) + I S ≤ I R) (fun x => Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => σ ((hA x).eigenvalues i) ((hA x).eigenvalues j) * ((U x).transpose * Z r x * U x) i j ^ 2))))) (fun x => ((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))) (fun a b : ℝ => (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100 else if min a b < -1 then 38/100 else 68/100)) / 16 * (1 + (δ a b)^2/30 + (δ a b)^4/1680) * (δ a b)^2)) (fun a b : ℝ => Real.log (q a) - Real.log (q b))) (fun a b : ℝ => if a = b then k a ^ 2 + 2 * k a * deriv k a / (q a - a) else (q a * k a ^ 2 - q b * k b ^ 2) / (q a - q b))) (fun (f : ℝ → ℝ) (a b : ℝ) => if a = b then deriv f a else (f a - f b) / (a - b))) (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (ka x * ka x) i j * Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) + Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => (J x)⁻¹ r s * Matrix.trace ((K s x * ka x + ka x * K s x) * H r x))))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (MeasureTheory.integral γ)) (d ka)) (d A)) (d J)) (fun x => cfc k (A x))) (fun x => cfc q (A x))) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) := by
  classical
  intro m hm A hA hAs hb φ hφ hJ hZ hK hR hBs hBm hsec
  let q : ℝ → ℝ := gaussianHazard
  let k : ℝ → ℝ := transportRatio
  let f : ℝ → ℝ := fun a => Real.log (q a)
  let S := fun x => ∑ r : Fin m, ∑ i : Fin m, ∑ j : Fin m,
    surplusWeight f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
      (((hA x).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ).transpose *
        matrixPartial A r x * (hA x).eigenvectorUnitary) i j ^ 2
  have hAc : Continuous A := continuous_matrix fun i j => (hAs i j).continuous
  have hAd : ∀ x i j, DifferentiableAt ℝ (fun y => A y i j) x :=
    fun x i j => (hAs i j).differentiable (by simp) x
  have hf : Continuous f := contDiff_gaussianHazard.continuous.log
    (fun a => ne_of_gt (gaussianHazard_pos a))
  have hZm : ∀ r i j, Measurable (fun x => matrixPartial A r x i j) := by
    intro r i j
    exact measurable_fderiv_apply_const ℝ (fun y => A y i j) (PiLp.single 2 r (1 : ℝ))
  have hSm : Measurable S := Finset.measurable_sum _ fun r _ =>
    measurable_separation hA hAc hf (hZm r)
  have hS0 : ∀ x, 0 ≤ S x := by
    intro x
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (surplusWeight_nonneg f _ _) (sq_nonneg _)
  have hsec' : ∀ a b, 1 - (dslope k a b) ^ 2 + surplusWeight f a b ≤
      (dslope q a b) ^ 2 * secantMultiplier q k a b / (q a * q b) := by
    intro a b
    rw [dslope_eq_dividedDifference, dslope_eq_dividedDifference]
    exact hsec a b
  have hpoint := pointwise_hessian_estimate hA hAc hAd
    (q := q) (k := k)
    (fun a => (hasDerivAt_gaussianHazard a).differentiableAt)
    (fun a => (hasDerivAt_transportRatio a).differentiableAt)
    gaussianHazard_pos strictMono_gaussianHazard
    (fun a => (hasDerivAt_gaussianHazard a).deriv)
    (fun a => ne_of_gt (gaussianGap_pos a)) hφ hJ hBs hBm (surplusWeight f) hsec'
  exact integrate_surplus (Z := matrixPartial A)
    (K := matrixPartial (fun y => cfc k (A y))) (S := S)
    hZ hK hSm hS0 hR hpoint
