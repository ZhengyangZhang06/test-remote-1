import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.Projection
import Submission.Obl.Entropy__centered_slack_transports.Fields
import Submission.Lib.JacobianCompatibility.Coefficients
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.gaussian_first_chaos_h1_projection`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__gaussian_first_chaos_h1_projection`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__gaussian_first_chaos_h1_projection/`
belong to this obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Submission.Obl.Entropy__gaussian_first_chaos_h1_projection
open Submission.Obl.Entropy__centered_slack_transports
open Submission.Lib.JacobianCompatibility

theorem Submission.Entropy.gaussian_first_chaos_h1_projection : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, (∀ x, (A x).IsHermitian) → (fun γ => (fun I => (fun L2 => (fun d => (fun X => (fun Y => (fun N => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (d A r)) → (∀ x, (Y x).IsHermitian) ∧ (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => Y x i j)) ∧ L2 Y ∧ (∀ r, L2 (d Y r)) ∧ (∀ i j, I (fun x => Y x i j) = 0) ∧ (∀ r i j, I (fun x => x r * Y x i j) = 0) ∧ N A - Finset.sum Finset.univ (fun r : Fin m => N (d A r)) = N Y - Finset.sum Finset.univ (fun r : Fin m => N (d Y r))) (fun F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r : Fin m => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (MeasureTheory.integral γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  classical
  intro m hm A hA
  dsimp only
  intro hSmooth hBound hMean hGrad
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  let X : Fin m → Matrix (Fin m) (Fin m) ℝ := fun r =>
    Matrix.of (fun i j => ∫ x, x r * A x i j ∂γ)
  let Y : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ :=
    fun x => A x - ∑ r, x r • X r
  let d := fun (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
      (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) =>
    Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ)))
  let L2 := fun (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) =>
    ∀ i j, MemLp (fun x => F x i j) 2 γ
  let N := fun (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) =>
    ∫ x, ∑ i, ∑ j, (F x i j)^2 ∂γ
  change (∀ x, (Y x).IsHermitian) ∧
    (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => Y x i j)) ∧
    L2 Y ∧ (∀ r, L2 (d Y r)) ∧ (∀ i j, (∫ x, Y x i j ∂γ) = 0) ∧
    (∀ r i j, (∫ x, x r * Y x i j ∂γ) = 0) ∧
    N A - ∑ r, N (d A r) = N Y - ∑ r, N (d Y r)
  have hA2 : L2 A := field_memLp (fun i j => (hSmooth i j).continuous) hBound
  have hAdiff (i j : Fin m) : Differentiable ℝ (fun x => A x i j) :=
    (hSmooth i j).differentiable (by simp)
  have hY (i j : Fin m) : (fun x => Y x i j) = scalarRemainder (fun x => A x i j) := by
    funext x
    simp [Y, X, γ, scalarRemainder, linearPart_apply, firstCoeff, Matrix.sub_apply,
      Matrix.sum_apply]
  have hY2 : L2 Y := by
    intro i j
    rw [hY i j]
    exact remainder_memLp (hA2 i j)
  have hdY (r i j : Fin m) :
      (fun x => d Y r x i j) =
        (fun x => d A r x i j - firstCoeff (fun x => A x i j) r) := by
    funext x
    change fderiv ℝ (fun y => Y y i j) x (PiLp.single 2 r (1 : ℝ)) = _
    rw [hY i j, fderiv_remainder (hAdiff i j)]
    rfl
  have hdY2 : ∀ r, L2 (d Y r) := by
    intro r i j
    rw [hdY r i j]
    exact (hGrad r i j).sub (memLp_const _)
  refine ⟨?_, ?_, hY2, hdY2, ?_, ?_, ?_⟩
  · intro x
    apply (hA x).sub
    simpa only [coefficientField_apply] using
      coefficientField_isHermitian X (fun r => coefficient_isHermitian A hA r) x
  · intro i j
    rw [hY i j]
    exact remainder_contDiff (hSmooth i j)
  · intro i j
    change (∫ x, (fun y => Y y i j) x ∂γ) = 0
    rw [hY i j]
    exact integral_remainder (hA2 i j) (hMean i j)
  · intro r i j
    change (∫ x, x r * (fun y => Y y i j) x ∂γ) = 0
    rw [hY i j]
    exact integral_coord_remainder (hA2 i j) r
  · have hN (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) (hF : L2 F) :
        N F = ∑ i, ∑ j, ∫ x, (F x i j)^2 ∂γ := by
      dsimp only [N]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => (hF i j).integrable_sq)
      · intro i _
        exact integrable_finsetSum _ (fun j _ => (hF i j).integrable_sq)
    have hentry (i j : Fin m) :
        (∫ x, (A x i j)^2 ∂γ) - ∑ r, ∫ x, (d A r x i j)^2 ∂γ =
        (∫ x, (Y x i j)^2 ∂γ) - ∑ r, ∫ x, (d Y r x i j)^2 ∂γ := by
      have h := remainder_energy (hAdiff i j) (hA2 i j) (fun r => hGrad r i j)
      simpa only [← hY i j, d, γ, Matrix.of_apply] using h
    rw [hN A hA2, hN Y hY2]
    simp_rw [hN (d A _) (hGrad _), hN (d Y _) (hdY2 _)]
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
      Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hentry i j))
    simp only [Finset.sum_sub_distrib] at hs
    have hswap (F : Fin m → Fin m → Fin m → ℝ) :
        (∑ i, ∑ j, ∑ r, F r i j) = ∑ r, ∑ i, ∑ j, F r i j := by
      simp_rw [Finset.sum_comm (f := fun j r => F r _ j)]
      rw [Finset.sum_comm]
    rw [hswap (fun r i j => ∫ x, (d A r x i j)^2 ∂γ),
      hswap (fun r i j => ∫ x, (d Y r x i j)^2 ∂γ)] at hs
    exact hs
