/-
Adapted from: here:o006
Original proofs by session x0062.
-/

import Submission.Lib.EntropyRemainder.WeakMatrix

/-! # Weak covariance witnesses -/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable def covarianceWitnessU {m : ℕ}
    (A b l : E m → Mat m) (β : ℝ) (x : E m) : Mat m :=
  nonlinearPart A x * (b x - β • 1) +
    ∑ r, firstCoeff A r * (coordinateDerivative b r x - firstCoeff A r * l x) +
      (firstGram A - 1) * l x

noncomputable def covarianceWitnessV {m : ℕ} (A b : E m → Mat m)
    (K g : Fin m → E m → Mat m) (β : ℝ) (r : Fin m) (x : E m) : Mat m :=
  K r x - firstCoeff A r * b x - β • g r x

lemma covarianceWitnessU_sub {m : ℕ} (A b l : E m → Mat m) (β : ℝ) (x : E m) :
    covarianceWitnessU A b l β x - (A x * b x - l x) =
      -(∑ r, (x r • (firstCoeff A r * b x) -
        firstCoeff A r * coordinateDerivative b r x)) - β • nonlinearPart A x := by
  simp only [covarianceWitnessU, nonlinearPart, linearPart, firstGram,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Finset.sum_sub_distrib, ← Matrix.mul_assoc]
  module

/-- The covariance witnesses have the exact weak sign used in the completion. -/
theorem covarianceWitness_weak {m : ℕ} {A b l J k : E m → Mat m}
    {K g : Fin m → E m → Mat m} (β : ℝ)
    (hA : SquareIntegrable A)
    (hb : ∀ i j, ContDiff ℝ 1 (fun x => b x i j))
    (hbL : ∀ i j, MemLp (fun x => b x i j) ∞ (stdGaussian (E m)))
    (hdb : ∀ r, SquareIntegrable (coordinateDerivative b r))
    (hg : ∀ r, SquareIntegrable (g r)) (hdiv : WeakDivergence (nonlinearPart A) g)
    (hJ : ∀ x, J x - k x = A x * b x - l x) :
    WeakDivergence (fun x => covarianceWitnessU A b l β x - (J x - k x))
      (fun r x => covarianceWitnessV A b K g β r x - K r x) := by
  have h0 := (weakDivergence_const_mul (firstCoeff A) hb).neg
  have h0L := squareIntegrable_gaussian_adjoint_const_mul (firstCoeff A) hbL hdb
  have hXb (r : Fin m) : SquareIntegrable (fun x => firstCoeff A r * b x) :=
    squareIntegrable_const_mul _ (fun i j => (hbL i j).mono_exponent le_top)
  have h := h0.sub_smul hdiv (fun i j => (h0L i j).neg)
    (nonlinearPart_memLp hA) (fun r i j => (hXb r i j).neg) hg β
  convert! h using 1
  · funext x
    rw [hJ, covarianceWitnessU_sub]
  · funext r x
    unfold covarianceWitnessV
    module

lemma covarianceWitnessU_memLp {m : ℕ} {A b l : E m → Mat m} (β : ℝ)
    (hA : SquareIntegrable A)
    (hb : ∀ i j, MemLp (fun x => b x i j) ∞ (stdGaussian (E m)))
    (hl : SquareIntegrable l) (hdb : ∀ r, SquareIntegrable (coordinateDerivative b r)) :
    SquareIntegrable (covarianceWitnessU A b l β) := by
  have hb' : ∀ i j, MemLp (fun x => (b x - β • 1) i j) ∞ (stdGaussian (E m)) :=
    fun i j => (hb i j).sub (memLp_const _)
  have h1 := squareIntegrable_mul_top (nonlinearPart_memLp hA) hb'
  have h2 (r : Fin m) := squareIntegrable_const_mul (firstCoeff A r)
    (fun i j => (hdb r i j).sub (squareIntegrable_const_mul (firstCoeff A r) hl i j))
  have h3 := squareIntegrable_const_mul (firstGram A - 1) hl
  intro i j
  simpa only [covarianceWitnessU, Matrix.add_apply, Matrix.sum_apply, Matrix.sub_apply,
    Pi.add_apply, Pi.sub_apply] using!
    ((h1 i j).add (memLp_finsetSum Finset.univ (fun r _ => h2 r i j))).add (h3 i j)

lemma covarianceWitnessV_memLp {m : ℕ} {A b : E m → Mat m}
    {K g : Fin m → E m → Mat m} (β : ℝ) (hb : SquareIntegrable b)
    (hK : ∀ r, SquareIntegrable (K r)) (hg : ∀ r, SquareIntegrable (g r)) (r : Fin m) :
    SquareIntegrable (covarianceWitnessV A b K g β r) := by
  intro i j
  exact ((hK r i j).sub (squareIntegrable_const_mul (firstCoeff A r) hb i j)).sub
    ((hg r i j).const_mul β)

end Submission.Lib.EntropyRemainder
