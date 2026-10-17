import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.Data
import Submission.Lib.JacobianCompatibility.Coefficients
import Submission.Obl.Entropy__linear_transport_limit.Fields
import Submission.Obl.Entropy__centered_slack_transports.Fields

set_option maxHeartbeats 400000

open MeasureTheory
open scoped ENNReal ContDiff

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

variable {m : ℕ} {A : Field m} {g : Fin m → Field m}

lemma Regularity.top (hreg : Regularity A) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    MatrixLp (gaussian m) ⊤ (calcField A f) := by
  obtain ⟨hc, ⟨C, hC, hb⟩, hd⟩ := hreg f hf
  exact MatrixLp.of_bound (fun i j => (hc i j).continuous.aestronglyMeasurable)
    ⟨C, hb⟩

lemma matY_memLp (hA : MatrixLp (gaussian m) 2 A) :
    MatrixLp (gaussian m) 2 (matY A) := by
  refine hA.sub (MatrixLp.sum (fun r => ?_))
  intro i j
  exact (Submission.Obl.Entropy__linear_transport_limit.memLp_coord r).mul_const _

lemma matX_hermitian (hA : ∀ x, (A x).IsHermitian) (r : Fin m) : (matX A r).IsHermitian :=
  Submission.Obl.Entropy__centered_slack_transports.coefficient_isHermitian A hA r

lemma matY_hermitian (hA : ∀ x, (A x).IsHermitian) (x : Space m) : (matY A x).IsHermitian := by
  apply (hA x).sub
  simpa only [Submission.Lib.JacobianCompatibility.coefficientField_apply] using
    Submission.Lib.JacobianCompatibility.coefficientField_isHermitian
      (matX A) (matX_hermitian hA) x

/-- L2 closure justifies every term of the expanded remainder and budget. -/
lemma integrability_from_regularity (hreg : Regularity A)
    (hA : MatrixLp (gaussian m) 2 A) (hg : ∀ r, MatrixLp (gaussian m) 2 (g r))
    (hp : ∀ a, 0 < scalarP a) :
    MatrixLp (gaussian m) 2 (witnessU A) ∧
    (∀ r, MatrixLp (gaussian m) 2 (witnessV A g r)) ∧
    Integrable (fun x => core A g x + commutator A g x) (gaussian m) ∧
    Integrable (rightSide A g) (gaussian m) ∧
    (∫ x, rightSide A g x ∂gaussian m) =
      -(∫ x, Matrix.trace (matH A * matRho A * calcField A scalarP x) ∂gaussian m) +
      (∫ x, Matrix.trace (matY A x * matY A x * calcField A scalarCost x) ∂gaussian m) +
      budgetIntegral A g := by
  have hY := matY_memLp hA
  have hb := hreg.top smooth_scalarB
  have hl := hreg.top smooth_scalarL
  have hD (r : Fin m) : MatrixLp (gaussian m) 2 (residualD A r) :=
    ((hreg scalarK smooth_scalarK).2.2 r).sub ((hb.const_mul _).of_le le_top)
  have hL (r : Fin m) : MatrixLp (gaussian m) 2 (residualL A r) :=
    ((hreg scalarB smooth_scalarB).2.2 r).sub ((hl.const_mul _).of_le le_top)
  have hM (r : Fin m) : MatrixLp (gaussian m) 2 (residualM A g r) :=
    (((((hreg scalarF smooth_scalarF).2.2 r).sub
      (((hreg.top (contDiff_infty_iff_deriv.mp smooth_scalarF).2).const_mul _).of_le le_top)).sub
      (((hD r).mul hb).nsmul 2)).sub (((hL r).mul hl).smul (80/3))).add
      (((hg r).mul hb).smul (3/2))
  have hV (r : Fin m) : MatrixLp (gaussian m) 2 (witnessV A g r) :=
    (hD r).sub ((hg r).smul (7/25))
  have hW (r : Fin m) : MatrixLp (gaussian m) 2 (witnessW A g r) :=
    (hD r).sub ((hg r).smul (3/4))
  have hF : MatrixLp (gaussian m) 2 (witnessF A) :=
    (hY.mul (hb.sub (MatrixLp.const _))).add (MatrixLp.sum fun r => (hL r).const_mul _)
  have hU : MatrixLp (gaussian m) 2 (witnessU A) :=
    hF.add ((hl.const_mul _).of_le le_top)
  have hWM (r : Fin m) : MatrixLp (gaussian m) 2 (weightedM A g r) :=
    (hM r).mul (hreg.top (smooth_scalarInvSqrt hp))
  have hc0 : Integrable (fun x => -Matrix.trace (matH A * calcField A scalarP x)) (gaussian m) :=
    (((hreg.top smooth_scalarP).const_mul _).of_le le_top).integrable_trace.neg
  have hc1 : Integrable (fun x => Matrix.trace (matT A * (matY A x * calcField A scalarH x +
      ∑ r, matX A r * residualM A g r x))) (gaussian m) :=
    ((((hY.mul (hreg.top smooth_scalarH)).add
      (MatrixLp.sum fun r => (hM r).const_mul _)).const_mul _).of_le (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).integrable_trace
  have hc2 : Integrable (fun x => Matrix.trace
      ((witnessF A x).transpose * matS A * witnessF A x)) (gaussian m) :=
    ((hF.transpose.mul_const _).mul hF).integrable_trace
  have hc3 : Integrable (fun x => ∑ r, Matrix.trace
      ((witnessV A g r x).transpose * matS A * witnessV A g r x)) (gaussian m) :=
    integrable_finsetSum _ fun r _ => (((hV r).transpose.mul_const _).mul (hV r)).integrable_trace
  have hc4 : Integrable (fun x => (9/16 : ℝ) * Matrix.trace (matT A * ∑ r, g r x * g r x))
      (gaussian m) :=
    ((MatrixLp.sum fun r => (hg r).mul (hg r)).const_mul _).integrable_trace.const_mul (9/16)
  have hcore : Integrable (core A g) (gaussian m) := (((hc0.add hc1).add hc2).add hc3).add hc4
  have hm0 : Integrable (fun x => -Matrix.trace
      (matT A * calcField A scalarB x * matB A * calcField A scalarB x -
       matT A * matB A * calcField A scalarB x * calcField A scalarB x)) (gaussian m) :=
    (((((hb.const_mul _).mul_const _).mul hb).sub
      ((hb.const_mul _).mul hb)).of_le le_top).integrable_trace.neg
  have hm1 : Integrable (fun x => 2 * Matrix.trace
      ((matT A * calcField A scalarB x - calcField A scalarB x * matT A) *
       ∑ r, matX A r * witnessW A g r x)) (gaussian m) :=
    ((((hb.const_mul _).sub (hb.mul_const _)).mul
      (MatrixLp.sum fun r => (hW r).const_mul _)).of_le (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).integrable_trace.const_mul 2
  have hm2 : Integrable (fun x => Matrix.trace
      (matT A * ∑ r, (witnessW A g r x).transpose * witnessW A g r x)) (gaussian m) :=
    ((MatrixLp.sum fun r => (hW r).transpose.mul (hW r)).const_mul _).integrable_trace
  have hcomm : Integrable (commutator A g) (gaussian m) := (hm0.sub hm1).sub hm2
  have hbudget : Integrable (budget A g) (gaussian m) := by
    exact integrable_finsetSum _ fun r _ =>
      (((((hV r).integrable_squares.const_mul (40/37)).add
        ((hW r).integrable_squares.const_mul (42/37))).add
        ((hg r).integrable_squares.const_mul (27/592))).add
        ((hL r).integrable_squares.const_mul (40/3))).add
        ((hWM r).integrable_squares.const_mul (5/17))
  have hreserve : Integrable (fun x => Matrix.trace (matH A * matRho A * calcField A scalarP x))
      (gaussian m) :=
    (((hreg.top smooth_scalarP).const_mul _).of_le le_top).integrable_trace
  have hcost : Integrable (fun x => Matrix.trace (matY A x * matY A x * calcField A scalarCost x))
      (gaussian m) :=
    ((hY.mul (t := 1) hY).mul (hreg.top (smooth_scalarCost hp))).integrable_trace
  refine ⟨hU, hV, hcore.add hcomm, (hreserve.neg.add hcost).add hbudget, ?_⟩
  change (∫ x, -Matrix.trace _ + Matrix.trace _ + budget A g x ∂gaussian m) = _
  erw [integral_add (hreserve.neg.add hcost) hbudget, integral_add hreserve.neg hcost, integral_neg]
  congr 1
  exact (Submission.Lib.PairEstimate.integral_budget _ _ _ _ _ hV hW hg hL hWM).symm

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
