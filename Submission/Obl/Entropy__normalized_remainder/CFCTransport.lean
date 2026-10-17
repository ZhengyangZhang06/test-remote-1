import Submission.Obl.Entropy__normalized_remainder.CFCUniform
import Submission.Obl.Entropy__normalized_remainder.Interfaces
import Submission.Lib.GaussianTransport.GaussianTails

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ContDiff

namespace Submission.Obl.Entropy__normalized_remainder

lemma contDiff_hazard_scalar : ContDiff ℝ ∞ hazard :=
  Submission.Lib.GaussianTransport.contDiff_gaussianHazard

lemma contDiff_tailPotential_scalar : ContDiff ℝ ∞ tailPotential :=
  Submission.Lib.GaussianTransport.contDiff_exponentialTransport

lemma contDiff_multiplier_scalar : ContDiff ℝ ∞ multiplier :=
  contDiff_tailPotential_scalar.div contDiff_hazard_scalar
    (fun a => ne_of_gt (Submission.Lib.GaussianTransport.gaussianHazard_pos a))

lemma contDiff_scalarB : ContDiff ℝ ∞ scalarB :=
  (contDiff_infty_iff_deriv.1 contDiff_multiplier_scalar).2

lemma contDiff_scalarL : ContDiff ℝ ∞ scalarL :=
  (contDiff_infty_iff_deriv.1 contDiff_scalarB).2

lemma contDiff_scalarF : ContDiff ℝ ∞ scalarF :=
  contDiff_multiplier_scalar.mul (contDiff_const.add contDiff_scalarB)

variable {m : ℕ} {A : E m → Mat m}

lemma coordinateDerivative_cfc_eigenbasis
    (hAs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hA : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : Fin m) (x : E m) (i j : Fin m) :
    ((spectralBasis hA x).transpose *
      coordinateDerivative (fun y => cfc f (A y)) r x * spectralBasis hA x) i j =
      dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        ((spectralBasis hA x).transpose * coordinateDerivative A r x *
          spectralBasis hA x) i j :=
  entryDirectionalDerivative_cfc_eigenbasis A (fun i j => (hAs i j).continuous)
    hA hf (fun i j => (hAs i j).differentiable (by simp) x)
      (PiLp.single 2 r (1 : ℝ)) i j

lemma contDiff_one_cfc_field_entries
    (hAs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hA : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ i j, ContDiff ℝ 1 (fun x => cfc f (A x) i j) :=
  contDiff_one_cfc_entries (fun i j => (hAs i j).of_le (by simp)) hA
    (hf.of_le (by simp))

lemma squareIntegrable_coordinateDerivative_cfc
    (hAs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (r : Fin m)
    (hZ : SquareIntegrable (coordinateDerivative A r)) :
    SquareIntegrable (coordinateDerivative (fun y => cfc f (A y)) r) :=
  memLp_entryDirectionalDerivative_cfc_of_bounded A
    (fun i j => (hAs i j).continuous) hA hbound hf
    (fun x i j => (hAs i j).differentiable (by simp) x)
    (PiLp.single 2 r (1 : ℝ)) hZ

/-- For bounded parameters, finite Jacobian energy implies finite parameter energy. -/
lemma squareIntegrable_coordinateDerivative_of_jacobian
    (hAs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) (r : Fin m)
    (hJ : SquareIntegrable (coordinateDerivative (jacobianField A) r)) :
    SquareIntegrable (coordinateDerivative A r) :=
  memLp_entryDirectionalDerivative_of_cfc_of_bounded A
    (fun i j => (hAs i j).continuous) hA hbound
    (contDiff_hazard_scalar.of_le (by simp))
    Submission.Lib.GaussianTransport.deriv_gaussianHazard_pos
    (fun x i j => (hAs i j).differentiable (by simp) x)
    (PiLp.single 2 r (1 : ℝ)) hJ

lemma squareIntegrable_multiplierGradient
    (hAs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hA : ∀ x, (A x).IsHermitian)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) (r : Fin m)
    (hZ : SquareIntegrable (coordinateDerivative A r)) :
    SquareIntegrable (multiplierGradient A r) :=
  squareIntegrable_coordinateDerivative_cfc hAs hA hbound
    (contDiff_multiplier_scalar.of_le (by simp)) r hZ

end Submission.Obl.Entropy__normalized_remainder
