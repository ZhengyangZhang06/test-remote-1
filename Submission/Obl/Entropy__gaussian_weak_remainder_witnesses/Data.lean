import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.Scalar
import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.MatrixLp

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

abbrev Space (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ
abbrev Field (m : ℕ) := Space m → Mat m

noncomputable abbrev gaussian (m : ℕ) := stdGaussian (Space m)
noncomputable abbrev calcField {m : ℕ} (A : Field m) (f : ℝ → ℝ) : Field m :=
  fun x => cfc f (A x)
noncomputable def coordDeriv {m : ℕ} (F : Field m) (r : Fin m) : Field m :=
  fun x => Matrix.of fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))

def Regularity {m : ℕ} (A : Field m) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
    (∀ i j, ContDiff ℝ 1 (fun x => calcField A f x i j)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x i j, |calcField A f x i j| ≤ C) ∧
    (∀ r, MatrixLp (gaussian m) 2 (coordDeriv (calcField A f) r))

def WeakDiv {m : ℕ} (F : Field m) (V : Fin m → Field m) : Prop :=
  ∀ i j, ∀ z : Space m → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
    (∫ x, F x i j * z x ∂gaussian m) =
      ∑ r, ∫ x, V r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂gaussian m

noncomputable def matX {m : ℕ} (A : Field m) (r : Fin m) : Mat m :=
  Matrix.of fun i j => ∫ x, x r * A x i j ∂gaussian m
noncomputable def matY {m : ℕ} (A : Field m) : Field m :=
  fun x => A x - ∑ r, x r • matX A r
noncomputable def matB {m : ℕ} (A : Field m) : Mat m := ∑ r, matX A r * matX A r
noncomputable def matS {m : ℕ} (A : Field m) : Mat m := ((37/40 : ℝ) • 1 + (3/40 : ℝ) • matB A)⁻¹
noncomputable def matT {m : ℕ} (A : Field m) : Mat m := matS A - 1
noncomputable def matH {m : ℕ} (A : Field m) : Mat m := -matT A * (matB A - 1)
noncomputable def matRho {m : ℕ} (A : Field m) : Mat m := (3/20 : ℝ) • 1 + (1813/4000 : ℝ) • matS A
noncomputable def matK {m : ℕ} (A : Field m) (r : Fin m) : Field m := coordDeriv (calcField A scalarK) r
noncomputable def residualD {m : ℕ} (A : Field m) (r : Fin m) : Field m :=
  fun x => matK A r x - matX A r * calcField A scalarB x
noncomputable def residualL {m : ℕ} (A : Field m) (r : Fin m) : Field m :=
  fun x => coordDeriv (calcField A scalarB) r x - matX A r * calcField A scalarL x
noncomputable def residualM {m : ℕ} (A : Field m) (g : Fin m → Field m) (r : Fin m) : Field m :=
  fun x => coordDeriv (calcField A scalarF) r x - matX A r * calcField A (deriv scalarF) x -
    2 • (residualD A r x * calcField A scalarB x) -
    (80/3 : ℝ) • (residualL A r x * calcField A scalarL x) +
    (3/2 : ℝ) • (g r x * calcField A scalarB x)
noncomputable def witnessV {m : ℕ} (A : Field m) (g : Fin m → Field m) (r : Fin m) : Field m :=
  fun x => residualD A r x - (7/25 : ℝ) • g r x
noncomputable def witnessW {m : ℕ} (A : Field m) (g : Fin m → Field m) (r : Fin m) : Field m :=
  fun x => residualD A r x - (3/4 : ℝ) • g r x
noncomputable def witnessF {m : ℕ} (A : Field m) : Field m :=
  fun x => matY A x * (calcField A scalarB x - (7/25 : ℝ) • 1) +
    ∑ r, matX A r * residualL A r x
noncomputable def witnessU {m : ℕ} (A : Field m) : Field m :=
  fun x => witnessF A x + (matB A - 1) * calcField A scalarL x
noncomputable def weightedM {m : ℕ} (A : Field m) (g : Fin m → Field m) (r : Fin m) : Field m :=
  fun x => residualM A g r x * calcField A (fun a => (Real.sqrt (scalarP a))⁻¹) x
noncomputable def squareSum {m : ℕ} (Q : Mat m) : ℝ := ∑ i, ∑ j, (Q i j)^2
noncomputable def normSq {m : ℕ} (F : Field m) : ℝ := ∫ x, squareSum (F x) ∂gaussian m
noncomputable def core {m : ℕ} (A : Field m) (g : Fin m → Field m) (x : Space m) : ℝ :=
  -Matrix.trace (matH A * calcField A scalarP x) +
    Matrix.trace (matT A * (matY A x * calcField A scalarH x +
      ∑ r, matX A r * residualM A g r x)) +
    Matrix.trace ((witnessF A x).transpose * matS A * witnessF A x) +
    (∑ r, Matrix.trace ((witnessV A g r x).transpose * matS A * witnessV A g r x)) +
    (9/16 : ℝ) * Matrix.trace (matT A * ∑ r, g r x * g r x)
noncomputable def commutator {m : ℕ} (A : Field m) (g : Fin m → Field m) (x : Space m) : ℝ :=
  -Matrix.trace (matT A * calcField A scalarB x * matB A * calcField A scalarB x -
    matT A * matB A * calcField A scalarB x * calcField A scalarB x) -
    2 * Matrix.trace ((matT A * calcField A scalarB x - calcField A scalarB x * matT A) *
      ∑ r, matX A r * witnessW A g r x) -
    Matrix.trace (matT A * ∑ r, (witnessW A g r x).transpose * witnessW A g r x)
noncomputable def budget {m : ℕ} (A : Field m) (g : Fin m → Field m) (x : Space m) : ℝ :=
  ∑ r, ((40/37 : ℝ) * squareSum (witnessV A g r x) +
    (42/37 : ℝ) * squareSum (witnessW A g r x) +
    (27/592 : ℝ) * squareSum (g r x) +
    (40/3 : ℝ) * squareSum (residualL A r x) +
    (5/17 : ℝ) * squareSum (weightedM A g r x))
noncomputable def rightSide {m : ℕ} (A : Field m) (g : Fin m → Field m) (x : Space m) : ℝ :=
  -Matrix.trace (matH A * matRho A * calcField A scalarP x) +
    Matrix.trace (matY A x * matY A x * calcField A scalarCost x) + budget A g x
noncomputable def budgetIntegral {m : ℕ} (A : Field m) (g : Fin m → Field m) : ℝ :=
  ∑ r, ((40/37 : ℝ) * normSq (witnessV A g r) + (42/37 : ℝ) * normSq (witnessW A g r) +
    (27/592 : ℝ) * normSq (g r) + (40/3 : ℝ) * normSq (residualL A r) +
    (5/17 : ℝ) * normSq (weightedM A g r))

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
