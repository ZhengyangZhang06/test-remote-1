/-
Adapted from: here:o006

Original proofs by sessions x0016, x0019 and x0062.
-/

import Submission.Lib.EntropyRemainder.MatrixBounds

/-!
# Definitions used by the six closed interfaces

The child statements beta-bind the same expressions, so they need no
Submission definitions. This module gives those expressions readable names
for the glue. Constants are the exact rational constants in Sections 2--4.
-/

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def expectation {m : ℕ} (f : E m → ℝ) : ℝ :=
  ∫ x, f x ∂stdGaussian (E m)

noncomputable def hazard (a : ℝ) : ℝ :=
  gaussianPDFReal 0 1 a / cdf (gaussianReal 0 1) (-a)

noncomputable def tailPotential (a : ℝ) : ℝ :=
  -Real.log (cdf (gaussianReal 0 1) (-a))

noncomputable def multiplier (a : ℝ) : ℝ := tailPotential a / hazard a
noncomputable def scalarB : ℝ → ℝ := deriv multiplier
noncomputable def scalarL : ℝ → ℝ := deriv scalarB
noncomputable def scalarF (a : ℝ) : ℝ := multiplier a * (1 + scalarB a)
noncomputable def scalarP (a : ℝ) : ℝ :=
  deriv scalarF a - (scalarB a)^2 - (40/3) * (scalarL a)^2
noncomputable def scalarH (a : ℝ) : ℝ :=
  scalarF a - (3/2) * multiplier a - (80/3) * (scalarB a - 7/25) * scalarL a
noncomputable def absorptionWeight (a : ℝ) : ℝ :=
  (40/37) * ((scalarB a - 7/25)^2 + (5/96) * (scalarH a)^2 / scalarP a)

noncomputable def coordinateDerivative {m : ℕ} (F : E m → Mat m)
    (r : Fin m) (x : E m) : Mat m :=
  Matrix.of fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))

def SquareIntegrable {m : ℕ} (F : E m → Mat m) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) 2 (stdGaussian (E m))

/-- The Gaussian adjoint identity `partial* v = F`, in distributions. -/
def WeakDivergence {m : ℕ} (F : E m → Mat m) (v : Fin m → E m → Mat m) : Prop :=
  ∀ i j, ∀ z : E m → ℝ,
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
    expectation (fun x => F x i j * z x) =
      ∑ r, expectation (fun x => v r x i j *
        fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))

noncomputable def jacobianField {m : ℕ} (A : E m → Mat m) (x : E m) : Mat m :=
  cfc hazard (A x)
noncomputable def multiplierField {m : ℕ} (A : E m → Mat m) (x : E m) : Mat m :=
  cfc multiplier (A x)
noncomputable def multiplierGradient {m : ℕ} (A : E m → Mat m) :
    Fin m → E m → Mat m := coordinateDerivative (multiplierField A)

noncomputable def covarianceRemainder {m : ℕ} (A : E m → Mat m) (x : E m) : Mat m :=
  2 • cfc tailPotential (A x) - multiplierField A x * multiplierField A x -
    ∑ r, multiplierGradient A r x * multiplierGradient A r x

noncomputable def weightedEnergy {m : ℕ} (P : Mat m) (F : E m → Mat m) : ℝ :=
  expectation (fun x => Matrix.trace ((F x).transpose * P * F x))

noncomputable def covarianceOfDensity {m : ℕ} (f : E m → ℝ) : Mat m :=
  Matrix.of fun i j => ∫ x, f x * (x i - (∫ y, f y • y) i) *
    (x j - (∫ y, f y • y) j)

noncomputable def absorptionCost {m : ℕ} (A : E m → Mat m) : ℝ :=
  Matrix.trace (dualS (firstGram A) - 1) - Real.log (dualS (firstGram A)).det -
    expectation (fun x => Matrix.trace
      ((-(dualS (firstGram A) - 1) * (firstGram A - 1)) *
        dualRho (firstGram A) * cfc scalarP (A x))) +
    expectation (fun x => Matrix.trace
      (nonlinearPart A x * nonlinearPart A x * cfc absorptionWeight (A x)))

noncomputable def chaosBudget {m : ℕ} (A : E m → Mat m)
    (g : Fin m → E m → Mat m) : ℝ :=
  expectation (fun x => ∑ r, ∑ i, ∑ j,
    Submission.Lib.EntropyTools.chaosQuadratic
      (coordinateDerivative (nonlinearPart A) r x i j)
      (g r x i j - coordinateDerivative (nonlinearPart A) r x i j / 2))

noncomputable def logSeparation (a b : ℝ) : ℝ :=
  Real.log (hazard a) - Real.log (hazard b)
noncomputable def separationWeight (a b : ℝ) : ℝ :=
  (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100
    else if min a b < -1 then 38/100 else 68/100)) / 16 *
    (1 + (logSeparation a b)^2/30 + (logSeparation a b)^4/1680) *
    (logSeparation a b)^2
noncomputable def spectralBasis {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (x : E m) : Mat m := (hA x).eigenvectorUnitary
noncomputable def separationSurplus {m : ℕ} (A : E m → Mat m)
    (hA : ∀ x, (A x).IsHermitian) : ℝ :=
  expectation (fun x => ∑ r, ∑ i, ∑ j,
    separationWeight ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
      ((spectralBasis hA x).transpose * coordinateDerivative A r x *
        spectralBasis hA x) i j ^ 2)

noncomputable def derivativeResidual {m : ℕ} (A : E m → Mat m)
    (r : Fin m) (x : E m) : Mat m :=
  multiplierGradient A r x - firstCoeff A r * cfc scalarB (A x)
noncomputable def secondResidual {m : ℕ} (A : E m → Mat m)
    (r : Fin m) (x : E m) : Mat m :=
  coordinateDerivative (fun y => cfc scalarB (A y)) r x -
    firstCoeff A r * cfc scalarL (A x)
noncomputable def mixedResidual {m : ℕ} (A : E m → Mat m)
    (g : Fin m → E m → Mat m) (r : Fin m) (x : E m) : Mat m :=
  coordinateDerivative (fun y => cfc scalarF (A y)) r x -
    firstCoeff A r * cfc (deriv scalarF) (A x) -
    2 • (derivativeResidual A r x * cfc scalarB (A x)) -
    (80/3 : ℝ) • (secondResidual A r x * cfc scalarL (A x)) +
    (3/2 : ℝ) • (g r x * cfc scalarB (A x))
noncomputable def residualBudget {m : ℕ} (A : E m → Mat m)
    (g : Fin m → E m → Mat m) : ℝ :=
  ∑ r, ((40/37)*fieldEnergy (fun x => derivativeResidual A r x - (7/25 : ℝ) • g r x) +
    (42/37)*fieldEnergy (fun x => derivativeResidual A r x - (3/4 : ℝ) • g r x) +
    (27/592)*fieldEnergy (g r) + (40/3)*fieldEnergy (secondResidual A r) +
    (5/17)*fieldEnergy (fun x => mixedResidual A g r x *
      cfc (fun a => (Real.sqrt (scalarP a))⁻¹) (A x)))

end Submission.Lib.EntropyRemainder
