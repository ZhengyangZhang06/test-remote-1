import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__normalized_remainder.Interfaces
import Submission.Obl.Entropy__integrated_two_eigenvalue
import Submission.Obl.Entropy__transport_energy_surplus
import Submission.Obl.Entropy__transport_covariance_completion
import Submission.Obl.Entropy__noncommuting_remainder_assembly
import Submission.Obl.Entropy__first_chaos_absorption
import Submission.Obl.Entropy__gaussian_chaos_resolvent
set_option linter.unusedVariables false

open scoped BigOperators
open Submission.Obl.Entropy__normalized_remainder

/-!
# `Submission.Entropy.normalized_remainder`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__normalized_remainder`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__normalized_remainder/`
belong to this obligation.
-/

theorem Submission.Entropy.normalized_remainder : ∀ m : ℕ, 1 ≤ m → (fun (density : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m)) → ℝ) => (fun (mean : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (EuclideanSpace ℝ (Fin m))) => (fun (covariance : ((EuclideanSpace ℝ (Fin m)) → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) => (fun (entropy : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => (fun (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) => (fun (q : ℝ → ℝ) => (fun (normalized : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ((EuclideanSpace ℝ (Fin m)) → ℝ) → ((EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) → Prop) => (fun (ω : ℝ → ℝ) => ∀ V : (EuclideanSpace ℝ (Fin m)) → ℝ, regular V → ∀ φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ∀ A : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ), normalized V φ A → (fun (X : Fin m → (Matrix (Fin m) (Fin m) ℝ)) => (fun (Y : (EuclideanSpace ℝ (Fin m)) → (Matrix (Fin m) (Fin m) ℝ)) => (fun (B : (Matrix (Fin m) (Fin m) ℝ)) => ∃ hB : B.PosSemidef, MeasureTheory.integral γ (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (Y x i j) ^ 2))) / 500 + Finset.sum Finset.univ (fun i : Fin m => ω (hB.isHermitian.eigenvalues i)) / 1000 ≤ 2 * entropy (density V) - 2 * (m : ℝ) - Real.log (covariance (density V)).det) (Finset.sum Finset.univ (fun r : Fin m => X r * X r))) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => (x r) • X r))) (fun r => Matrix.of (fun i j => MeasureTheory.integral γ (fun x => (x r) * A x i j)))) (fun z => (3 * (z - 1) ^ 2 / (37 + 3 * z)) * ((3 : ℝ) / 20 + ((49 : ℝ) / 100) * (37 / (37 + 3 * z))) * (if z = 0 then (13 : ℝ) / 100 else min ((13 : ℝ) / 100) (32 / (25 * Real.sqrt z))))) (fun V φ A => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧ ConvexOn ℝ Set.univ φ ∧ (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) ∧ (∀ x, (A x).IsHermitian) ∧ (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) ∧ (∀ x i j, cfc q (A x) i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) ∧ MeasureTheory.Measure.map (gradient φ) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (density V x)) ∧ (∀ i j, MeasureTheory.integral γ (fun x => A x i j) = 0))) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun V => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖ ^ 2) ∧ MeasureTheory.Integrable (density V) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (density V) = 1 ∧ MeasureTheory.Integrable (fun x => density V x * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => density V x * Real.log (density V x)) MeasureTheory.volume)) (fun f => -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)))) (fun f => Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - mean f i) * (x j - mean f j))))) (fun f => MeasureTheory.integral MeasureTheory.volume (fun x => f x • x))) (fun V x => Real.exp (-V x)) := by
  intro m hm V hV φ A hdata
  rcases hV with ⟨hVs, hVc, hf, hprob, hf2, hflog⟩
  rcases hdata with ⟨hφs, hφc, hAs, hA, hbound, hJac, hmap, hmean⟩
  have henergy :
      (∀ r, SquareIntegrable (coordinateDerivative A r)) ∧
      (∀ r, SquareIntegrable (multiplierGradient A r)) ∧
      (∑ r, fieldEnergy (coordinateDerivative A r)) -
        (∑ r, fieldEnergy (multiplierGradient A r)) + separationSurplus A hA ≤
          fieldEnergy (multiplierField A) :=
    Submission.Entropy.transport_energy_surplus m hm A hA hAs hbound V φ
      hVs hVc hφs hφc hJac hmap
  rcases henergy with ⟨hZ, hK, hsurplus⟩
  obtain ⟨g, hgs, hgL, hgdiv, hchaos⟩ :
      ∃ g : Fin m → E m → Mat m,
        (∀ r x, (g r x).IsHermitian) ∧ (∀ r, SquareIntegrable (g r)) ∧
        WeakDivergence (nonlinearPart A) g ∧
        fieldEnergy A - (∑ r, fieldEnergy (coordinateDerivative A r)) +
          chaosBudget A g ≤ -(7/50)*fieldEnergy (nonlinearPart A) :=
    Submission.Entropy.gaussian_chaos_resolvent m hm A hA hAs hbound hmean hZ
  have hpair : (∀ a, 0 < scalarP a) ∧
      residualBudget A g ≤ chaosBudget A g + separationSurplus A hA :=
    Submission.Entropy.integrated_two_eigenvalue m hm A hA hAs hbound hmean hZ hK
      g hgs hgL
  have hB : (firstGram A).PosSemidef := firstGram_posSemidef hA
  obtain ⟨u, v, hu, hv, hweak, hmatrix⟩ :
      ∃ u : E m → Mat m, ∃ v : Fin m → E m → Mat m,
        SquareIntegrable u ∧ (∀ r, SquareIntegrable (v r)) ∧
        WeakDivergence (fun x => u x - (jacobianField A x - multiplierField A x))
          (fun r x => v r x - multiplierGradient A r x) ∧
        expectation (fun x => Matrix.trace
          ((dualS (firstGram A) - 1) * covarianceRemainder A x)) +
          weightedEnergy (dualS (firstGram A)) u +
          (∑ r, weightedEnergy (dualS (firstGram A)) (v r)) -
          Real.log (dualS (firstGram A)).det ≤ absorptionCost A + residualBudget A g :=
    Submission.Entropy.noncommuting_remainder_assembly m hm A hA hAs hbound hmean
      hZ hK hpair.1 g hgs hgL hgdiv
  have habsorption : absorptionCost A ≤ (69/500)*fieldEnergy (nonlinearPart A) -
      (∑ i, Submission.Lib.EntropyTools.rigidityWeight (hB.isHermitian.eigenvalues i))/1000 :=
    Submission.Entropy.first_chaos_absorption m hm A hA hAs hbound hmean hB
  have hcovariance :
      2*(m : ℝ) + Real.log (covarianceOfDensity (fun x => Real.exp (-V x))).det +
        2*MeasureTheory.integral MeasureTheory.volume
          (fun x => Real.exp (-V x) * Real.log (Real.exp (-V x))) ≤
      fieldEnergy A - fieldEnergy (multiplierField A) -
        (∑ r, fieldEnergy (multiplierGradient A r)) +
        expectation (fun x => Matrix.trace
          ((dualS (firstGram A) - 1) * covarianceRemainder A x)) +
        weightedEnergy (dualS (firstGram A)) u +
        (∑ r, weightedEnergy (dualS (firstGram A)) (v r)) -
        Real.log (dualS (firstGram A)).det :=
    Submission.Entropy.transport_covariance_completion m hm A hA hAs hbound hK
      (fun x => Real.exp (-V x)) (fun x => (Real.exp_pos _).le) hf hprob hf2 hflog
      φ hφs hφc hJac hmap (dualS (firstGram A)) (dualS_posDef hB) u v hu hv hweak
  refine ⟨hB, ?_⟩
  change fieldEnergy (nonlinearPart A)/500 +
      (∑ i, Submission.Lib.EntropyTools.rigidityWeight (hB.isHermitian.eigenvalues i))/1000 ≤
    2*(-MeasureTheory.integral MeasureTheory.volume
      (fun x => Real.exp (-V x) * Real.log (Real.exp (-V x)))) - 2*(m : ℝ) -
      Real.log (covarianceOfDensity (fun x => Real.exp (-V x))).det
  linarith only [hsurplus, hchaos, hpair.2, hmatrix, habsorption, hcovariance]
