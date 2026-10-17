import Submission.Obl.Root.SmoothTransportParameter
import Submission.Lib.GaussianTransport.GaussianMatrixMean
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Hessian

/-!
# Constructing the normalized matrix parameter from a zero

Once the inverse-hazard Jacobian has zero Gaussian mean, the smooth spectral
calculus supplies all the matrix-field clauses in Proposition 2.3.
-/

open MeasureTheory ProbabilityTheory Matrix Set
open scoped Matrix.Norms.L2Operator ContDiff

namespace Submission.Obl.Root.GaussianMatrixSmooth

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Mat" => Matrix (Fin m) (Fin m) ℝ
local notation "γ" => stdGaussian E

/-- A zero of the inverse-hazard mean yields the exact normalized transport data. -/
theorem normalized_parameter_of_zero {V φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hconvex : ConvexOn ℝ univ φ) {J : E → Mat}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i)
    (hpos : ∀ x, (J x).PosDef) {l u : ℝ} (hl : 0 < l)
    (hs : ∀ x, spectrum ℝ (J x) ⊆ Icc l u)
    (hlaw : Measure.map (gradient φ) γ =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (hmean : (∫ x, cfc inverseGaussianHazard (J x) ∂γ) = 0) :
    ∃ A : E → Mat,
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ univ φ ∧
      (∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) ∧
      (∀ x, (A x).IsHermitian) ∧
      (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) ∧
      (∀ x i j, cfc gaussianHazard (A x) i j =
        (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) ∧
      Measure.map (gradient φ) γ =
        volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) ∧
      (∀ i j, (∫ x, A x i j ∂γ) = 0) := by
  have hJs : ContDiff ℝ ∞ J := contDiff_matrix_of_entries (fun i j =>
    contDiff_pi.mp (contDiff_pi.mp
      (Submission.Obl.Entropy__transport_finite_jacobian_energy.contDiff_jacobian hφ hJ) i) j)
  obtain ⟨hAs, hAH, hAb, hAQ⟩ := smooth_bounded_inverseGaussianHazard hJs hpos hl hs
  have hAi : Integrable (fun x => cfc inverseGaussianHazard (J x)) γ := by
    apply (integrable_const (|inverseGaussianHazard l| + |inverseGaussianHazard u|)).mono'
      (contDiff_cfc_inverseGaussianHazard hJs hpos).continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => norm_inverseGaussianHazard_le hl (hs x))
  refine ⟨fun x => cfc inverseGaussianHazard (J x), hφ, hconvex, hAs, hAH, hAb,
    ?_, hlaw, ?_⟩
  · intro x i j
    rw [hAQ x, hJ]
  · intro i j
    rw [← matrix_integral_apply hAi i j, hmean]
    rfl

end Submission.Obl.Root.GaussianMatrixSmooth
