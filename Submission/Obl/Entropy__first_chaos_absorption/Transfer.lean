import Submission.Obl.Entropy__first_chaos_absorption.ScalarAbsorption
import Submission.Obl.Entropy__first_chaos_absorption.Moments
import Submission.Obl.Entropy__first_chaos_absorption.Regularity

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__first_chaos_absorption

open Submission.Lib.EntropyTools

set_option backward.isDefEq.respectTransparency false

lemma matrix_absorption_of_bounds {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).IsHermitian)
    (hc : ∀ i j, Continuous (fun x => A x i j))
    (hb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    (hmean : ∀ i j, (∫ x, A x i j ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0)
    (hB : (∑ r, momentCoefficient A r * momentCoefficient A r).PosSemidef)
    {p cost : ℝ → ℝ} (hpcont : Continuous p)
    (hpneg : ∀ a, a ≤ 0 → 1/(7+a^2) ≤ p a)
    (hpmid : ∀ a, 0 ≤ a → (1/4 : ℝ) ≤ p a)
    (hphi : ∀ a, 4 ≤ a → (23/50 : ℝ) ≤ p a)
    (hcost : ∀ a, cost a ≤ 111/1000) :
    let B := ∑ r, momentCoefficient A r * momentCoefficient A r
    let S := ((37/40 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) + (3/40 : ℝ) • B)⁻¹
    (S - 1).trace - Real.log S.det -
      (∫ x, ((-(S - 1) * (B - 1)) *
        ((3/20 : ℝ) • 1 + (1813/4000 : ℝ) • S) * cfc p (A x)).trace
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) +
      (∫ x, (momentRemainder A x * momentRemainder A x * cfc cost (A x)).trace
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
      (69/500)*(∫ x, ∑ i, ∑ j, (momentRemainder A x i j)^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) -
        (∑ i, rigidityWeight (hB.isHermitian.eigenvalues i))/1000 := by
  have hL2 := Submission.Obl.Entropy__centered_slack_transports.field_memLp hc hb
  have hint := fun i j => (hL2 i j).integrable (by norm_num)
  have hb' : ∃ R : ℝ, ∀ x i j, |A x i j| ≤ R := by
    obtain ⟨R, _, hR⟩ := hb
    exact ⟨R, hR⟩
  exact absorption_from_scalar hA (momentRemainder_isHermitian A hA) hB hint
    (matrix_square_integrable A hL2)
    (matrix_square_integrable (momentRemainder A) (momentRemainder_memLp A hL2))
    hmean (moment_matrix_second A hL2)
    (integrable_cfc_entry hA hc hb' hpcont)
    (fun z hz a => quadratic_minorant hpneg hpmid hphi (rigidityCutoff_pos hz)
      (rigidityCutoff_le z) a)
    hcost (fun z hz r hr e he => scalar_absorption_bound hz hr he)

end Submission.Obl.Entropy__first_chaos_absorption
