/- Adapted from: here:o022. Original proofs by session x0047. -/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Submission.Lib.GaussianHermite

/-- An everywhere finite moment-generating function determines a finite measure from its moments. -/
theorem measure_eq_of_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : integrableExpSet id μ = univ) (hν : integrableExpSet id ν = univ)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂ν) : μ = ν := by
  have hμa : AnalyticOnNhd ℂ (complexMGF id μ) univ := by
    simpa [hμ] using (analyticOnNhd_complexMGF (X := id) (μ := μ))
  have hνa : AnalyticOnNhd ℂ (complexMGF id ν) univ := by
    simpa [hν] using (analyticOnNhd_complexMGF (X := id) (μ := ν))
  have hzero : (fun z => complexMGF id μ z - complexMGF id ν z) = 0 := by
    apply (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (fun z => (hμa z (mem_univ _)).sub (hνa z (mem_univ _)))).mp
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((hμa 0 (mem_univ _)).sub (hνa 0 (mem_univ _)))]
    intro i hi
    rw [iteratedDeriv_sub (hμa 0 (mem_univ _)).contDiffAt
      (hνa 0 (mem_univ _)).contDiffAt]
    rw [iteratedDeriv_complexMGF (by simp [hμ]),
      iteratedDeriv_complexMGF (by simp [hν])]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one,
      ← Complex.ofReal_pow, integral_complex_ofReal, hmom, sub_self]
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  have h := congrFun hzero z
  exact sub_eq_zero.mp h

end Submission.Lib.GaussianHermite
