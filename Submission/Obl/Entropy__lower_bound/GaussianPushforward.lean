import Submission.Obl.Entropy__lower_bound.GaussianModel

/-! The scalar Gaussian-to-exponential transport from Section 2.1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__lower_bound

/-- The scalar transport takes values in the positive half-line. -/
theorem exponentialTransport_pos (a : ℝ) : 0 < exponentialTransport a := by
  exact neg_pos.mpr (Real.log_neg (normalCDF_pos (-a)) (normalCDF_lt_one (-a)))

/-- Positivity of its derivative makes the scalar transport strictly increasing. -/
theorem strictMono_exponentialTransport : StrictMono exponentialTransport :=
  strictMono_of_hasDerivAt_pos hasDerivAt_exponentialTransport gaussianHazard_pos

/-- Every positive value is attained by the scalar transport. -/
theorem range_exponentialTransport : range exponentialTransport = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact exponentialTransport_pos a
  · intro hy
    have he0 := Real.exp_pos (-y)
    have he1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hy)
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually_lt_const he0).exists
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually_const_lt he1).exists
    obtain ⟨z, hz⟩ := intermediate_value_univ a b contDiff_normalCDF.continuous
      ⟨ha.le, hb.le⟩
    refine ⟨-z, ?_⟩
    simp only [exponentialTransport, neg_neg, hz, Real.log_exp]

/-- The scalar map sends standard Gaussian measure to the mean-one exponential law. -/
theorem map_exponentialTransport :
    (gaussianReal 0 1).map exponentialTransport = expMeasure 1 := by
  have hm := contDiff_exponentialTransport.continuous.measurable
  let : IsProbabilityMeasure ((gaussianReal 0 1).map exponentialTransport) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.eq_of_cdf
  ext y
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic,
    cdf_expMeasure_eq zero_lt_one]
  by_cases hy : 0 < y
  · have hy' : y ∈ range exponentialTransport := by rwa [range_exponentialTransport]
    obtain ⟨a, rfl⟩ := hy'
    have hpre : exponentialTransport ⁻¹' Iic (exponentialTransport a) = Iic a := by
      ext x
      exact strictMono_exponentialTransport.le_iff_le
    rw [hpre, ← cdf_eq_real, if_pos (exponentialTransport_pos a).le]
    change normalCDF a = 1 - Real.exp (-(1 * exponentialTransport a))
    simp only [one_mul, exponentialTransport, neg_neg,
      Real.exp_log (normalCDF_pos (-a))]
    linarith [normalCDF_add_neg a]
  · have hpre : exponentialTransport ⁻¹' Iic y = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_le_of_lt (le_of_not_gt hy) (exponentialTransport_pos x))
    rw [hpre, measureReal_empty]
    split_ifs with h
    · have : y = 0 := le_antisymm (le_of_not_gt hy) h
      simp [this]
    · rfl

/-- A measurable-law formulation for composition with other random variables. -/
theorem hasLaw_exponentialTransport :
    HasLaw exponentialTransport (expMeasure 1) (gaussianReal 0 1) :=
  ⟨contDiff_exponentialTransport.continuous.measurable.aemeasurable,
    map_exponentialTransport⟩

end Submission.Obl.Entropy__lower_bound
