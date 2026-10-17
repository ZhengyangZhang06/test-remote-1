import Submission.Lib.Brenier
import Submission.Lib.EntropyRemainder.GaussianDensity

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Submission.Obl.Entropy__smooth_gaussian_transport

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- A nonnegative density of mass one defines a probability measure. -/
theorem probabilityMeasure_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f μ)
    (hmass : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0), hmass]
  exact ENNReal.ofReal_one

/-- The weighted second-moment assumption is exactly the L2 assumption in Brenier's theorem. -/
theorem memLp_id_withDensity {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume) :
    MemLp (id : E m → E m) 2
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  apply (integrable_withDensity_iff_integrable_smul₀'
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)).2
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, id_eq] using hf2

/-- A positive measurable density has the same support as Lebesgue measure. -/
theorem support_withDensity_eq_univ {m : ℕ} {f : E m → ℝ}
    (hf : Measurable f) (hfpos : ∀ x, 0 < f x) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).support = univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← Measure.support_eq_univ (μ := (volume : Measure (E m)))]
  apply Measure.AbsolutelyContinuous.support_mono
  exact withDensity_absolutelyContinuous' hf.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hfpos x)).ne')

theorem stdGaussian_absolutelyContinuous (m : ℕ) :
    stdGaussian (E m) ≪ volume := by
  rw [Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

theorem support_stdGaussian (m : ℕ) : (stdGaussian (E m)).support = univ := by
  rw [Submission.Lib.EntropyRemainder.stdGaussian_eq_withDensity]
  exact support_withDensity_eq_univ
    Submission.Lib.EntropyRemainder.gaussianDensity_continuous.measurable
    Submission.Lib.EntropyRemainder.gaussianDensity_pos

/-- The measure-theoretic part of the obligation: the target has a continuous convex
potential whose gradient transports the Gaussian. Smoothness is a separate regularity step. -/
theorem exists_continuous_convex_gradient_transport {m : ℕ} {V : E m → ℝ}
    (hVint : Integrable (fun x => Real.exp (-V x)) volume)
    (hVmass : ∫ x, Real.exp (-V x) = 1)
    (hV2 : Integrable (fun x => Real.exp (-V x) * ‖x‖ ^ 2) volume) :
    ∃ φ : E m → ℝ, ConvexOn ℝ univ φ ∧ Continuous φ ∧ Measurable (gradient φ) ∧
      MemLp (gradient φ) 2 (stdGaussian (E m)) ∧
      Measure.map (gradient φ) (stdGaussian (E m)) =
        volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) := by
  let ν : Measure (E m) := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))
  have : IsProbabilityMeasure ν :=
    probabilityMeasure_withDensity (fun x => (Real.exp_pos _).le) hVint hVmass
  have hν2 : MemLp (id : E m → E m) 2 ν :=
    memLp_id_withDensity (fun x => (Real.exp_pos _).le) hVint hV2
  have hγ2 : MemLp (id : E m → E m) 2 (stdGaussian (E m)) :=
    IsGaussian.memLp_two_id
  obtain ⟨φ, hconv, hcont, hmeas, hlaw⟩ :=
    Submission.Lib.Brenier.exists_convex_gradient_transport
      (⟨stdGaussian (E m), inferInstance⟩ : ProbabilityMeasure (E m))
      (⟨ν, inferInstance⟩ : ProbabilityMeasure (E m))
      hγ2 hν2 (stdGaussian_absolutelyContinuous m) (support_stdGaussian m)
  refine ⟨φ, hconv, hcont, hmeas, ?_, hlaw⟩
  change Measure.map (gradient φ) (stdGaussian (E m)) = ν at hlaw
  rw [← hlaw] at hν2
  exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable hmeas.aemeasurable).1 hν2

end Submission.Obl.Entropy__smooth_gaussian_transport
