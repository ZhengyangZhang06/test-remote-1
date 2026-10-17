import Mathlib

/-!
# Existence of optimal couplings

Fixed marginals make the family of couplings tight and closed. Prokhorov
compactness and lower semicontinuity of nonnegative continuous costs then yield
an optimal plan. This is the compactness step of the transport existence problem.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace Submission.Obl.Root.OptimalCoupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Probability measures with two prescribed marginals. -/
def couplings (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    Set (ProbabilityMeasure (X × Y)) :=
  {π | π.map measurable_fst.aemeasurable = μ ∧ π.map measurable_snd.aemeasurable = ν}

lemma couplings_nonempty (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (couplings μ ν).Nonempty := by
  exact ⟨μ.prod ν, by simp [couplings]⟩

lemma measurePreserving_fst {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν) :
    MeasurePreserving Prod.fst (π : Measure (X × Y)) (μ : Measure X) :=
  ⟨measurable_fst, congrArg ProbabilityMeasure.toMeasure hπ.1⟩

lemma measurePreserving_snd {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} (hπ : π ∈ couplings μ ν) :
    MeasurePreserving Prod.snd (π : Measure (X × Y)) (ν : Measure Y) :=
  ⟨measurable_snd, congrArg ProbabilityMeasure.toMeasure hπ.2⟩

variable [MetricSpace X] [MetricSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [CompleteSpace X] [CompleteSpace Y]

lemma isClosed_couplings (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsClosed (couplings μ ν) := by
  exact (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)

lemma isTight_couplings (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsTightMeasureSet {((π : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
      π ∈ couplings μ ν} := by
  apply IsTightMeasureSet.prodMk
  · apply (isTightMeasureSet_singleton (μ := (μ : Measure X))).subset
    rintro _ ⟨_, ⟨π, hπ, rfl⟩, rfl⟩
    change (π : Measure (X × Y)).fst = (μ : Measure X)
    exact congrArg ProbabilityMeasure.toMeasure hπ.1
  · apply (isTightMeasureSet_singleton (μ := (ν : Measure Y))).subset
    rintro _ ⟨_, ⟨π, hπ, rfl⟩, rfl⟩
    change (π : Measure (X × Y)).snd = (ν : Measure Y)
    exact congrArg ProbabilityMeasure.toMeasure hπ.2

/-- The fixed-marginal coupling family is weakly compact. -/
lemma isCompact_couplings (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsCompact (couplings μ ν) := by
  have h := isCompact_closure_of_isTightMeasureSet (isTight_couplings μ ν)
  simpa only [(isClosed_couplings μ ν).closure_eq] using h

section Cost

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]

private noncomputable def truncatedCost {c : Z → ℝ≥0} (hc : Continuous c) (n : ℕ) :
    BoundedContinuousFunction Z ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (c x) n, hc.min continuous_const⟩ n (by
    intro x y
    change dist (min (c x) n) (min (c y) n) ≤ (n : ℝ)
    rw [NNReal.dist_eq, abs_le]
    have hx : ((min (c x) n : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast min_le_right (c x) (n : ℝ≥0)
    have hy : ((min (c y) n : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast min_le_right (c y) (n : ℝ≥0)
    constructor <;> linarith [(min (c x) (n : ℝ≥0)).coe_nonneg,
      (min (c y) (n : ℝ≥0)).coe_nonneg])

/-- The integral of a nonnegative continuous cost is weakly lower semicontinuous. -/
lemma lowerSemicontinuous_cost {c : Z → ℝ≥0} (hc : Continuous c) :
    LowerSemicontinuous (fun π : ProbabilityMeasure Z => ∫⁻ x, (c x : ℝ≥0∞) ∂π) := by
  have he (π : ProbabilityMeasure Z) :
      (∫⁻ x, (c x : ℝ≥0∞) ∂π) =
        ⨆ n : ℕ, ∫⁻ x, ((truncatedCost hc n) x : ℝ≥0∞) ∂π := by
    rw [← lintegral_iSup (μ := (π : Measure Z))
      (f := fun n x => ((truncatedCost hc n) x : ℝ≥0∞)) (fun n =>
      ENNReal.continuous_coe.measurable.comp (truncatedCost hc n).continuous.measurable)
      (show Monotone (fun n x => ((truncatedCost hc n) x : ℝ≥0∞)) from by
        intro n k hnk x
        change ((min (c x) n : ℝ≥0) : ℝ≥0∞) ≤ ((min (c x) k : ℝ≥0) : ℝ≥0∞)
        exact ENNReal.coe_le_coe.mpr
          (min_le_min_left (c x) (show (n : ℝ≥0) ≤ k by exact_mod_cast hnk)))]
    apply lintegral_congr
    intro x
    change (c x : ℝ≥0∞) = ⨆ n : ℕ, ((min (c x) n : ℝ≥0) : ℝ≥0∞)
    simp only [ENNReal.coe_min, ENNReal.coe_natCast, ← inf_iSup_eq, ENNReal.iSup_natCast,
      inf_top_eq]
  simp_rw [he]
  exact lowerSemicontinuous_iSup (fun n =>
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (truncatedCost hc n)).lowerSemicontinuous)

end Cost

/-- A continuous nonnegative cost attains its minimum among couplings. -/
theorem exists_optimal_coupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    {c : X × Y → ℝ≥0} (hc : Continuous c) :
    ∃ π ∈ couplings μ ν, ∀ ρ ∈ couplings μ ν,
      (∫⁻ z, (c z : ℝ≥0∞) ∂π) ≤ ∫⁻ z, (c z : ℝ≥0∞) ∂ρ := by
  exact LowerSemicontinuousOn.exists_isMinOn (couplings_nonempty μ ν) (isCompact_couplings μ ν)
    ((lowerSemicontinuous_cost hc).lowerSemicontinuousOn _)

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- Finite second moments of the marginals make the quadratic cost integrable
for every coupling. -/
lemma integrable_quadratic_cost {μ ν : ProbabilityMeasure E}
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    {π : ProbabilityMeasure (E × E)} (hπ : π ∈ couplings μ ν) :
    Integrable (fun z : E × E => ‖z.1 - z.2‖^2) (π : Measure (E × E)) := by
  have hfst : MemLp (Prod.fst : E × E → E) 2 (π : Measure (E × E)) := by
    simpa only [Function.comp_def, id_eq] using hμ.comp_measurePreserving (measurePreserving_fst hπ)
  have hsnd : MemLp (Prod.snd : E × E → E) 2 (π : Measure (E × E)) := by
    simpa only [Function.comp_def, id_eq] using hν.comp_measurePreserving (measurePreserving_snd hπ)
  exact (memLp_two_iff_integrable_sq_norm (hfst.sub hsnd).aestronglyMeasurable).mp (hfst.sub hsnd)

/-- Quadratic optimal transport plans exist for all finite-second-moment laws. -/
theorem exists_quadratic_optimal_coupling (μ ν : ProbabilityMeasure E)
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E)) :
    ∃ π ∈ couplings μ ν,
      Integrable (fun z : E × E => ‖z.1 - z.2‖^2) (π : Measure (E × E)) ∧
      ∀ ρ ∈ couplings μ ν,
        (∫ z, ‖z.1 - z.2‖^2 ∂(π : Measure (E × E))) ≤
          ∫ z, ‖z.1 - z.2‖^2 ∂(ρ : Measure (E × E)) := by
  let c : E × E → ℝ≥0 := fun z => ‖z.1 - z.2‖₊^2
  obtain ⟨π, hπ, hmin⟩ := exists_optimal_coupling μ ν (c := c) (by fun_prop)
  refine ⟨π, hπ, integrable_quadratic_cost hμ hν hπ, fun ρ hρ => ?_⟩
  have hp : Integrable (fun z => (c z : ℝ)) (π : Measure (E × E)) := by
    simpa [c] using integrable_quadratic_cost hμ hν hπ
  have hr : Integrable (fun z => (c z : ℝ)) (ρ : Measure (E × E)) := by
    simpa [c] using integrable_quadratic_cost hμ hν hρ
  have hh := hmin ρ hρ
  rw [lintegral_coe_eq_integral c hp, lintegral_coe_eq_integral c hr] at hh
  have he := ENNReal.toReal_mono (by simp) hh
  have hp0 : 0 ≤ ∫ z, (c z : ℝ) ∂(π : Measure (E × E)) :=
    integral_nonneg (fun z => (c z).coe_nonneg)
  have hr0 : 0 ≤ ∫ z, (c z : ℝ) ∂(ρ : Measure (E × E)) :=
    integral_nonneg (fun z => (c z).coe_nonneg)
  rw [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hr0] at he
  simpa only [c, NNReal.coe_pow, coe_nnnorm] using he

end Quadratic

end Submission.Obl.Root.OptimalCoupling
