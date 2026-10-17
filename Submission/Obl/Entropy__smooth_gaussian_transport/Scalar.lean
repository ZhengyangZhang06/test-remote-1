import Submission.Obl.Entropy__smooth_gaussian_transport.Brenier
import Submission.Lib.GaussianTransport.GaussianModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def scalarCDF (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, f t

noncomputable def scalarQuantile (f : ℝ → ℝ) : ℝ → ℝ := Function.invFun (scalarCDF f)

noncomputable def scalarTransport (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  scalarQuantile f (normalCDF x)

theorem hasDerivAt_scalarCDF {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (x : ℝ) : HasDerivAt (scalarCDF f) (f x) x := by
  have he (y : ℝ) : scalarCDF f y = scalarCDF f 0 + ∫ t in (0 : ℝ)..y, f t := by
    have h := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := y) hi.integrableOn hi.integrableOn
    dsimp [scalarCDF]
    linarith
  exact ((intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    hi.intervalIntegrable hf.stronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt).const_add (scalarCDF f 0)).congr_of_eventuallyEq
      (Eventually.of_forall he)

theorem contDiff_scalarCDF {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hi : Integrable f) :
    ContDiff ℝ ∞ (scalarCDF f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_scalarCDF hf.continuous hi x).differentiableAt, ?_⟩
  have hd : deriv (scalarCDF f) = f :=
    funext fun x => (hasDerivAt_scalarCDF hf.continuous hi x).deriv
  rwa [hd]

theorem strictMono_scalarCDF {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) : StrictMono (scalarCDF f) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_scalarCDF hf hi) hp

theorem scalarCDF_eq_cdf {f : ℝ → ℝ} (hi : Integrable f)
    (hp : ∀ x, 0 ≤ f x) (hm : ∫ x, f x = 1) (x : ℝ) :
    scalarCDF f x = cdf (volume.withDensity (fun y => ENNReal.ofReal (f y))) x := by
  have : IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (f y))) :=
    probabilityMeasure_withDensity hp hi hm
  rw [cdf_eq_real, measureReal_def, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Eventually.of_forall hp),
    ENNReal.toReal_ofReal (integral_nonneg hp)]
  rfl

theorem scalarCDF_mem_Ioo {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) (x : ℝ) : scalarCDF f x ∈ Ioo 0 1 := by
  have hmono := strictMono_scalarCDF hf hi hp
  have hlo : 0 ≤ scalarCDF f (x - 1) := by
    rw [scalarCDF_eq_cdf hi (fun y => (hp y).le) hm]
    exact cdf_nonneg _ _
  have hhi : scalarCDF f (x + 1) ≤ 1 := by
    rw [scalarCDF_eq_cdf hi (fun y => (hp y).le) hm]
    exact cdf_le_one _ _
  exact ⟨hlo.trans_lt (hmono (by linarith)), (hmono (by linarith)).trans_le hhi⟩

theorem range_scalarCDF {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) : range (scalarCDF f) = Ioo 0 1 := by
  have hc : Continuous (scalarCDF f) :=
    Differentiable.continuous (fun x => (hasDerivAt_scalarCDF hf hi x).differentiableAt)
  have he : scalarCDF f = cdf (volume.withDensity (fun y => ENNReal.ofReal (f y))) :=
    funext (scalarCDF_eq_cdf hi (fun y => (hp y).le) hm)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact scalarCDF_mem_Ioo hf hi hp hm x
  · intro hy
    have hbot : Tendsto (scalarCDF f) atBot (𝓝 0) := by rw [he]; exact tendsto_cdf_atBot _
    have htop : Tendsto (scalarCDF f) atTop (𝓝 1) := by rw [he]; exact tendsto_cdf_atTop _
    obtain ⟨a, ha⟩ := (hbot.eventually_lt_const hy.1).exists
    obtain ⟨b, hb⟩ := (htop.eventually_const_lt hy.2).exists
    exact intermediate_value_univ a b hc ⟨ha.le, hb.le⟩

theorem scalarQuantile_scalarCDF {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (x : ℝ) : scalarQuantile f (scalarCDF f x) = x :=
  Function.leftInverse_invFun (strictMono_scalarCDF hf hi hp).injective x

theorem scalarCDF_scalarQuantile {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) {y : ℝ} (hy : y ∈ Ioo 0 1) :
    scalarCDF f (scalarQuantile f y) = y := by
  apply Function.invFun_eq
  change y ∈ range (scalarCDF f)
  rwa [range_scalarCDF hf hi hp hm]

theorem contDiffAt_scalarQuantile {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hi : Integrable f) (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1)
    {y : ℝ} (hy : y ∈ Ioo 0 1) : ContDiffAt ℝ ∞ (scalarQuantile f) y := by
  have hC := contDiff_scalarCDF hf hi
  have hQcont : ContinuousOn (scalarQuantile f) (Ioo 0 1) := by
    intro z hz
    have hd := hC.hasStrictDerivAt (by simp : (∞ : WithTop ENat) ≠ 0)
      (x := scalarQuantile f z)
    have hne : deriv (scalarCDF f) (scalarQuantile f z) ≠ 0 := by
      rw [(hasDerivAt_scalarCDF hf.continuous hi _).deriv]
      exact (hp _).ne'
    have hiQ := hd.to_local_left_inverse hne
      (Eventually.of_forall (scalarQuantile_scalarCDF hf.continuous hi hp))
    rw [scalarCDF_scalarQuantile hf.continuous hi hp hm hz] at hiQ
    exact hiQ.hasDerivAt.continuousAt.continuousWithinAt
  let e : OpenPartialHomeomorph ℝ ℝ :=
    { toFun := scalarCDF f
      invFun := scalarQuantile f
      source := univ
      target := Ioo 0 1
      map_source' := fun x _ => scalarCDF_mem_Ioo hf.continuous hi hp hm x
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun x _ => scalarQuantile_scalarCDF hf.continuous hi hp x
      right_inv' := fun _ hz => scalarCDF_scalarQuantile hf.continuous hi hp hm hz
      open_source := isOpen_univ
      open_target := isOpen_Ioo
      continuousOn_toFun := hC.continuous.continuousOn
      continuousOn_invFun := hQcont }
  exact e.contDiffAt_symm_deriv (hp _).ne' hy
    (hasDerivAt_scalarCDF hf.continuous hi _) hC.contDiffAt

theorem scalarCDF_scalarTransport {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) (x : ℝ) :
    scalarCDF f (scalarTransport f x) = normalCDF x :=
  scalarCDF_scalarQuantile hf hi hp hm ⟨normalCDF_pos x, normalCDF_lt_one x⟩

theorem contDiff_scalarTransport {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hi : Integrable f) (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) :
    ContDiff ℝ ∞ (scalarTransport f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (contDiffAt_scalarQuantile hf hi hp hm ⟨normalCDF_pos x, normalCDF_lt_one x⟩).comp
    x contDiff_normalCDF.contDiffAt

theorem strictMono_scalarTransport {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) : StrictMono (scalarTransport f) := by
  have hG : StrictMono normalCDF :=
    strictMono_of_hasDerivAt_pos hasDerivAt_normalCDF normalPDF_pos
  intro x y hxy
  apply (strictMono_scalarCDF hf hi hp).lt_iff_lt.mp
  simpa only [scalarCDF_scalarTransport hf hi hp hm] using hG hxy

theorem surjective_scalarTransport {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) : Function.Surjective (scalarTransport f) := by
  intro y
  have hy := scalarCDF_mem_Ioo hf hi hp hm y
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually_lt_const hy.1).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually_const_lt hy.2).exists
  obtain ⟨x, hx⟩ := intermediate_value_univ a b contDiff_normalCDF.continuous ⟨ha.le, hb.le⟩
  refine ⟨x, ?_⟩
  change scalarQuantile f (normalCDF x) = y
  rw [hx, scalarQuantile_scalarCDF hf hi hp]

theorem map_scalarTransport {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hi : Integrable f) (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) :
    (gaussianReal 0 1).map (scalarTransport f) =
      volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  have hT := (contDiff_scalarTransport hf hi hp hm).continuous.measurable
  have : IsProbabilityMeasure ((gaussianReal 0 1).map (scalarTransport f)) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (f y))) :=
    probabilityMeasure_withDensity (fun y => (hp y).le) hi hm
  apply Measure.eq_of_cdf
  ext y
  obtain ⟨x, rfl⟩ := surjective_scalarTransport hf.continuous hi hp hm y
  have hpre : scalarTransport f ⁻¹' Iic (scalarTransport f x) = Iic x := by
    ext z
    exact (strictMono_scalarTransport hf.continuous hi hp hm).le_iff_le
  rw [cdf_eq_real, map_measureReal_apply hT measurableSet_Iic, hpre, ← cdf_eq_real,
    ← scalarCDF_eq_cdf hi (fun y => (hp y).le) hm,
    scalarCDF_scalarTransport hf.continuous hi hp hm]
  rfl

/-- Every smooth positive scalar probability density has a smooth convex transport primitive. -/
theorem exists_scalar_smooth_convex_transport {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hi : Integrable f) (hp : ∀ x, 0 < f x) (hm : ∫ x, f x = 1) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ ConvexOn ℝ univ ψ ∧
      (gaussianReal 0 1).map (deriv ψ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let ψ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, scalarTransport f t
  have hT := contDiff_scalarTransport hf hi hp hm
  have hψ (x : ℝ) : HasDerivAt ψ (scalarTransport f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hT.continuous.intervalIntegrable _ _)
      hT.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hT.continuous.continuousAt
  have hd : deriv ψ = scalarTransport f := funext fun x => (hψ x).deriv
  have hs : ContDiff ℝ ∞ ψ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hψ x).differentiableAt, hd ▸ hT⟩
  refine ⟨ψ, hs, ?_, ?_⟩
  · apply Monotone.convexOn_univ_of_deriv (fun x => (hψ x).differentiableAt)
    rw [hd]
    exact (strictMono_scalarTransport hf.continuous hi hp hm).monotone
  · rw [hd]
    exact map_scalarTransport hf hi hp hm

end Submission.Obl.Entropy__smooth_gaussian_transport
