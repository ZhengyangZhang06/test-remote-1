import Mathlib
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.CDF

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__orthogonal_gaussian_exponential_law

private noncomputable abbrev G := Submission.Obl.Entropy__gaussian_hazard_lipschitz.mass

lemma gaussian_cdf_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [Submission.Obl.Entropy__gaussian_hazard_lipschitz.cdf_eq_mass]
  exact Submission.Obl.Entropy__gaussian_hazard_lipschitz.mass_pos x

lemma continuous_gaussian_cdf : Continuous (cdf (gaussianReal 0 1)) := by
  have he : (cdf (gaussianReal 0 1) : ℝ → ℝ) = G :=
    funext Submission.Obl.Entropy__gaussian_hazard_lipschitz.cdf_eq_mass
  rw [he]
  exact continuous_iff_continuousAt.mpr fun x =>
    (Submission.Obl.Entropy__gaussian_hazard_lipschitz.hasDerivAt_mass x).continuousAt

lemma strictMono_gaussian_cdf : StrictMono (cdf (gaussianReal 0 1)) := by
  have he : (cdf (gaussianReal 0 1) : ℝ → ℝ) = G :=
    funext Submission.Obl.Entropy__gaussian_hazard_lipschitz.cdf_eq_mass
  rw [he]
  exact strictMono_of_hasDerivAt_pos
    Submission.Obl.Entropy__gaussian_hazard_lipschitz.hasDerivAt_mass
    Submission.Obl.Entropy__gaussian_hazard_lipschitz.pdf_pos

lemma gaussian_cdf_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 :=
  (strictMono_gaussian_cdf (show x < x + 1 by linarith)).trans_le (cdf_le_one _ _)

lemma gaussian_cdf_surj {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ∃ x, cdf (gaussianReal 0 1) x = u := by
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value_Ioo
    (by simp : (atBot : Filter ℝ) ≤ 𝓟 (univ : Set ℝ))
    (by simp : (atTop : Filter ℝ) ≤ 𝓟 (univ : Set ℝ))
    continuous_gaussian_cdf.continuousOn
    (tendsto_cdf_atBot (gaussianReal 0 1)) (tendsto_cdf_atTop (gaussianReal 0 1)) hu
  exact ⟨x, hx⟩

lemma continuous_neg_log_gaussian_cdf :
    Continuous (fun x => -Real.log (cdf (gaussianReal 0 1) x)) :=
  (continuous_gaussian_cdf.log (fun x => (gaussian_cdf_pos x).ne')).neg


lemma map_neg_log_gaussian_cdf :
    (gaussianReal 0 1).map (fun x => -Real.log (cdf (gaussianReal 0 1) x)) =
      expMeasure 1 := by
  have : NullSingletonClass (gaussianReal 0 1) :=
    ⟨fun x => gaussianReal_absolutelyContinuous 0 one_ne_zero (measure_singleton x)⟩
  have : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply continuous_neg_log_gaussian_cdf.measurable measurableSet_Iic,
    ← ofReal_cdf, cdf_expMeasure_eq zero_lt_one]
  simp only [one_mul]
  by_cases ht : t ≤ 0
  · have hp : (fun x => -Real.log (cdf (gaussianReal 0 1) x)) ⁻¹' Iic t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hn := Real.log_neg (gaussian_cdf_pos x) (gaussian_cdf_lt_one x)
      change -Real.log (cdf (gaussianReal 0 1) x) ≤ t at hx
      linarith
    rw [hp, measure_empty]
    by_cases h0 : 0 ≤ t
    · have : t = 0 := le_antisymm ht h0
      simp [this]
    · simp [h0]
  · have htpos : 0 < t := lt_of_not_ge ht
    obtain ⟨z, hz⟩ := gaussian_cdf_surj
      (show Real.exp (-t) ∈ Ioo (0 : ℝ) 1 from
        ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos htpos)⟩)
    have hp : (fun x => -Real.log (cdf (gaussianReal 0 1) x)) ⁻¹' Iic t = Ici z := by
      ext x
      change -Real.log (cdf (gaussianReal 0 1) x) ≤ t ↔ z ≤ x
      rw [← strictMono_gaussian_cdf.le_iff_le (a := z) (b := x), hz]
      have he : Real.exp (-t) ≤ cdf (gaussianReal 0 1) x ↔
          -t ≤ Real.log (cdf (gaussianReal 0 1) x) := by
        exact (Real.le_log_iff_exp_le (gaussian_cdf_pos x)).symm
      rw [he]
      constructor <;> intro h <;> linarith
    rw [hp, if_pos htpos.le, ← measure_congr Ioi_ae_eq_Ici, ← compl_Iic,
      prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, hz]
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_sub 1 (Real.exp_pos (-t)).le).symm

/-- Gaussian survival transformed by negative logarithm has the mean-one exponential law. -/
lemma map_gaussian_survival :
    (gaussianReal 0 1).map (fun x => -Real.log (cdf (gaussianReal 0 1) (-x))) =
      expMeasure 1 := by
  have hg : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  rw [show (fun x => -Real.log (cdf (gaussianReal 0 1) (-x))) =
      (fun x => -Real.log (cdf (gaussianReal 0 1) x)) ∘ (fun x => -x) from rfl,
    ← Measure.map_map continuous_neg_log_gaussian_cdf.measurable (by fun_prop),
    hg, map_neg_log_gaussian_cdf]

lemma continuous_gaussian_survival :
    Continuous (fun x => -Real.log (cdf (gaussianReal 0 1) (-x))) :=
  continuous_neg_log_gaussian_cdf.comp continuous_neg

end Submission.Obl.Entropy__orthogonal_gaussian_exponential_law
