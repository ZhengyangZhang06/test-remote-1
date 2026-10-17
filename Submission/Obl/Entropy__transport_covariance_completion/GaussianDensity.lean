import Mathlib
import Submission.Obl.Entropy__gaussian_hazard_lipschitz.GaussianMoments

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Push a density through a measurable map when the weight is a target function. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {F : α → β} (hF : Measurable F) {g : β → ENNReal} (hg : Measurable g) :
    Measure.map F (μ.withDensity (fun x => g (F x))) = (Measure.map F μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hF]

/-- The product of standard one-dimensional Gaussian measures has product density. -/
theorem gaussian_pi_eq_withDensity (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  have hi : Integrable (fun x : Fin m → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) volume :=
    Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ =>
        (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).le)]
  change ENNReal.ofReal (∫ x, (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi (fun _ : Fin m => volume)).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x =>
      (gaussianPDFReal_pos 0 1 x one_ne_zero).le)]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]

noncomputable def gaussianDensity {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

lemma gaussianDensity_pos {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    0 < gaussianDensity x := Finset.prod_pos fun _ _ => gaussianPDFReal_pos 0 1 _ one_ne_zero

lemma continuous_gaussianDensity (m : ℕ) :
    Continuous (gaussianDensity : EuclideanSpace ℝ (Fin m) → ℝ) := by
  unfold gaussianDensity
  exact continuous_finsetProd _ fun i _ =>
    Submission.Obl.Entropy__gaussian_hazard_lipschitz.continuous_pdf.comp (by fun_prop)

/-- Standard Gaussian measure in the exact Euclidean coordinates used by the obligation. -/
theorem stdGaussian_eq_withDensity (m : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  rw [← map_pi_eq_stdGaussian, gaussian_pi_eq_withDensity]
  have hm := map_withDensity_comp (μ := (volume : Measure (Fin m → ℝ)))
    (F := WithLp.toLp 2) (by fun_prop)
    (g := fun x : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (gaussianDensity x))
    ((continuous_gaussianDensity m).measurable.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp (Fin m)).map_eq] at hm
  exact hm

/-- The logarithm of the Gaussian density, with its normalization constant. -/
theorem log_gaussianDensity {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    Real.log (gaussianDensity x) =
      -(m : ℝ) * Real.log (2 * Real.pi) / 2 - ‖x‖^2 / 2 := by
  rw [gaussianDensity, Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')]
  have h (a : ℝ) : Real.log (gaussianPDFReal 0 1 a) =
      -Real.log (2 * Real.pi) / 2 - a^2 / 2 := by
    change Real.log (Submission.Obl.Entropy__gaussian_hazard_lipschitz.pdf a) = _
    rw [Submission.Obl.Entropy__gaussian_hazard_lipschitz.pdf_formula,
      Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne') (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp, Real.log_sqrt (by positivity)]
    ring
  simp_rw [h]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, EuclideanSpace.real_norm_sq_eq]
  ring

/-- The standard Gaussian has total second moment equal to the dimension. -/
theorem integral_norm_sq_stdGaussian (m : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin m), ‖x‖^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = m := by
  have hsq : (∫ t : ℝ, t^2 ∂gaussianReal 0 1) = 1 := by
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simpa only [id_eq, integral_id_gaussianReal, sub_zero, NNReal.coe_one] using hv
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  have hi : Integrable (fun t : ℝ => t^2) (gaussianReal 0 1) :=
    (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq
  have hci (i : Fin m) : Integrable (fun x : Fin m → ℝ => (x i)^2)
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
    integrable_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i) hi
  rw [integral_finsetSum Finset.univ (fun i _ => hci i)]
  simp_rw [integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t^2)
    (gaussianReal 0 1)), hsq]
  simp

lemma integrable_norm_sq_stdGaussian (m : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  IsGaussian.memLp_two_id.norm.integrable_sq

lemma integrable_log_gaussianDensity (m : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => Real.log (gaussianDensity x))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  simp_rw [log_gaussianDensity]
  exact (integrable_const _).sub ((integrable_norm_sq_stdGaussian m).div_const 2)

/-- Expected log density, the normalization entering entropy change of variables. -/
theorem integral_log_gaussianDensity (m : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin m), Real.log (gaussianDensity x)
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
        -(m : ℝ) * Real.log (2 * Real.pi) / 2 - (m : ℝ) / 2 := by
  simp_rw [log_gaussianDensity]
  rw [integral_sub (integrable_const _) ((integrable_norm_sq_stdGaussian m).div_const 2),
    integral_const, integral_div, integral_norm_sq_stdGaussian]
  simp

end Submission.Obl.Entropy__transport_covariance_completion
