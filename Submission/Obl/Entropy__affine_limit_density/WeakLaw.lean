import Submission.Obl.Entropy__affine_limit_density.Covariance

open MeasureTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__affine_limit_density

/-- L1 convergence of weights is compatible with bounded, pointwise convergent tests. -/
theorem tendsto_integral_varying_density {m : ℕ} {fn : ℕ → E m → ℝ} {f : E m → ℝ}
    (hn : ∀ n, Integrable (fn n) volume) (hf : Integrable f volume)
    (hl1 : Tendsto (fun n => ∫ x, |fn n x - f x|) atTop (𝓝 0))
    {gn : ℕ → E m → ℝ} {g : E m → ℝ} (K : ℝ)
    (hg : ∀ n, AEStronglyMeasurable (gn n) volume)
    (hbound : ∀ n x, ‖gn n x‖ ≤ K)
    (hlim : ∀ x, Tendsto (fun n => gn n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, fn n x * gn n x) atTop (𝓝 (∫ x, f x * g x)) := by
  have hfixed : Tendsto (fun n => ∫ x, f x * gn n x) atTop (𝓝 (∫ x, f x * g x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * K)
      (fun n => hf.aestronglyMeasurable.mul (hg n)) (hf.norm.mul_const K)
    · intro n
      exact Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound n x) (norm_nonneg _)
    · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (hlim x)
  have herr : Tendsto (fun n => (∫ x, fn n x * gn n x) - ∫ x, f x * gn n x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => K * ∫ x, |fn n x - f x|)
    · intro n
      rw [← integral_sub ((hn n).mul_bdd (hg n) (Eventually.of_forall (hbound n)))
        (hf.mul_bdd (hg n) (Eventually.of_forall (hbound n)))]
      calc
        _ ≤ ∫ x, K * |fn n x - f x| := norm_integral_le_of_norm_le
          (((hn n).sub hf).norm.const_mul K) (Eventually.of_forall fun x => by
            rw [← sub_mul, norm_mul, Real.norm_eq_abs]
            exact (mul_le_mul_of_nonneg_left (hbound n x) (abs_nonneg _)).trans_eq
              (mul_comm _ _))
        _ = K * ∫ x, |fn n x - f x| := integral_const_mul _ _
    · simpa using tendsto_const_nhds.mul hl1
  simpa only [sub_add_cancel, zero_add] using herr.add hfixed

 theorem isFinite_density {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume) :
    IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)]
  exact ENNReal.ofReal_lt_top

/-- Identify a limiting transported law from L1 convergence of densities and a.e. convergence
of the source maps. -/
theorem map_eq_of_density_limits {m : ℕ} {μ : Measure (E m)} [IsFiniteMeasure μ]
    {fn : ℕ → E m → ℝ} {f : E m → ℝ}
    (hn0 : ∀ n x, 0 ≤ fn n x) (hn : ∀ n, Integrable (fn n) volume)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hl1 : Tendsto (fun n => ∫ x, |fn n x - f x|) atTop (𝓝 0))
    {Tn : ℕ → E m → E m} {T : E m → E m}
    (hTn : ∀ n, Continuous (Tn n)) (hT : Continuous T)
    (hTlim : ∀ x, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    {Fn : ℕ → E m → E m} {F : E m → E m}
    (hFn : ∀ n, AEMeasurable (Fn n) μ) (hF : AEMeasurable F μ)
    (hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (hlaw : ∀ n, Measure.map (Fn n) μ = Measure.map (Tn n)
      (volume.withDensity (fun x => ENNReal.ofReal (fn n x)))) :
    Measure.map F μ = Measure.map T (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  letI := isFinite_density hf0 hf
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have hleft : Tendsto (fun n => ∫ x, g (Fn n x) ∂μ) atTop
      (𝓝 (∫ x, g (F x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
    · intro n
      exact (g.continuous.measurable.comp_aemeasurable (hFn n)).aestronglyMeasurable
    · exact integrable_const _
    · exact fun n => Eventually.of_forall fun x => g.norm_coe_le_norm _
    · filter_upwards [hFlim] with x hx
      exact g.continuous.continuousAt.tendsto.comp hx
  have hright : Tendsto (fun n => ∫ x, fn n x * g (Tn n x)) atTop
      (𝓝 (∫ x, f x * g (T x))) :=
    tendsto_integral_varying_density hn hf hl1 ‖g‖
      (fun n => (g.continuous.comp (hTn n)).aestronglyMeasurable)
      (fun n x => g.norm_coe_le_norm _) (fun x =>
        g.continuous.continuousAt.tendsto.comp (hTlim x))
  have heq (n : ℕ) : (∫ x, g (Fn n x) ∂μ) = ∫ x, fn n x * g (Tn n x) := by
    rw [← integral_map (hFn n) g.continuous.aestronglyMeasurable, hlaw n,
      integral_map (hTn n).aemeasurable g.continuous.aestronglyMeasurable,
      integral_density (hn0 n) (hn n)]
  simp_rw [heq] at hleft
  rw [integral_map hF g.continuous.aestronglyMeasurable,
    integral_map hT.aemeasurable g.continuous.aestronglyMeasurable,
    integral_density hf0 hf]
  exact tendsto_nhds_unique hleft hright

end Submission.Obl.Entropy__affine_limit_density
