import Submission.Obl.Entropy__transport_integrated_multiplier.Cutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {ι : Type*} [Fintype ι]

/-- A weak identity extends to a bounded C1 test when its derivative products are integrable. -/
theorem integral_mul_eq_neg_sum_of_weak
    (v : ι → E) {f p : E → ℝ} {b : ι → E → ℝ}
    (hf : Integrable f μ) (hb : ∀ r, Integrable (b r) μ)
    (hp : ContDiff ℝ 1 p) (hp_bound : ∃ M : ℝ, ∀ x, ‖p x‖ ≤ M)
    (hp_deriv : ∀ r, Integrable (fun x => fderiv ℝ p x (v r) * b r x) μ)
    (hweak : ∀ z : E → ℝ, ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, z x * f x ∂μ) = -∑ r, ∫ x, fderiv ℝ z x (v r) * b r x ∂μ) :
    (∫ x, p x * f x ∂μ) = -∑ r, ∫ x, fderiv ℝ p x (v r) * b r x ∂μ := by
  have hcut (n : ℕ) : ContDiff ℝ 1 (cutoff (E := E) n) :=
    (cutoff_contDiff n).of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ENat) ≤ ⊤))
  obtain ⟨M, hM⟩ := hp_bound
  have hM0 : 0 ≤ M := (norm_nonneg (p 0)).trans (hM 0)
  obtain ⟨C, hC, hCb⟩ := exists_bound_fderiv_cutoff (E := E)
  let z : ℕ → E → ℝ := fun n x => cutoff n x * p x
  have hz (n : ℕ) : ContDiff ℝ 1 (z n) := (hcut n).mul hp
  have hzc (n : ℕ) : HasCompactSupport (z n) := (cutoff_hasCompactSupport n).mul_right
  have hzderiv (n : ℕ) (x w : E) :
      fderiv ℝ (z n) x w =
        cutoff n x * fderiv ℝ p x w + p x * fderiv ℝ (cutoff n) x w := by
    have hd := fderiv_mul ((hcut n).differentiable (by simp) x)
      (hp.differentiable (by simp) x)
    exact congrArg (fun L => L w) hd
  have hc_bound (n : ℕ) (x : E) : ‖cutoff n x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (cutoff_mem_Icc n x).1]
    exact (cutoff_mem_Icc n x).2
  have hleft : Tendsto (fun n => ∫ x, z n x * f x ∂μ) atTop
      (𝓝 (∫ x, p x * f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => M * ‖f x‖)
    · intro n
      exact (hz n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.norm.const_mul M
    · intro n
      exact ae_of_all _ fun x => by
        change ‖cutoff n x * p x * f x‖ ≤ M * ‖f x‖
        simp only [norm_mul]
        calc
          ‖cutoff n x‖ * ‖p x‖ * ‖f x‖ ≤ 1 * M * ‖f x‖ := by
            gcongr
            · exact hc_bound n x
            · exact hM x
          _ = _ := by ring
    · exact ae_of_all _ fun x => by
        simpa only [z, one_mul] using ((cutoff_tendsto x).mul_const (p x)).mul_const (f x)
  have hright (r : ι) : Tendsto (fun n => ∫ x, fderiv ℝ (z n) x (v r) * b r x ∂μ)
      atTop (𝓝 (∫ x, fderiv ℝ p x (v r) * b r x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖fderiv ℝ p x (v r) * b r x‖ + (M * (C * ‖v r‖)) * ‖b r x‖)
    · intro n
      exact (((hz n).continuous_fderiv (by simp)).eval_const (v r)).aestronglyMeasurable.mul
        (hb r).aestronglyMeasurable
    · exact (hp_deriv r).norm.add ((hb r).norm.const_mul _)
    · intro n
      exact ae_of_all _ fun x => by
        rw [hzderiv, add_mul]
        calc
          _ ≤ ‖cutoff n x * fderiv ℝ p x (v r) * b r x‖ +
              ‖p x * fderiv ℝ (cutoff n) x (v r) * b r x‖ := norm_add_le _ _
          _ ≤ ‖fderiv ℝ p x (v r) * b r x‖ +
              (M * (C * ‖v r‖)) * ‖b r x‖ := by
            simp only [norm_mul]
            gcongr
            · exact mul_le_of_le_one_left (norm_nonneg _) (hc_bound n x)
            · exact hM x
            · exact hCb n x (v r)
    · exact ae_of_all _ fun x => by
        simp only [hzderiv]
        simpa only [one_mul, mul_zero, add_zero] using
          (((cutoff_tendsto x).mul_const (fderiv ℝ p x (v r))).add
            ((fderiv_cutoff_tendsto x (v r)).const_mul (p x))).mul_const (b r x)
  have hs := (tendsto_finsetSum Finset.univ (fun r _ => hright r)).neg
  exact tendsto_nhds_unique hleft (hs.congr' (Eventually.of_forall fun n => (hweak (z n) (hz n) (hzc n)).symm))

end Submission.Obl.Entropy__transport_integrated_multiplier
