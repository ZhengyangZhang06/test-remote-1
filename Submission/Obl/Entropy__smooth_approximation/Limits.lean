import Submission.Obl.Entropy__smooth_approximation.Normalization

open MeasureTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_approximation

lemma density_continuous {m : ℕ} {V : E m → ℝ} (hV : SmoothPotential V) :
    Continuous (density V) := Real.continuous_exp.comp hV.1.continuous.neg

/-- The last paragraph of Lemma 5.2: normalize a dominated smooth approximation.
The two majorants control the second moment and the entropy integrand. -/
theorem approximation_of_dominated {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume) (hmass : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    {U : ℕ → E m → ℝ} (hU : ∀ n, SmoothPotential (U n))
    {B C : E m → ℝ} (hB : Integrable B volume) (hC : Integrable C volume)
    (hbound : ∀ n x, density (U n) x * (1 + ‖x‖ ^ 2) ≤ B x)
    (hent : ∀ n x, |density (U n) x * Real.log (density (U n) x)| ≤ C x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => density (U n) x) atTop (𝓝 (f x))) :
    ∃ V : ℕ → E m → ℝ, (∀ n, Regular (V n)) ∧
      Tendsto (fun n => entropy (density (V n))) atTop (𝓝 (entropy f)) ∧
      (∀ i j, Tendsto (fun n => covariance (density (V n)) i j) atTop
        (𝓝 (covariance f i j))) ∧
      Tendsto (fun n => mean (density (V n))) atTop (𝓝 (mean f)) ∧
      Tendsto (fun n => ∫ x, |density (V n) x - f x|) atTop (𝓝 0) := by
  let g := fun n => density (U n)
  have hg0 (n : ℕ) (x : E m) : 0 ≤ g n x := (Real.exp_pos _).le
  have hgcont (n : ℕ) : Continuous (g n) := density_continuous (hU n)
  have hgB (n : ℕ) (x : E m) : g n x ≤ B x := by
    calc
      g n x ≤ g n x * (1 + ‖x‖ ^ 2) := by nlinarith [mul_nonneg (hg0 n x) (sq_nonneg ‖x‖)]
      _ ≤ B x := hbound n x
  have hg2B (n : ℕ) (x : E m) : g n x * ‖x‖ ^ 2 ≤ B x := by
    calc
      g n x * ‖x‖ ^ 2 ≤ g n x * (1 + ‖x‖ ^ 2) := by nlinarith [hg0 n x]
      _ ≤ B x := hbound n x
  have hgi (n : ℕ) : Integrable (g n) volume := by
    apply hB.mono' (hgcont n).aestronglyMeasurable
    exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 n x)] using hgB n x
  have hgi2 (n : ℕ) : Integrable (fun x => g n x * ‖x‖ ^ 2) volume := by
    apply hB.mono' ((hgcont n).mul (continuous_norm.pow 2)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖g n x * ‖x‖ ^ 2‖ ≤ B x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 n x) (sq_nonneg ‖x‖))]
      exact hg2B n x
  have hgie (n : ℕ) : Integrable (fun x => g n x * Real.log (g n x)) volume := by
    have hc : Continuous (fun x => g n x * Real.log (g n x)) :=
      Real.continuous_mul_log.comp (hgcont n)
    apply hC.mono' hc.aestronglyMeasurable
    exact Eventually.of_forall fun x => hent n x
  let Z := fun n => ∫ x, g n x
  have hZpos (n : ℕ) : 0 < Z n := mass_pos (hgi n)
  have hZ : Tendsto Z atTop (𝓝 1) := by
    rw [← hmass]
    apply tendsto_integral_of_dominated_convergence B
      (fun n => (hgcont n).aestronglyMeasurable) hB _ hlim
    intro n
    exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 n x)] using hgB n x
  have hZi : Tendsto (fun n => (Z n)⁻¹) atTop (𝓝 1) := by
    simpa using hZ.inv₀ (by norm_num)
  have hZib : ∀ᶠ n in atTop, (Z n)⁻¹ ≤ 2 :=
    (hZi.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono fun n hn => hn.le
  let V := fun n x => U n x + Real.log (Z n)
  have hreg (n : ℕ) : Regular (V n) := normalized_regular (hU n) (hgi n) (hgi2 n) (hgie n)
  have hVeq (n : ℕ) (x : E m) : density (V n) x = (Z n)⁻¹ * g n x :=
    density_normalize (U n) (hZpos n) x
  have hV0 (n : ℕ) (x : E m) : 0 ≤ density (V n) x := (Real.exp_pos _).le
  have hVlim : ∀ᵐ x ∂volume, Tendsto (fun n => density (V n) x) atTop (𝓝 (f x)) := by
    filter_upwards [hlim] with x hx
    simpa only [hVeq, one_mul] using hZi.mul hx
  have hVB : ∀ᶠ n in atTop, ∀ x, density (V n) x * (1 + ‖x‖ ^ 2) ≤ 2 * B x := by
    filter_upwards [hZib] with n hn x
    rw [hVeq, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hbound n x) (inv_pos.mpr (hZpos n)).le).trans
      (mul_le_mul_of_nonneg_right hn ((hg0 n x).trans (hgB n x)))
  have hVB0 : ∀ᶠ n in atTop, ∀ x, density (V n) x ≤ 2 * B x := by
    filter_upwards [hVB] with n hn x
    exact (show density (V n) x ≤ density (V n) x * (1 + ‖x‖ ^ 2) by
      nlinarith [mul_nonneg (hV0 n x) (sq_nonneg ‖x‖)]).trans (hn x)
  have hVB2 : ∀ᶠ n in atTop, ∀ x, density (V n) x * ‖x‖ ^ 2 ≤ 2 * B x := by
    filter_upwards [hVB] with n hn x
    exact (show density (V n) x * ‖x‖ ^ 2 ≤ density (V n) x * (1 + ‖x‖ ^ 2) by
      nlinarith [hV0 n x]).trans (hn x)
  have hmean : Tendsto (fun n => mean (density (V n))) atTop (𝓝 (mean f)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 2 * B x)
      (Eventually.of_forall fun n => (Submission.Lib.EntropyTools.integrable_density_smul
        (hV0 n) (hreg n).2.1 (hreg n).2.2.2.1).aestronglyMeasurable)
      ?_ (hB.const_mul 2) ?_
    · filter_upwards [hVB] with n hn
      exact Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hV0 n x)]
        calc
          density (V n) x * ‖x‖ ≤ density (V n) x * (1 + ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖x‖ - 1)]) (hV0 n x)
          _ ≤ 2 * B x := hn x
    · filter_upwards [hVlim] with x hx
      exact hx.smul_const x
  have hfirst (i : Fin m) : Tendsto (fun n => ∫ x, density (V n) x * x i) atTop
      (𝓝 (∫ x, f x * x i)) := by
    have hi := (EuclideanSpace.proj i).continuous.tendsto (mean f) |>.comp hmean
    change Tendsto (fun n => mean (density (V n)) i) atTop (𝓝 (mean f i)) at hi
    simpa only [mean, Submission.Lib.EntropyTools.density_mean_apply hf0 hf hf2,
      Submission.Lib.EntropyTools.density_mean_apply (hV0 _) (hreg _).2.1 (hreg _).2.2.2.1] using hi
  have hsecond (i j : Fin m) : Tendsto (fun n => ∫ x, density (V n) x * x i * x j) atTop
      (𝓝 (∫ x, f x * x i * x j)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 2 * B x)
      (Eventually.of_forall fun n => by
        exact ((density_continuous (hreg n).1).mul (by fun_prop) |>.mul
          (by fun_prop)).aestronglyMeasurable)
      ?_ (hB.const_mul 2) ?_
    · filter_upwards [hVB2] with n hn
      exact Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hV0 n x)]
        calc
          density (V n) x * ‖x i‖ * ‖x j‖ ≤ density (V n) x * ‖x‖ ^ 2 := by
            have hb := mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
              (norm_nonneg _) (norm_nonneg _)
            nlinarith [mul_le_mul_of_nonneg_left hb (hV0 n x)]
          _ ≤ 2 * B x := hn x
    · filter_upwards [hVlim] with x hx
      exact (hx.mul_const (x i)).mul_const (x j)
  have hentropyraw : Tendsto (fun n => entropy (g n)) atTop (𝓝 (entropy f)) := by
    apply Tendsto.neg
    apply tendsto_integral_of_dominated_convergence C
      (fun n => (hgie n).aestronglyMeasurable) hC
      (fun n => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hent n x)
    filter_upwards [hlim] with x hx
    exact Real.continuous_mul_log.continuousAt.tendsto.comp hx
  refine ⟨V, hreg, ?_, ?_, hmean, ?_⟩
  · have heq (n : ℕ) : entropy (density (V n)) =
        (Z n)⁻¹ * entropy (g n) + Real.log (Z n) := entropy_normalize (hgi n) (hgie n)
    simp only [heq]
    simpa using (hZi.mul hentropyraw).add (hZ.log (by norm_num))
  · exact Submission.Lib.EntropyTools.densityCovariance_tendsto_of_moments
      hf0 hf hmass hf2 hV0 (fun n => (hreg n).2.1) (fun n => (hreg n).2.2.1)
      (fun n => (hreg n).2.2.2.1) hfirst hsecond
  · have hi := tendsto_integral_filter_of_dominated_convergence
      (F := fun n x => |density (V n) x - f x|) (f := fun _ => (0 : ℝ))
      (fun x => 2 * B x + |f x|)
      (Eventually.of_forall fun n => ((hreg n).2.1.sub hf).abs.aestronglyMeasurable)
      ?_ ((hB.const_mul 2).add hf.abs) ?_
    · simpa using hi
    · filter_upwards [hVB0] with n hn
      exact Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (add_le_add_right (by
          simpa only [abs_of_nonneg (hV0 n x)] using hn x) _)
    · filter_upwards [hVlim] with x hx
      simpa using (hx.sub_const (f x)).abs

end Submission.Obl.Entropy__smooth_approximation
