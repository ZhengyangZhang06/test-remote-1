import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientSchauder
import Submission.Obl.Entropy__smooth_gaussian_transport.AveragedCoefficient
import Submission.Obl.Entropy__smooth_gaussian_transport.CompactLipschitz
import Submission.Obl.Entropy__smooth_gaussian_transport.SegmentDerivative

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem segmentMean_const_sub {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {P : X → Y} (hP : Continuous P) (c : Y) (a b : X) :
    segmentMean (fun z => c - P z) a b = c - segmentMean P a b := by
  have hc : Continuous (fun t : ℝ => P ((1 - t) • a + t • b)) := hP.comp (by fun_prop)
  simp only [segmentMean, intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable 0 1),
    intervalIntegral.integral_const, sub_zero, one_smul]

/-- The first nonlinear regularity step in coordinates where the frozen
principal functional is the trace. The increment identity is the exact
linearization of the nonlinear equation. -/
theorem nonlinear_quotient_regularization {m : ℕ} {f U : E m → ℝ}
    {R : (E m →L[ℝ] ℝ) → ℝ}
    {A : (E m [×2]→L[ℝ] ℝ) → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U)
    (hR : ContDiff ℝ 2 R) (hRc : HasCompactSupport R) (hA : ContDiff ℝ 1 A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hH : UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 f))
    (x : E m) (hAx : A (iteratedFDeriv ℝ 2 f x) = hessianTrace m)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (heq : ∀ z w, ‖z - x‖ < r₀ → ‖w - x‖ < r₀ →
      segmentMean A (iteratedFDeriv ℝ 2 f z) (iteratedFDeriv ℝ 2 f w)
        (iteratedFDeriv ℝ 2 f w - iteratedFDeriv ℝ 2 f z) =
        R (fderiv ℝ f w) - R (fderiv ℝ f z) + (U w - U z))
    (v : E m) :
    ∃ χ : E m → ℝ, (∀ᶠ y in nhds x, χ y = 1) ∧
      ContDiff ℝ 2 (fun y => χ y * fderiv ℝ f y v) ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun y => χ y * fderiv ℝ f y v)) := by
  letI : FiniteDimensional ℝ (E m [×2]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (hessianCurry (E m) ℝ).toLinearEquiv.toLinearMap
      (hessianCurry (E m) ℝ).injective
  obtain ⟨ε, hε, hS⟩ := exists_quotient_schauder_threshold m hα hα1
  obtain ⟨T, hT, hTs, r, hr, hTe⟩ := exists_uniform_small_averaged_coefficient
    (hf.continuous_iteratedFDeriv (by norm_num)).continuousAt hH
    (contDiffAt_const.sub hA.contDiffAt) (by rw [hAx, sub_self]) hε
  let δ : ℝ := min r r₀ / 4
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδr : δ ≤ r / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδr₀ : δ ≤ r₀ / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨χ, hχ, hχc, hχsupp, hχrange, hχone⟩ :=
    exists_compact_smooth_cutoff (Metric.ball_mem_nhds x hδ)
  let c : ℝ := δ / (‖v‖ + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  let h : ℕ → ℝ := fun n => c * (1 / ((n : ℝ) + 1))
  have hh (n : ℕ) : 0 < h n := by dsimp only [h]; positivity
  have hlim : Tendsto h atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hstep (n : ℕ) : ‖h n • v‖ < δ := by
    have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hh' : h n ≤ c := by dsimp only [h]; nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hh n)]
    have hc' : c * (‖v‖ + 1) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg v]
  have hD : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f) :=
    .of_compact_c1 (hf.fderiv_right (by norm_num)) (hfc.fderiv ℝ) hα hα1.le
  have hDD : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ (fderiv ℝ f)) := by
    obtain ⟨M, C, hM, hC, hb, hm⟩ := hH
    refine ⟨M, C, hM, hC, ?_, ?_⟩
    · intro i z; rw [norm_second_fderiv]; exact hb i z
    · intro i z w; rw [norm_second_fderiv_sub]; exact hm i z w
  have hqd := uniformBoundedHolder_quotients (hf.fderiv_right (by norm_num)) hDD h
    (fun n => (hh n).ne') v
  obtain ⟨L, hLip⟩ := compact_c1_lipschitz_global (hR.fderiv_right (by norm_num)) (hRc.fderiv ℝ)
  have hD' : UniformBoundedHolder α (fun (_ : ℕ) => fderiv ℝ f) := hD.reindex (fun _ => ())
  have hav := hD'.segmentMean (hD'.translate (fun n => h n • v)) hLip
  have hqU := uniformBoundedHolder_quotients (hU.of_le (by norm_num))
    (UniformBoundedHolder.of_compact_c1 (hU.fderiv_right (by norm_num)) (hUc.fderiv ℝ) hα hα1.le)
    h (fun n => (hh n).ne') v
  let g : ℕ → E m → ℝ := fun n z =>
    segmentMean (fderiv ℝ R) (fderiv ℝ f z) (fderiv ℝ f (z + h n • v))
      (directionalQuotient (fderiv ℝ f) (h n) v z) + directionalQuotient U (h n) v z
  have hg : UniformBoundedHolder α g := (hav.clm_apply hqd).add hqU
  have hlocal (n : ℕ) (z : E m) (hz : χ z ≠ 0) :
      laplacian (directionalQuotient f (h n) v) z =
        g n z + T (h n • v) z (iteratedFDeriv ℝ 2 (directionalQuotient f (h n) v) z) := by
    have hzδ : ‖z - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hχsupp (subset_closure hz)
    have hzr : ‖z - x‖ < r := by linarith
    have hz₀ : ‖z - x‖ < r₀ := by linarith
    have hzw : ‖z + h n • v - x‖ < r₀ := by
      have he : z + h n • v - x = (z - x) + h n • v := by abel
      rw [he]
      exact (norm_add_le _ _).trans_lt (by linarith [hstep n])
    have hdiff := heq z (z + h n • v) hz₀ hzw
    have hRdiff := segmentMean_fderiv_apply (hR.of_le (by norm_num)) (fderiv ℝ f z) (fderiv ℝ f (z + h n • v))
    rw [hTe _ _ (by linarith [hstep n]) hzr,
      segmentMean_const_sub hA.continuous,
      laplacian_eq_hessianTrace (directionalQuotient_contDiff hf (h n) v),
      directionalQuotient_iteratedFDeriv hf]
    dsimp only [g, directionalQuotient]
    simp only [sub_apply, map_smul, smul_eq_mul]
    rw [hRdiff, hdiff]
    ring
  obtain ⟨hres, hmod⟩ := hS f χ h v g (fun n => T (h n • v)) hf
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ENat) ≤ ⊤))) hχc
    (fun n => (hh n).ne') hlim hD hH hg (hT.reindex (fun n => h n • v))
    (fun n z => hTs _ _) hlocal
  exact ⟨χ, hχone, hres, hmod⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
