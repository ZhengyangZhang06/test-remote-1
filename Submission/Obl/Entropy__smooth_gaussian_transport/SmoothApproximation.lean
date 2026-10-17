import Submission.Obl.Entropy__smooth_gaussian_transport.AlexandrovConvergence
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianBounds
import Submission.Obl.Entropy__smooth_gaussian_transport.ClassicalEquation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem conjugateDomain_eq_univ_of_le {m : ℕ} {u v : E m → ℝ}
    (hu : conjugateDomain u = univ) (huv : ∀ x, u x ≤ v x) :
    conjugateDomain v = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨M, hM⟩ := bounded_conjugate_values hu p
  refine ⟨M, ?_⟩
  rintro z ⟨x, rfl⟩
  exact (sub_le_sub_left (huv x) _).trans (hM (mem_range_self x))

/-- A positive uniform Hessian lower bound makes the gradient injective. -/
theorem gradient_injective_of_positive_hessian {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 2 u) {a : ℝ} (ha : 0 < a)
    (hH : ∀ x z, a * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ u) x z z) :
    Function.Injective (gradient u) := by
  intro x y hxy
  have h₁ := quadratic_lower_bound hu hH x y
  have h₂ := quadratic_lower_bound hu hH y x
  have hderiv : fderiv ℝ u x = fderiv ℝ u y := by
    simpa only [toDual_gradient] using congrArg (InnerProductSpace.toDual ℝ (E m)) hxy
  rw [hderiv] at h₁
  have hsum : fderiv ℝ u y (y - x) + fderiv ℝ u y (x - y) = 0 := by
    rw [← map_add, sub_add_sub_cancel, sub_self, map_zero]
  rw [norm_sub_rev y x] at h₁
  have hnorm : ‖x - y‖ = 0 := by
    have hle : a * ‖x - y‖ ^ 2 ≤ 0 := by nlinarith
    by_contra hn
    exact (mul_pos ha (sq_pos_of_ne_zero hn)).not_ge hle
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Every superlinear finite convex potential admits smooth uniformly convex
majorants converging uniformly on compact sets. Their classical Jacobian
measures converge to the original Alexandrov measure. -/
theorem exists_smooth_convex_alexandrov_approximation {m : ℕ} {v : E m → ℝ}
    (hv : ConvexOn ℝ univ v) (hdv : conjugateDomain v = univ) :
    ∃ u : ℕ → E m → ℝ,
      (∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (u n) ∧ ConvexOn ℝ univ (u n) ∧
        conjugateDomain (u n) = univ ∧ Function.Injective (gradient (u n)) ∧
        ∀ x z, (2 / ((n : ℝ) + 1)) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (u n)) x z z) ∧
      (∀ n x, v x ≤ u n x) ∧
      (∀ K : Set (E m), IsCompact K → TendstoUniformlyOn u v atTop K) ∧
      ∀ f : E m → ℝ, Continuous f → HasCompactSupport f →
        Tendsto (fun n => ∫ x, f x ∂(volume.withDensity
          (fun x => ENNReal.ofReal |(fderiv ℝ (gradient (u n)) x).det|))) atTop
          (𝓝 (∫ x, f x ∂alexandrovMeasure v)) := by
  let φ : ℕ → ContDiffBump (0 : E m) := fun n =>
    { rIn := (1 / ((n : ℝ) + 1)) / 2
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  let w : ℕ → E m → ℝ := fun n =>
    Submission.Obl.Entropy__mollified_convex_sequence.smooth (φ n) v
  let u : ℕ → E m → ℝ := fun n x => w n x + (1 / ((n : ℝ) + 1)) * ‖x‖ ^ 2
  have hw (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (w n) :=
    Submission.Obl.Entropy__mollified_convex_sequence.smooth_contDiff (φ n)
      hv.locallyLipschitz.continuous
  have hw2 (n : ℕ) : ContDiff ℝ 2 (w n) :=
    (hw n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))
  have hwc (n : ℕ) : ConvexOn ℝ univ (w n) :=
    Submission.Obl.Entropy__mollified_convex_sequence.smooth_convex (φ n)
      hv.locallyLipschitz.continuous hv
  have hus (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (u n) :=
    (hw n).add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hu2 (n : ℕ) : ContDiff ℝ 2 (u n) :=
    (hus n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))
  have huH (n : ℕ) (x z : E m) :
      (2 / ((n : ℝ) + 1)) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (u n)) x z z := by
    have hnonneg := Submission.Obl.Entropy__mollified_convex_sequence.convex_hessian_nonneg
      (hw2 n) (hwc n) x z
    change _ ≤ fderiv ℝ (fderiv ℝ (fun y => w n y + (1 / ((n : ℝ) + 1)) * ‖y‖ ^ 2)) x z z
    rw [Submission.Obl.Entropy__mollified_convex_sequence.add_quadratic_hessian (hw2 n)]
    rw [show 2 * (1 / ((n : ℝ) + 1)) = 2 / ((n : ℝ) + 1) by ring]
    linarith
  have huc (n : ℕ) : ConvexOn ℝ univ (u n) :=
    convex_of_hessian_nonneg (hu2 n) (fun x z => (by positivity :
      0 ≤ (2 / ((n : ℝ) + 1)) * ‖z‖ ^ 2).trans (huH n x z))
  have hmajor (n : ℕ) (x : E m) : v x ≤ u n x := by
    have h := Submission.Obl.Entropy__mollified_convex_sequence.le_smooth (φ n)
      hv.locallyLipschitz.continuous hv x
    exact h.trans (le_add_of_nonneg_right (by positivity))
  have hdu (n : ℕ) : conjugateDomain (u n) = univ :=
    conjugateDomain_eq_univ_of_le hdv (hmajor n)
  have hinj (n : ℕ) : Function.Injective (gradient (u n)) :=
    gradient_injective_of_positive_hessian (hu2 n) (by positivity) (huH n)
  have hlim (x : E m) : Tendsto (fun n => u n x) atTop (𝓝 (v x)) := by
    have hwlim : Tendsto (fun n => w n x) atTop (𝓝 (v x)) :=
      ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
        (show Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) from
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hv.locallyLipschitz.continuous x
    simpa only [u, zero_mul, add_zero] using
      hwlim.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖x‖ ^ 2))
  refine ⟨u, fun n => ⟨hus n, huc n, hdu n, hinj n, huH n⟩, hmajor,
    fun K hK => tendstoUniformlyOn_of_convex_pointwise huc hlim hK, ?_⟩
  intro f hf hfK
  have hMA (n : ℕ) := alexandrovMeasure_eq_withDensity_abs_det (huc n) (hdu n)
    ((hu2 n).differentiable (by norm_num))
    (contDiff_one_gradient_of_contDiff_two (hu2 n)).differentiable_one (hinj n)
  simpa only [hMA] using tendsto_integral_alexandrov_of_pointwise huc hv hdu hdv hlim hf hfK

end Submission.Obl.Entropy__smooth_gaussian_transport
