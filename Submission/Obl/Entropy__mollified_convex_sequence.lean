import Submission.Obl.Entropy__mollified_convex_sequence.Hessian
import Submission.Obl.Entropy__mollified_convex_sequence.Error
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# Smooth convex majorants

Convolve each potential with an even normalized bump of radius `1 / (n + 1)`,
then add `‖x‖ ^ 2 / (n + 1)`. The convolution preserves convexity and the
Lipschitz constant of the derivative, while its error is at most `1 / (n + 1)`.
The quadratic term supplies the stated positive Hessian lower bound.
-/

open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped Topology
open Submission.Obl.Entropy__mollified_convex_sequence

theorem Submission.Entropy.mollified_convex_sequence : ∀ m : ℕ, 1 ≤ m → ∀ Q : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ 1 (Q n) ∧ ConvexOn ℝ Set.univ (Q n) ∧ ∀ x y : (EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (Q n) x - fderiv ℝ (Q n) y‖ ≤ ((n : ℝ) + 1) * ‖x - y‖) → ∃ U : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (U n) ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), (2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (U n)) x v) v ∧ (fderiv ℝ (fderiv ℝ (U n)) x v) v ≤ ((n : ℝ) + 1 + 2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2) ∧ (∀ n x, Q n x ≤ U n x) ∧ ∀ x, Filter.Tendsto (fun n => U n x - Q n x) Filter.atTop (nhds 0) := by
  intro m hm Q hQ
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) := fun n =>
    { rIn := (1 / ((n:ℝ)+1)) / 2
      rOut := 1 / ((n:ℝ)+1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  let U : ℕ → EuclideanSpace ℝ (Fin m) → ℝ := fun n x =>
    smooth (φ n) (Q n) x + (1 / ((n:ℝ)+1)) * ‖x‖ ^ 2
  have hpos (n : ℕ) : 0 < (n:ℝ)+1 := by positivity
  have hs (n : ℕ) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (smooth (φ n) (Q n)) :=
    smooth_contDiff (φ n) (hQ n).1.continuous
  have hs2 (n : ℕ) : ContDiff ℝ 2 (smooth (φ n) (Q n)) :=
    (hs n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))
  have hmajor (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) : Q n x ≤ U n x := by
    have h := le_smooth (φ n) (hQ n).1.continuous (hQ n).2.1 x
    have hquad : 0 ≤ (1 / ((n:ℝ)+1)) * ‖x‖ ^ 2 := by positivity
    dsimp only [U]
    linarith
  have herr (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
      U n x - Q n x ≤ (1 + ‖x‖ ^ 2) * (1 / ((n:ℝ)+1)) := by
    have h := smooth_error_le (φ n) (hQ n).1 (hpos n).le (hQ n).2.2 x
    have hr : ((n:ℝ)+1) * (1 / ((n:ℝ)+1)) ^ 2 = 1 / ((n:ℝ)+1) := by
      field_simp
    change ‖smooth (φ n) (Q n) x - Q n x‖ ≤ ((n:ℝ)+1) * (1 / ((n:ℝ)+1)) ^ 2 at h
    rw [hr] at h
    have hb := (le_abs_self (smooth (φ n) (Q n) x - Q n x)).trans h
    dsimp only [U]
    nlinarith
  refine ⟨U, ?_, hmajor, ?_⟩
  · intro n
    refine ⟨(hs n).add (contDiff_const.mul (contDiff_norm_sq ℝ)), ?_⟩
    intro x v
    have hb := smooth_hessian_bounds (φ n) (hQ n).1 (hQ n).2.1
      (hpos n).le (hQ n).2.2 x v
    change (2 / ((n:ℝ)+1)) * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (fun y => smooth (φ n) (Q n) y +
          (1 / ((n:ℝ)+1)) * ‖y‖ ^ 2)) x v v ∧
      fderiv ℝ (fderiv ℝ (fun y => smooth (φ n) (Q n) y +
          (1 / ((n:ℝ)+1)) * ‖y‖ ^ 2)) x v v ≤
        ((n:ℝ)+1 + 2 / ((n:ℝ)+1)) * ‖v‖ ^ 2
    rw [add_quadratic_hessian (hs2 n)]
    have he : 2 * (1 / ((n:ℝ)+1)) = 2 / ((n:ℝ)+1) := by ring
    rw [he]
    constructor <;> nlinarith [hb.1, hb.2]
  · intro x
    apply squeeze_zero (fun n => sub_nonneg.mpr (hmajor n x)) (fun n => herr n x)
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1+‖x‖ ^ 2)
