import Submission.Obl.Entropy__mollified_convex_sequence.Derivative

open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 400000

namespace Submission.Obl.Entropy__mollified_convex_sequence

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma convex_hessian_nonneg {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : ConvexOn ℝ univ f) (x v : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hd := hf.differentiable (by norm_num)
  have hd2 := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => x+t•v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hg (t : ℝ) : HasDerivAt (fun t : ℝ => f (x+t•v)) (fderiv ℝ f (x+t•v) v) t :=
    (hd (x+t•v)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hline : ConvexOn ℝ univ (fun t : ℝ => f (x+t•v)) := by
    refine ⟨convex_univ, ?_⟩
    intro t _ u _ a b ha hb hab
    have he : x + (a*t+b*u) • v = a • (x+t•v) + b • (x+u•v) := by
      calc
        x + (a*t+b*u) • v = (a+b) • x + (a*t+b*u) • v := by rw [hab, one_smul]
        _ = a • (x+t•v) + b • (x+u•v) := by module
    simpa only [smul_eq_mul, he] using
      hc.2 (mem_univ (x+t•v)) (mem_univ (x+u•v)) ha hb hab
  have he : deriv (fun t : ℝ => f (x+t•v)) = fun t => fderiv ℝ f (x+t•v) v :=
    funext fun t => (hg t).deriv
  have hmono : Monotone (fun t : ℝ => fderiv ℝ f (x+t•v) v) := by
    rw [← he]
    exact monotoneOn_univ.mp (hline.monotoneOn_deriv (fun t _ => (hg t).differentiableAt))
  have hsecond : HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t•v) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t•v))
        (fderiv ℝ (fderiv ℝ f) (x+(0:ℝ)•v) v) 0 :=
      (hd2 (x+(0:ℝ)•v)).hasFDerivAt.comp_hasDerivAt 0 (hp 0)
    have h := hcomp.clm_apply (hasDerivAt_const (0:ℝ) v)
    simpa only [zero_smul, add_zero, map_zero] using h
  rw [← hsecond.deriv]
  exact hmono.deriv_nonneg

lemma hessian_le_of_fderiv_lipschitz {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ L * ‖v‖ ^ 2 := by
  have hnorm : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L :=
    norm_fderiv_le_of_lip' ℝ hL (Eventually.of_forall fun y => hl y x)
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x v v‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x v‖ * ‖v‖ := le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg _)
    _ ≤ (L * ‖v‖) * ‖v‖ := by gcongr
    _ = L * ‖v‖ ^ 2 := by ring

lemma smooth_hessian_bounds (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : ConvexOn ℝ univ f) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖) (x v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (smooth φ f)) x v v ∧
    fderiv ℝ (fderiv ℝ (smooth φ f)) x v v ≤ L * ‖v‖ ^ 2 := by
  constructor
  · exact convex_hessian_nonneg ((smooth_contDiff φ hf.continuous).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤)))
      (smooth_convex φ hf.continuous hc) x v
  · exact hessian_le_of_fderiv_lipschitz hL (smooth_fderiv_lipschitz φ hf hL hl) x v

lemma add_quadratic_hessian {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + c * ‖y‖ ^ 2)) x v v =
      fderiv ℝ (fderiv ℝ f) x v v + 2 * c * ‖v‖ ^ 2 := by
  have hd := hf.differentiable (by norm_num)
  have hd2 := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have he : fderiv ℝ (fun y => f y + c * ‖y‖ ^ 2) =
      fun y => fderiv ℝ f y + c • (2 • innerSL ℝ y) := by
    funext y
    exact ((hd y).hasFDerivAt.add ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul c)).fderiv
  rw [he]
  have h : HasFDerivAt (fun y => fderiv ℝ f y + c • (2 • innerSL ℝ y))
      (fderiv ℝ (fderiv ℝ f) x + c • (2 • innerSL ℝ)) x :=
    (hd2 x).hasFDerivAt.add (by
      simpa only [Pi.smul_def] using
        (((innerSL ℝ).hasFDerivAt (x := x)).const_smul (2:ℕ)).const_smul c)
  rw [h.fderiv]
  have hi : (innerSL ℝ v) v = ‖v‖ ^ 2 :=
    (innerSL_apply_apply ℝ v v).trans (real_inner_self_eq_norm_sq v)
  simp [smul_apply, hi, smul_eq_mul, mul_assoc, mul_comm]

end Submission.Obl.Entropy__mollified_convex_sequence
