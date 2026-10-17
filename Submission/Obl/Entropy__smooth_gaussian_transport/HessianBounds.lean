import Submission.Obl.Entropy__smooth_gaussian_transport.Brenier
import Submission.Obl.Entropy__mollified_convex_sequence.Hessian

open Set Filter
open scoped ContDiff RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Integrating a lower Hessian bound along a line gives a quadratic supporting function. -/
theorem quadratic_lower_bound {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (x y : E m) :
    V x + fderiv ℝ V x (y - x) + a / 2 * ‖y - x‖ ^ 2 ≤ V y := by
  let v := y - x
  let g : ℝ → ℝ := fun t => V (x + t • v) - a / 2 * t ^ 2 * ‖v‖ ^ 2
  let g' : ℝ → ℝ := fun t => fderiv ℝ V (x + t • v) v - a * t * ‖v‖ ^ 2
  have hVd := hV.differentiable (by norm_num)
  have hVdd := (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have h₁ := (hVd (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)
    have h₂ : HasDerivAt (fun t : ℝ => a / 2 * t ^ 2 * ‖v‖ ^ 2)
        (a * t * ‖v‖ ^ 2) t := by
      convert! (((hasDerivAt_id t).pow 2).const_mul (a / 2)).mul_const (‖v‖ ^ 2)
        using 1
      simp only [id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
      ring
    exact h₁.sub h₂
  have hg' (t : ℝ) : HasDerivAt g'
      (fderiv ℝ (fderiv ℝ V) (x + t • v) v v - a * ‖v‖ ^ 2) t := by
    have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v))
        (fderiv ℝ (fderiv ℝ V) (x + t • v) v) t :=
      (hVdd (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)
    have h₁ : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v) v)
        (fderiv ℝ (fderiv ℝ V) (x + t • v) v v) t := by
      simpa only [map_zero, add_zero] using hcomp.clm_apply (hasDerivAt_const t v)
    have h₂ : HasDerivAt (fun t : ℝ => a * t * ‖v‖ ^ 2) (a * ‖v‖ ^ 2) t := by
      simpa using ((hasDerivAt_id t).const_mul a).mul_const (‖v‖ ^ 2)
    exact h₁.sub h₂
  have hm : Monotone g' := monotone_of_hasDerivAt_nonneg hg' (fun t => sub_nonneg.mpr (ha _ _))
  have hc : ConvexOn ℝ univ g := by
    apply Monotone.convexOn_univ_of_deriv (fun t => (hg t).differentiableAt)
    have he : deriv g = g' := funext (fun t => (hg t).deriv)
    rwa [he]
  have hs := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num) (hg 0)
  simp only [slope, g, g', zero_smul, add_zero, zero_pow (by decide : 2 ≠ 0),
    one_smul, one_pow, mul_zero, zero_mul, sub_zero, mul_one, inv_one] at hs
  dsimp [v] at hs
  simp only [add_sub_cancel] at hs
  linarith

/-- A nonnegative Hessian on the full space implies convexity. -/
theorem convex_of_hessian_nonneg {m : ℕ} {V : E m → ℝ}
    (hV : ContDiff ℝ 2 V)
    (hH : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    ConvexOn ℝ univ V := by
  have hs (x y : E m) : V x + fderiv ℝ V x (y - x) ≤ V y := by
    simpa using quadratic_lower_bound (a := 0) hV (by simpa using hH) x y
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hs z x) ha
  have hy := mul_le_mul_of_nonneg_left (hs z y) hb
  have he : a * fderiv ℝ V z (x - z) + b * fderiv ℝ V z (y - z) = 0 := by
    have hz : a • (x - z) + b • (y - z) = 0 := by
      calc
        _ = a • x + b • y - (a + b) • z := by module
        _ = 0 := by rw [hab, one_smul]; exact sub_self z
    simpa only [map_add, map_smul, smul_eq_mul, map_zero] using
      congrArg (fderiv ℝ V z) hz
  change V z ≤ a * V x + b * V y
  have hez : (a + b) * V z = V z := by rw [hab, one_mul]
  nlinarith only [hx, hy, he, hez]

/-- The lower Hessian constant is a strong-convexity modulus for the target potential. -/
theorem strongConvexOn_of_hessian_lower {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    StrongConvexOn univ a V := by
  rw [strongConvexOn_iff_convex]
  have he : (fun x => V x - a / 2 * ‖x‖ ^ 2) =
      (fun x => V x + (-a / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [he]
  apply convex_of_hessian_nonneg
  · exact hV.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  · intro x v
    rw [Submission.Obl.Entropy__mollified_convex_sequence.add_quadratic_hessian hV]
    have h := ha x v
    nlinarith

/-- Both sides of the Hessian hypothesis yield global second-order bounds. -/
theorem quadratic_bounds {m : ℕ} {V : E m → ℝ} {a b : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v ∧
      fderiv ℝ (fderiv ℝ V) x v v ≤ b * ‖v‖ ^ 2)
    (x y : E m) :
    V x + fderiv ℝ V x (y - x) + a / 2 * ‖y - x‖ ^ 2 ≤ V y ∧
      V y ≤ V x + fderiv ℝ V x (y - x) + b / 2 * ‖y - x‖ ^ 2 := by
  refine ⟨quadratic_lower_bound hV (fun x v => (hH x v).1) x y, ?_⟩
  have hd := hV.differentiable (by norm_num)
  have hdd := (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have he : fderiv ℝ (-V) = fun x => -fderiv ℝ V x := by
    funext x
    exact (hd x).hasFDerivAt.neg.fderiv
  have hn := quadratic_lower_bound (V := -V) (a := -b) hV.neg (by
    intro z v
    rw [he]
    change -b * ‖v‖ ^ 2 ≤ fderiv ℝ (-fderiv ℝ V) z v v
    rw [(hdd z).hasFDerivAt.neg.fderiv]
    simp only [neg_apply]
    nlinarith [(hH z v).2]) x y
  rw [he] at hn
  simp only [Pi.neg_apply, neg_apply] at hn
  linarith

/-- A positive lower Hessian bound gives a coercive quadratic minorant. -/
theorem exists_quadratic_minorant {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    ∃ C : ℝ, ∀ x, a / 4 * ‖x‖ ^ 2 - C ≤ V x := by
  let L := ‖fderiv ℝ V 0‖
  refine ⟨L ^ 2 / a - V 0, fun x => ?_⟩
  have hq := quadratic_lower_bound hV hH 0 x
  simp only [sub_zero] at hq
  have hl : -(L * ‖x‖) ≤ fderiv ℝ V 0 x :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using (fderiv ℝ V 0).le_opNorm x)).1
  have hs : 0 ≤ a / 4 * ‖x‖ ^ 2 - L * ‖x‖ + L ^ 2 / a := by
    apply nonneg_of_mul_nonneg_right (a := a) _ ha
    have he : a * (a / 4 * ‖x‖ ^ 2 - L * ‖x‖ + L ^ 2 / a) =
        (a * ‖x‖ / 2 - L) ^ 2 := by
      field_simp [ha.ne']
      ring
    rw [he]
    exact sq_nonneg _
  linarith

theorem tendsto_atTop_of_hessian_lower {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    Tendsto V (cocompact (E m)) atTop := by
  obtain ⟨C, hC⟩ := exists_quadratic_minorant hV ha hH
  have hp : Tendsto (fun x : E m => ‖x‖ ^ 2) (cocompact (E m)) atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_norm_cocompact_atTop
  have hmul : Tendsto (fun x : E m => a / 4 * ‖x‖ ^ 2) (cocompact (E m)) atTop :=
    Tendsto.const_mul_atTop (by positivity) hp
  apply tendsto_atTop_mono hC
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right (cocompact (E m)) (-C) hmul

/-- All sublevel sets of a uniformly convex smooth target are compact. -/
theorem isCompact_sublevel_of_hessian_lower {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) (r : ℝ) :
    IsCompact {x | V x ≤ r} := by
  have he := (tendsto_atTop_of_hessian_lower hV ha hH).eventually (eventually_gt_atTop r)
  obtain ⟨K, hK, hsub⟩ := mem_cocompact'.mp he
  apply hK.of_isClosed_subset (isClosed_le hV.continuous continuous_const)
  intro x hx
  exact hsub (by simpa only [mem_compl_iff, mem_ofPred_eq, not_lt] using hx)

theorem exists_minimizer_of_hessian_lower {m : ℕ} {V : E m → ℝ} {a : ℝ}
    (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    ∃ x, ∀ y, V x ≤ V y :=
  hV.continuous.exists_forall_le (tendsto_atTop_of_hessian_lower hV ha hH)

end Submission.Obl.Entropy__smooth_gaussian_transport
