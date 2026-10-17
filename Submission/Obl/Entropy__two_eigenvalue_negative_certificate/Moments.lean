import Submission.Lib.GaussianTransport.GaussianTails

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Topology

namespace Submission.Obl.Entropy__two_eigenvalue_negative_certificate

/-- The excess-moment kernel from Appendix A. -/
noncomputable def kernel (r v : ℝ) : ℝ := Real.exp (-r * v - v ^ 2 / 2)

noncomputable def moment (r : ℝ) (j : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), v ^ j * kernel r v

lemma integrable_exp_moment {r : ℝ} (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ j * Real.exp (-r * v)) (Ioi 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (j : ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) j; linarith) (by norm_num) hr)

lemma integral_exp_moment {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (∫ v in Ioi (0 : ℝ), v ^ j * Real.exp (-r * v)) =
      (j.factorial : ℝ) / r ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at h
  simpa only [← neg_mul, one_div, inv_pow, ← div_eq_inv_mul] using h

lemma integrable_moment {r : ℝ} (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ j * kernel r v) (Ioi 0) := by
  refine (integrable_exp_moment hr j).mono' (by unfold kernel; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 ≤ v := le_of_lt hv
  unfold kernel
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv0 _) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v]))
    (pow_nonneg hv0 _)

lemma moment_nonneg (r : ℝ) (j : ℕ) : 0 ≤ moment r j := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro v hv
  exact mul_nonneg (pow_nonneg (le_of_lt hv) _) (Real.exp_pos _).le

lemma moment_upper {r : ℝ} (hr : 0 < r) (j : ℕ) :
    moment r j ≤ (j.factorial : ℝ) / r ^ (j + 1) := by
  rw [← integral_exp_moment hr j]
  apply setIntegral_mono_on (integrable_moment hr j) (integrable_exp_moment hr j)
    measurableSet_Ioi
  intro v hv
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hv) _)
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])

lemma moment_lower {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (j.factorial : ℝ) / r ^ (j + 1) -
      ((j + 2).factorial : ℝ) / (2 * r ^ (j + 3)) ≤ moment r j := by
  have hi := (integrable_exp_moment hr j).sub
    ((integrable_exp_moment hr (j + 2)).div_const 2)
  have h := setIntegral_mono_on hi (integrable_moment hr j) measurableSet_Ioi
    (fun v hv => show v ^ j * Real.exp (-r * v) -
      v ^ (j + 2) * Real.exp (-r * v) / 2 ≤ v ^ j * kernel r v from by
      have he := Real.add_one_le_exp (-(v ^ 2 / 2))
      have hm := mul_le_mul_of_nonneg_left he
        (mul_nonneg (pow_nonneg (le_of_lt hv) j) (Real.exp_pos (-r * v)).le)
      dsimp [kernel]
      rw [show -r * v - v ^ 2 / 2 = -r * v + -(v ^ 2 / 2) by ring, Real.exp_add, pow_add]
      nlinarith)
  dsimp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_exp_moment hr j)
    ((integrable_exp_moment hr (j + 2)).div_const 2), integral_div,
    integral_exp_moment hr j, integral_exp_moment hr (j + 2)] at h
  convert! h using 1 <;> ring

lemma hasDerivAt_kernel (r v : ℝ) :
    HasDerivAt (kernel r) ((-r - v) * kernel r v) v := by
  convert! (((hasDerivAt_id v).const_mul (-r)).sub
    (((hasDerivAt_id v).pow 2).div_const 2)).exp using 1 <;>
    simp [kernel] <;> (first | (funext x; congr 1; ring) | ring)

lemma moment_one {r : ℝ} (hr : 0 < r) : moment r 1 = 1 - r * moment r 0 := by
  have hi : IntegrableOn (kernel r) (Ioi 0) := by
    simpa using integrable_moment hr 0
  have hi' : IntegrableOn (fun v => (-r - v) * kernel r v) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    convert! (hi.const_mul (-r)).sub (integrable_moment hr 1) using 1
    funext v
    simp only [Pi.sub_apply, pow_one]
    ring
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun v _ => hasDerivAt_kernel r v) hi' hi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun v _ => hasDerivAt_kernel r v) hi' ht
  have he : (∫ v in Ioi (0 : ℝ), (-r - v) * kernel r v) =
      -r * moment r 0 - moment r 1 := by
    simp only [moment, pow_zero, one_mul, pow_one]
    rw [← integral_const_mul, ← integral_sub (hi.const_mul (-r))
      (by simpa only [IntegrableOn, pow_one] using integrable_moment hr 1)]
    congr 1
    funext v
    ring
  rw [he] at h
  norm_num [kernel] at h
  linarith

lemma moment_recurrence {r : ℝ} (hr : 0 < r) (j : ℕ) :
    moment r (j + 2) = (j + 1 : ℝ) * moment r j - r * moment r (j + 1) := by
  have hd (v : ℝ) : HasDerivAt (fun v => v ^ (j + 1) * kernel r v)
      (((j + 1 : ℝ) * v ^ j - r * v ^ (j + 1) - v ^ (j + 2)) * kernel r v) v := by
    convert! ((hasDerivAt_id v).pow (j + 1)).mul (hasDerivAt_kernel r v) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul, mul_one, id_eq, Pi.pow_apply] <;> ring
  have hi := ((integrable_moment hr j).const_mul (j + 1 : ℝ)).sub
    ((integrable_moment hr (j + 1)).const_mul r)
  have hi' : IntegrableOn (fun v =>
      (((j + 1 : ℝ) * v ^ j - r * v ^ (j + 1) - v ^ (j + 2)) * kernel r v)) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    convert! hi.sub (integrable_moment hr (j + 2)) using 1
    funext v
    simp only [Pi.sub_apply]
    ring
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun v _ => hd v) hi' (integrable_moment hr (j + 1))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => hd v) hi' ht
  have he : (∫ v in Ioi (0 : ℝ),
      ((j + 1 : ℝ) * v ^ j - r * v ^ (j + 1) - v ^ (j + 2)) * kernel r v) =
      (j + 1 : ℝ) * moment r j - r * moment r (j + 1) - moment r (j + 2) := by
    unfold moment
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((integrable_moment hr j).const_mul _)
        ((integrable_moment hr (j + 1)).const_mul _),
      ← integral_sub (f := fun v => (j + 1 : ℝ) * (v ^ j * kernel r v) -
        r * (v ^ (j + 1) * kernel r v)) hi (integrable_moment hr (j + 2))]
    congr 1
    funext v
    ring
  rw [he] at h
  simp only [zero_pow (Nat.succ_ne_zero _), zero_mul, sub_zero] at h
  linarith

open Submission.Lib.GaussianTransport

lemma normalPDF_add (r v : ℝ) : normalPDF (r + v) = normalPDF r * kernel r v := by
  simp only [normalPDF, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one,
    sub_zero, mul_one, kernel]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

lemma tail_eq_pdf_moment (r : ℝ) : normalCDF (-r) = normalPDF r * moment r 0 := by
  rw [normalCDF_neg_eq_tail]
  have hs : (fun v : ℝ => v + r) '' Ioi 0 = Ioi r := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      change 0 < v at hv
      change r < v + r
      linarith
    · intro hx
      change r < x at hx
      exact ⟨x - r, show 0 < x - r by linarith, sub_add_cancel _ _⟩
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun v : ℝ => v + r) (f' := fun _ => (1 : ℝ))
    (fun v _ => ((hasDerivAt_id v).add_const r).hasDerivWithinAt)
    (fun x _ y _ hxy => add_right_cancel hxy) normalPDF
  rw [hs] at h
  simp only [abs_one, one_smul] at h
  rw [h]
  simp only [moment, pow_zero, one_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [add_comm v, normalPDF_add]

end Submission.Obl.Entropy__two_eigenvalue_negative_certificate
