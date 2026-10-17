import Submission.Lib.GaussianTransport.GaussianSlope

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Root.GaussianCurvature

open Submission.Lib.GaussianTransport

/-- Gaussian integration by parts gives every polynomial tail moment recursively. -/
theorem integral_pow_succ_succ_tail (a : ℝ) (n : ℕ) :
    (∫ x in Ioi a, x ^ (n + 2) * normalPDF x) =
      a ^ (n + 1) * normalPDF a + (n + 1 : ℝ) * ∫ x in Ioi a, x ^ n * normalPDF x := by
  have hd (x : ℝ) : HasDerivAt (fun x => x ^ (n + 1) * normalPDF x)
      ((n + 1 : ℝ) * (x ^ n * normalPDF x) - x ^ (n + 2) * normalPDF x) x := by
    have h := ((hasDerivAt_id x).pow (n + 1)).mul (hasDerivAt_normalPDF x)
    change HasDerivAt (fun x => x ^ (n + 1) * normalPDF x) _ x at h
    apply h.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [pow_succ]
    ring
  have hi := ((integrable_pow_mul_normalPDF n).const_mul (n + 1 : ℝ)).sub
    (integrable_pow_mul_normalPDF (n + 2))
  have ht : Tendsto (fun x => x ^ (n + 1) * normalPDF x) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hd x)
      hi.integrableOn (integrable_pow_mul_normalPDF (n + 1)).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    hi.integrableOn ht (a := a)
  rw [integral_sub ((integrable_pow_mul_normalPDF n).const_mul (n + 1 : ℝ)).integrableOn
    (integrable_pow_mul_normalPDF (n + 2)).integrableOn, integral_const_mul] at h
  linarith

theorem integral_cube_tail (a : ℝ) :
    (∫ x in Ioi a, x ^ 3 * normalPDF x) = (a ^ 2 + 2) * normalPDF a := by
  have h := integral_pow_succ_succ_tail a 1
  norm_num only [Nat.cast_one, Nat.reduceAdd, one_add_one_eq_two, pow_one] at h
  rw [integral_mul_normalPDF_tail] at h
  linarith

theorem integral_fourth_tail (a : ℝ) :
    (∫ x in Ioi a, x ^ 4 * normalPDF x) =
      (a ^ 3 + 3 * a) * normalPDF a + 3 * normalCDF (-a) := by
  have h := integral_pow_succ_succ_tail a 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  rw [integral_sq_mul_normalPDF_tail] at h
  linarith

theorem integrable_quadratic_sq (c b : ℝ) :
    Integrable (fun x : ℝ => (x ^ 2 - c * x - b) ^ 2 * normalPDF x) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have h1 : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have h := ((((integrable_pow_mul_normalPDF 4).add
    ((integrable_pow_mul_normalPDF 3).const_mul (-2 * c))).add
    ((integrable_pow_mul_normalPDF 2).const_mul (c ^ 2 - 2 * b))).add
    (h1.const_mul (2 * c * b))).add (hp.const_mul (b ^ 2))
  convert! h using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- No monic quadratic vanishes almost everywhere on a Gaussian tail. -/
theorem integral_quadratic_sq_pos (a c b : ℝ) :
    0 < ∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (normalPDF_pos x).le))
    (integrable_quadratic_sq c b).integrableOn).2
  have hs : Ioi (max a (|c| + |b| + 2)) ⊆
      Function.support (fun x => (x ^ 2 - c * x - b) ^ 2 * normalPDF x) ∩ Ioi a := by
    intro x hx
    have ha : a < x := (le_max_left _ _).trans_lt hx
    have hx' : |c| + |b| + 2 < x := (le_max_right _ _).trans_lt hx
    have hx0 : 0 < x := by linarith [abs_nonneg c, abs_nonneg b]
    have hcx := mul_le_mul_of_nonneg_right (le_abs_self c) hx0.le
    have hprod : 0 < x * (x - |c| - 1) := mul_pos hx0 (by linarith [abs_nonneg b])
    have hpoly : 0 < x ^ 2 - c * x - b := by
      nlinarith [le_abs_self b, abs_nonneg c]
    exact ⟨mul_ne_zero (pow_ne_zero _ hpoly.ne') (normalPDF_pos x).ne', ha⟩
  have hmeasure := measure_mono (μ := volume) hs
  rw [Real.volume_Ioi] at hmeasure
  exact ENNReal.zero_lt_top.trans_le hmeasure

theorem integral_quadratic_sq_tail (a c b : ℝ) :
    (∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x) =
      (a ^ 3 + 3 * a) * normalPDF a + 3 * normalCDF (-a) +
      (-2 * c) * ((a ^ 2 + 2) * normalPDF a) +
      (c ^ 2 - 2 * b) * (a * normalPDF a + normalCDF (-a)) +
      (2 * c * b) * normalPDF a + b ^ 2 * normalCDF (-a) := by
  have hp : Integrable normalPDF := integrable_gaussianPDFReal 0 1
  have h1 : Integrable (fun x => x * normalPDF x) := by
    simpa only [pow_one] using integrable_pow_mul_normalPDF 1
  have h4 := (integrable_pow_mul_normalPDF 4).integrableOn (s := Ioi a)
  have h3 := ((integrable_pow_mul_normalPDF 3).const_mul (-2 * c)).integrableOn (s := Ioi a)
  have h2 := ((integrable_pow_mul_normalPDF 2).const_mul (c ^ 2 - 2 * b)).integrableOn (s := Ioi a)
  have h1' := (h1.const_mul (2 * c * b)).integrableOn (s := Ioi a)
  have h0 := (hp.const_mul (b ^ 2)).integrableOn (s := Ioi a)
  have heq (x : ℝ) : (x ^ 2 - c * x - b) ^ 2 * normalPDF x =
      x ^ 4 * normalPDF x + (-2 * c) * (x ^ 3 * normalPDF x) +
      (c ^ 2 - 2 * b) * (x ^ 2 * normalPDF x) +
      (2 * c * b) * (x * normalPDF x) + b ^ 2 * normalPDF x := by ring
  simp_rw [heq]
  have hs4 := integral_add (((h4.add h3).add h2).add h1') h0
  have hs3 := integral_add ((h4.add h3).add h2) h1'
  have hs2 := integral_add (h4.add h3) h2
  have hs1 := integral_add h4 h3
  simp only [Pi.add_apply] at hs4 hs3 hs2 hs1
  rw [hs4, hs3, hs2, hs1]
  simp only [integral_const_mul, integral_fourth_tail, integral_cube_tail,
    integral_sq_mul_normalPDF_tail, integral_mul_normalPDF_tail, ← normalCDF_neg_eq_tail]

/-- Strict positivity of the degree-two Gaussian tail moment determinant. -/
theorem tail_moment_determinant_pos (a : ℝ) :
    0 < (1 - a * gaussianGap a) * (2 - a * gaussianGap a) -
      gaussianGap a ^ 2 * (3 - a * gaussianGap a) := by
  let q := gaussianHazard a
  let r := 1 + a * q
  let v := r - q ^ 2
  have hv : 0 < v := by
    have h := one_sub_hazard_mul_gap_pos a
    dsimp [v, r, q]
    unfold gaussianGap at h
    nlinarith
  let c := ((a ^ 2 + 2) * q - q * r) / v
  let b := r - c * q
  have hp := mul_pos (integral_quadratic_sq_pos a c b) hv
  have hpdf : normalPDF a = q * normalCDF (-a) := by
    dsimp [q, gaussianHazard]
    field_simp [(normalCDF_pos (-a)).ne']
  have hv0 : 1 + a * q - q ^ 2 ≠ 0 := hv.ne'
  have heq :
      (∫ x in Ioi a, (x ^ 2 - c * x - b) ^ 2 * normalPDF x) * v =
        normalCDF (-a) *
          ((1 - a * (q - a)) * (2 - a * (q - a)) - (q - a) ^ 2 * (3 - a * (q - a))) := by
    rw [integral_quadratic_sq_tail, hpdf]
    dsimp only [c, b, v, r]
    field_simp [hv0]
    ring
  rw [heq] at hp
  exact (mul_pos_iff_of_pos_left (normalCDF_pos (-a))).mp hp

theorem excess_second_moment_pos (a : ℝ) : 0 < 1 - a * gaussianGap a := by
  have h := one_sub_hazard_mul_gap_pos a
  have hd := gaussianGap_pos a
  unfold gaussianGap at *
  nlinarith

/-- The comparison whose derivative is the positive tail moment determinant. -/
noncomputable def curvatureComparison (a : ℝ) : ℝ :=
  exponentialTransport a - gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a)

theorem hasDerivAt_curvatureComparison (a : ℝ) :
    HasDerivAt curvatureComparison
      (gaussianHazard a *
        ((1 - a * gaussianGap a) * (2 - a * gaussianGap a) -
          gaussianGap a ^ 2 * (3 - a * gaussianGap a)) / (1 - a * gaussianGap a) ^ 2) a := by
  have hd := ((hasDerivAt_id a).mul (hasDerivAt_gaussianGap a)).const_sub 1
  have hr := ((hasDerivAt_gaussianHazard a).mul (hasDerivAt_gaussianGap a)).div hd
    (excess_second_moment_pos a).ne'
  have h := (hasDerivAt_exponentialTransport a).sub hr
  change HasDerivAt curvatureComparison _ a at h
  apply h.congr_deriv
  dsimp
  field_simp [(excess_second_moment_pos a).ne']
  unfold gaussianGap
  ring

theorem tendsto_curvatureComparison_atBot : Tendsto curvatureComparison atBot (𝓝 0) := by
  have hgap : Tendsto gaussianGap atBot atTop := by
    apply tendsto_atTop_mono (f := fun a : ℝ => -a) _ tendsto_neg_atBot_atTop
    intro a
    have h := gaussianHazard_pos a
    dsimp only [gaussianGap]
    linarith
  have hqdiv := tendsto_gaussianHazard_atBot.div_atTop hgap
  have hR : Tendsto (fun a => gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a))
      atBot (𝓝 0) := by
    apply squeeze_zero _ _ hqdiv
    · intro a
      exact div_nonneg (mul_nonneg (gaussianHazard_pos a).le (gaussianGap_pos a).le)
        (excess_second_moment_pos a).le
    · intro a
      rw [div_le_div_iff₀ (excess_second_moment_pos a) (gaussianGap_pos a)]
      have hv := one_sub_hazard_mul_gap_pos a
      have hq := gaussianHazard_pos a
      have hd : gaussianGap a ^ 2 ≤ 1 - a * gaussianGap a := by
        unfold gaussianGap at *
        nlinarith
      have h := mul_le_mul_of_nonneg_left hd hq.le
      nlinarith
  have hc : Tendsto (fun a => normalCDF (-a)) atBot (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp tendsto_neg_atBot_atTop
  have ht : Tendsto exponentialTransport atBot (𝓝 0) := by
    change Tendsto (fun a => -Real.log (normalCDF (-a))) atBot (𝓝 0)
    simpa only [Real.log_one, neg_zero] using (hc.log one_ne_zero).neg
  change Tendsto (fun a => exponentialTransport a -
    gaussianHazard a * gaussianGap a / (1 - a * gaussianGap a)) atBot (𝓝 0)
  simpa only [sub_zero] using ht.sub hR

/-- The transport ratio is strictly convex: the second scalar positivity assertion
in Lemma 2.2 follows from a Gaussian moment determinant, without numerical estimates. -/
theorem transportCurvature_pos (a : ℝ) : 0 < transportCurvature a := by
  have hm : StrictMono curvatureComparison := by
    apply strictMono_of_hasDerivAt_pos hasDerivAt_curvatureComparison
    intro x
    exact div_pos (mul_pos (gaussianHazard_pos x) (tail_moment_determinant_pos x))
      (sq_pos_of_pos (excess_second_moment_pos x))
  have hn := hm.monotone.le_of_tendsto tendsto_curvatureComparison_atBot (a - 1)
  have hlt := hm (show a - 1 < a by linarith)
  have hcmp : 0 < curvatureComparison a := lt_of_le_of_lt hn hlt
  unfold curvatureComparison at hcmp
  have hnum := (div_lt_iff₀ (excess_second_moment_pos a)).mp (sub_pos.mp hcmp)
  have heq : gaussianHazard a * transportCurvature a =
      exponentialTransport a * (1 - a * gaussianGap a) - gaussianHazard a * gaussianGap a := by
    unfold transportCurvature transportSlope transportRatio
    field_simp [(gaussianHazard_pos a).ne']
    unfold gaussianGap
    ring
  apply (mul_pos_iff_of_pos_left (gaussianHazard_pos a)).mp
  rw [heq]
  linarith

end Submission.Obl.Root.GaussianCurvature
