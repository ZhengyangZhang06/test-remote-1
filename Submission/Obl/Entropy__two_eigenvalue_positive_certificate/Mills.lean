import Submission.Lib.GaussianTransport.GaussianTails

open Filter Set
open scoped Topology
open Submission.Lib.GaussianTransport

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

/-- A function increasing towards zero on the positive half-line is nonpositive. -/
theorem nonpos_of_deriv_nonneg_of_tendsto_zero {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 < x → 0 ≤ f' x)
    (ht : Tendsto f atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) : f a ≤ 0 := by
  have hm : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hf x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hpos x (interior_subset hx)
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨a, fun x hx => hm ha (ha.trans_le hx) hx⟩)

/-- The first five terms of the alternating Mills expansion. -/
noncomputable def millsUpper (a : ℝ) : ℝ :=
  a⁻¹ - (a⁻¹)^3 + 3*(a⁻¹)^5 - 15*(a⁻¹)^7 + 105*(a⁻¹)^9

/-- One further term gives the lower endpoint. -/
noncomputable def millsLower (a : ℝ) : ℝ := millsUpper a - 945*(a⁻¹)^11

private theorem hasDerivAt_millsUpper {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt millsUpper
      (-(a⁻¹)^2 + 3*(a⁻¹)^4 - 15*(a⁻¹)^6 + 105*(a⁻¹)^8 - 945*(a⁻¹)^10) a := by
  have h := hasDerivAt_inv ha
  convert! (((h.sub ((h.pow 3))).add ((h.pow 5).const_mul 3)).sub
    ((h.pow 7).const_mul 15)).add ((h.pow 9).const_mul 105) using 1
  simp only [millsUpper, inv_pow]
  ring

private theorem hasDerivAt_millsLower {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt millsLower
      (-(a⁻¹)^2 + 3*(a⁻¹)^4 - 15*(a⁻¹)^6 + 105*(a⁻¹)^8 - 945*(a⁻¹)^10 +
        10395*(a⁻¹)^12) a := by
  convert! (hasDerivAt_millsUpper ha).sub (((hasDerivAt_inv ha).pow 11).const_mul 945)
    using 1
  simp only [millsLower, inv_pow]
  ring

private theorem tendsto_millsUpper : Tendsto millsUpper atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
  convert! (((h.sub (h.pow 3)).add ((h.pow 5).const_mul 3)).sub
    ((h.pow 7).const_mul 15)).add ((h.pow 9).const_mul 105) using 1 <;> norm_num

private theorem tendsto_millsLower : Tendsto millsLower atTop (𝓝 0) := by
  convert! tendsto_millsUpper.sub
    (((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 11).const_mul 945) using 1 <;> norm_num

/-- Alternating Gaussian-tail bounds, valid at every positive argument. -/
theorem mills_bounds {a : ℝ} (ha : 0 < a) :
    normalPDF a * millsLower a ≤ normalCDF (-a) ∧
    normalCDF (-a) ≤ normalPDF a * millsUpper a := by
  have hc (x : ℝ) : HasDerivAt (fun y => normalCDF (-y)) (-normalPDF x) x := by
    convert! (hasDerivAt_normalCDF (-x)).comp x (hasDerivAt_id x).neg using 1
    simp [normalPDF_neg]
  have ht : Tendsto (fun x => normalCDF (-x)) atTop (𝓝 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot _).comp tendsto_neg_atTop_atBot
  constructor
  · have hd (x : ℝ) (hx : 0 < x) : HasDerivAt
        (fun y => normalPDF y * millsLower y - normalCDF (-y))
        (10395 * normalPDF x * (x⁻¹)^12) x := by
      convert! ((hasDerivAt_normalPDF x).mul (hasDerivAt_millsLower hx.ne')).sub (hc x)
        using 1
      dsimp [millsLower, millsUpper]
      field_simp
      <;> ring
    have hn := nonpos_of_deriv_nonneg_of_tendsto_zero hd
      (fun x hx => by have := normalPDF_pos x; positivity)
      (by simpa using (tendsto_normalPDF_atTop.mul tendsto_millsLower).sub ht) ha
    linarith
  · have hd (x : ℝ) (hx : 0 < x) : HasDerivAt
        (fun y => normalCDF (-y) - normalPDF y * millsUpper y)
        (945 * normalPDF x * (x⁻¹)^10) x := by
      convert! (hc x).sub ((hasDerivAt_normalPDF x).mul (hasDerivAt_millsUpper hx.ne'))
        using 1
      dsimp [millsUpper]
      field_simp
      <;> ring
    have hn := nonpos_of_deriv_nonneg_of_tendsto_zero hd
      (fun x hx => by have := normalPDF_pos x; positivity)
      (by simpa using ht.sub (tendsto_normalPDF_atTop.mul tendsto_millsUpper)) ha
    linarith

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
