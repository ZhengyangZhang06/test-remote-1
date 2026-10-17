import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Polynomial
import Submission.Lib.GaussianTransport.GaussianTails

open Set Filter ProbabilityTheory
open scoped Topology

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

private theorem peval_nonneg (p : List ℚ) (hp : ∀ c ∈ p, 0 ≤ c)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ peval p x := by
  induction p with
  | nil => simp [peval]
  | cons a p ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hp
    exact add_nonneg (by exact_mod_cast hp.1) (mul_nonneg hx (ih hp.2))

private theorem peval_nonpos (p : List ℚ) (hp : ∀ c ∈ p, c ≤ 0)
    {x : ℝ} (hx : 0 ≤ x) : peval p x ≤ 0 := by
  induction p with
  | nil => simp [peval]
  | cons a p ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hp
    exact add_nonpos (by exact_mod_cast hp.1) (mul_nonpos_of_nonneg_of_nonpos hx (ih hp.2))

/-- The residual for a polynomial in the reciprocal coordinate. -/
def millsResidual (p : List ℚ) : List ℚ :=
  padd p (padd (0 :: 0 :: 0 :: pdiff p) [0,-1])

noncomputable def millsError (p : List ℚ) (x : ℝ) : ℝ :=
  normalPDF x * peval p x⁻¹ - normalCDF (-x)

theorem hasDerivAt_millsError (p : List ℚ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (millsError p)
      (-normalPDF x * x * peval (millsResidual p) x⁻¹) x := by
  have hc : HasDerivAt (fun y => normalCDF (-y)) (-normalPDF x) x := by
    convert! (hasDerivAt_normalCDF (-x)).comp x (hasDerivAt_id x).neg using 1
    simp [normalPDF_neg]
  have hh := ((hasDerivAt_normalPDF x).mul
    ((hasDerivAt_peval p x⁻¹).comp x (hasDerivAt_inv hx.ne'))).sub hc
  convert! hh using 1
  simp only [millsResidual, peval_add, peval, Rat.cast_zero, Rat.cast_neg, Rat.cast_one, Function.comp_def]
  field_simp [hx.ne']
  <;> ring

theorem tendsto_millsError (p : List ℚ) : Tendsto (millsError p) atTop (𝓝 0) := by
  have hp : Continuous (peval p) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_peval p x).continuousAt)
  have h := tendsto_normalPDF_atTop.mul ((hp.tendsto 0).comp tendsto_inv_atTop_zero)
  have hc : Tendsto (fun x => normalCDF (-x)) atTop (𝓝 0) :=
    (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
  change Tendsto (fun x => normalPDF x * peval p x⁻¹ - normalCDF (-x)) atTop (𝓝 0)
  convert! h.sub hc using 1 <;> simp

theorem mills_upper (p : List ℚ) (hp : ∀ c ∈ millsResidual p, 0 ≤ c)
    {x : ℝ} (hx : 0 < x) : normalCDF (-x) / normalPDF x ≤ peval p x⁻¹ := by
  have hm : AntitoneOn (millsError p) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun y hy => (hasDerivAt_millsError p hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_millsError p (by simpa using hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by simpa using hy
      rw [(hasDerivAt_millsError p hy').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (normalPDF_pos y).le) hy'.le)
        (peval_nonneg _ hp (inv_nonneg.mpr hy'.le))
  have hh : 0 ≤ millsError p x := le_of_tendsto (tendsto_millsError p)
    (eventually_atTop.2 ⟨x, fun y hy => hm hx (lt_of_lt_of_le hx hy) hy⟩)
  rw [div_le_iff₀ (normalPDF_pos x)]
  dsimp [millsError] at hh
  nlinarith

theorem mills_lower (p : List ℚ) (hp : ∀ c ∈ millsResidual p, c ≤ 0)
    {x : ℝ} (hx : 0 < x) : peval p x⁻¹ ≤ normalCDF (-x) / normalPDF x := by
  have hm : MonotoneOn (millsError p) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun y hy => (hasDerivAt_millsError p hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_millsError p (by simpa using hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by simpa using hy
      rw [(hasDerivAt_millsError p hy').deriv]
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (normalPDF_pos y).le) hy'.le)
        (peval_nonpos _ hp (inv_nonneg.mpr hy'.le))
  have hh : millsError p x ≤ 0 := ge_of_tendsto (tendsto_millsError p)
    (eventually_atTop.2 ⟨x, fun y hy => hm hx (lt_of_lt_of_le hx hy) hy⟩)
  rw [le_div_iff₀ (normalPDF_pos x)]
  dsimp [millsError] at hh
  nlinarith

def millsCoeff : Nat → ℤ
  | 0 => 1
  | n+1 => -(2*(n : ℤ)+1) * millsCoeff n

def millsPoly (n : Nat) : List ℚ :=
  ((List.range (n+1)).map (fun i => [0, (millsCoeff i : ℚ)])).flatten

set_option maxRecDepth 10000 in
 theorem mills_11_lower {x : ℝ} (hx : 0 < x) :
    peval (millsPoly 11) x⁻¹ ≤ normalCDF (-x) / normalPDF x :=
  mills_lower _ (by decide +kernel) hx

set_option maxRecDepth 10000 in
 theorem mills_12_upper {x : ℝ} (hx : 0 < x) :
    normalCDF (-x) / normalPDF x ≤ peval (millsPoly 12) x⁻¹ :=
  mills_upper _ (by decide +kernel) hx

set_option maxRecDepth 10000 in
 theorem mills_13_lower {x : ℝ} (hx : 0 < x) :
    peval (millsPoly 13) x⁻¹ ≤ normalCDF (-x) / normalPDF x :=
  mills_lower _ (by decide +kernel) hx

set_option maxRecDepth 10000 in
 theorem mills_14_upper {x : ℝ} (hx : 0 < x) :
    normalCDF (-x) / normalPDF x ≤ peval (millsPoly 14) x⁻¹ :=
  mills_upper _ (by decide +kernel) hx

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
