/-
Adapted from: here:o021
Original proofs by session x0046.
-/

import Submission.Lib.SpectralAbsorption.Integration
import Submission.Lib.SpectralAbsorption.DualSpectrum
import Submission.Lib.EntropyTools.Remainder

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

namespace Submission.Lib.SpectralAbsorption

set_option backward.isDefEq.respectTransparency false

open Submission.Lib.EntropyTools

noncomputable def dualSVal (z : ℝ) : ℝ := (37/40 + (3/40)*z)⁻¹
noncomputable def dualWVal (z : ℝ) : ℝ :=
  -(dualSVal z - 1) * (z - 1) * (3/20 + (1813/4000)*dualSVal z)

lemma dualSVal_pos {z : ℝ} (hz : 0 ≤ z) : 0 < dualSVal z := by
  unfold dualSVal
  positivity

lemma dualSVal_eq (z : ℝ) : dualSVal z = 40 / (37 + 3*z) := by
  unfold dualSVal
  rw [show (37/40 : ℝ) + (3/40)*z = (37+3*z)/40 by ring, inv_div]

lemma dualWVal_eq {z : ℝ} (hz : 0 ≤ z) :
    dualWVal z = (3 * (z - 1)^2 / (37 + 3*z)) *
      (3/20 + (49/100)*(37/(37+3*z))) := by
  have hd : 37 + 3*z ≠ 0 := ne_of_gt (by positivity)
  rw [dualWVal, dualSVal_eq]
  field_simp
  <;> ring

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma basisDiag_second_moment {A Y : Ω → Matrix n n ℝ} {B : Matrix n n ℝ}
    (hB : B.IsHermitian)
    (hA2 : ∀ i j, Integrable (fun x => (A x * A x) i j) μ)
    (hY2 : ∀ i j, Integrable (fun x => (Y x * Y x) i j) μ)
    (hsecond : ∀ i j, (∫ x, (A x * A x) i j ∂μ) =
      B i j + ∫ x, (Y x * Y x) i j ∂μ) (i : n) :
    (∫ x, basisDiag hB.eigenvectorUnitary (A x * A x) i ∂μ) =
      hB.eigenvalues i + ∫ x, basisDiag hB.eigenvectorUnitary (Y x * Y x) i ∂μ := by
  rw [integral_basisDiag _ hA2, integral_basisDiag _ hY2]
  have hm : (Matrix.of fun j k => ∫ x, (A x * A x) j k ∂μ) =
      B + Matrix.of (fun j k => ∫ x, (Y x * Y x) j k ∂μ) := by
    ext j k
    exact hsecond j k
  change basisDiag hB.eigenvectorUnitary
    (Matrix.of fun j k => ∫ x, (A x * A x) j k ∂μ) i =
      hB.eigenvalues i + basisDiag hB.eigenvectorUnitary
        (Matrix.of fun j k => ∫ x, (Y x * Y x) j k ∂μ) i
  rw [hm, basisDiag_add, basisDiag_self]

/-- The whole matrix portion of Proposition 3.5, with the one-dimensional
absorption estimate supplied as an explicit hypothesis. -/
theorem absorption_from_scalar [IsProbabilityMeasure μ]
    {A Y : Ω → Matrix n n ℝ} {B : Matrix n n ℝ}
    (hA : ∀ x, (A x).IsHermitian) (hY : ∀ x, (Y x).IsHermitian) (hB : B.PosSemidef)
    (hAint : ∀ i j, Integrable (fun x => A x i j) μ)
    (hA2 : ∀ i j, Integrable (fun x => (A x * A x) i j) μ)
    (hY2 : ∀ i j, Integrable (fun x => (Y x * Y x) i j) μ)
    (hmean : ∀ i j, (∫ x, A x i j ∂μ) = 0)
    (hsecond : ∀ i j, (∫ x, (A x * A x) i j ∂μ) =
      B i j + ∫ x, (Y x * Y x) i j ∂μ)
    {p cost u v d : ℝ → ℝ}
    (hpint : ∀ i j, Integrable (fun x => cfc p (A x) i j) μ)
    (hp : ∀ z, 0 ≤ z → ∀ a, u z + v z * a - d z * a^2 ≤ p a)
    (hcost : ∀ a, cost a ≤ 111/1000)
    (hscalar : ∀ z, 0 ≤ z → ∀ r, 0 ≤ r → ∀ e,
      u z - d z * (z + r) ≤ e →
      dualSVal z - 1 - Real.log (dualSVal z) - dualWVal z * e ≤
        (27/1000)*r - rigidityWeight z/1000) :
    let S := ((37/40 : ℝ) • (1 : Matrix n n ℝ) + (3/40 : ℝ) • B)⁻¹
    (S - 1).trace - Real.log S.det -
      (∫ x, ((-(S - 1) * (B - 1)) *
        ((3/20 : ℝ) • 1 + (1813/4000 : ℝ) • S) * cfc p (A x)).trace ∂μ) +
      (∫ x, (Y x * Y x * cfc cost (A x)).trace ∂μ) ≤
      (69/500)*(∫ x, ∑ i, ∑ j, (Y x i j)^2 ∂μ) -
        (∑ i, rigidityWeight (hB.isHermitian.eigenvalues i))/1000 := by
  dsimp only
  let U := hB.isHermitian.eigenvectorUnitary
  let ell := hB.isHermitian.eigenvalues
  let r : n → ℝ := fun i => ∫ x, basisDiag U (Y x * Y x) i ∂μ
  let e : n → ℝ := fun i => ∫ x, basisDiag U (cfc p (A x)) i ∂μ
  have hr i : 0 ≤ r i := integral_nonneg fun x =>
    basisDiag_nonneg U (square_posSemidef (hY x)) i
  have hentry i : dualSVal (ell i) - 1 - Real.log (dualSVal (ell i)) -
      dualWVal (ell i) * e i ≤ (27/1000)*r i - rigidityWeight (ell i)/1000 := by
    apply hscalar (ell i) (hB.eigenvalues_nonneg i) (r i) (hr i) (e i)
    have hm := integral_basisDiag_minorant U hA (hp (ell i) (hB.eigenvalues_nonneg i))
      hAint hA2 hpint hmean i
    rw [basisDiag_second_moment hB.isHermitian hA2 hY2 hsecond i] at hm
    exact hm
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset n)) => hentry i)
  have hrSum : (∑ i, r i) = ∫ x, ∑ i, ∑ j, (Y x i j)^2 ∂μ := by
    rw [show (∑ i, r i) = ∫ x, (Y x * Y x).trace ∂μ from integral_sum_basisDiag U hY2]
    simp_rw [trace_square (hY _)]
  have hs : ((37/40 : ℝ) • (1 : Matrix n n ℝ) + (3/40 : ℝ) • B)⁻¹ =
      cfc dualSVal B :=
    inverse_affine_eq_cfc hB.isHermitian (37/40) (3/40)
      (fun i => ne_of_gt (by have := hB.eigenvalues_nonneg i; positivity))
  have hlog : (((37/40 : ℝ) • (1 : Matrix n n ℝ) + (3/40 : ℝ) • B)⁻¹ - 1).trace -
      Real.log (((37/40 : ℝ) • (1 : Matrix n n ℝ) + (3/40 : ℝ) • B)⁻¹).det =
      ∑ i, (dualSVal (ell i) - 1 - Real.log (dualSVal (ell i))) := by
    rw [hs, logarithmic_cost_eq_sum hB.isHermitian dualSVal
      (fun i => (dualSVal_pos (hB.eigenvalues_nonneg i)).ne')]
  have hw := dual_weight_eq_cfc hB
  change (-( _ - 1) * (B - 1)) * _ = cfc dualWVal B at hw
  rw [hw, hlog, integral_trace_cfc_mul hB.isHermitian dualWVal hpint]
  have hcostInt := integral_trace_square_cfc_le hA hY hY2 (by norm_num : (0 : ℝ) ≤ 111/1000) hcost
  simp_rw [trace_square (hY _)] at hcostInt
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  rw [hrSum] at hsum
  change (∑ i, (dualSVal (ell i) - 1 - Real.log (dualSVal (ell i)))) -
    (∑ i, dualWVal (ell i) * e i) + _ ≤ _
  simp only [Finset.sum_sub_distrib]
  change _ ≤ (69/500)*(∫ x, ∑ i, ∑ j, (Y x i j)^2 ∂μ) - (∑ i, rigidityWeight (ell i))/1000
  linarith only [hsum, hcostInt]

end Submission.Lib.SpectralAbsorption
