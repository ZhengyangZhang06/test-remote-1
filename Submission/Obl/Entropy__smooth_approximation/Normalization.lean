import Mathlib
import Submission.Lib.EntropyTools.LimitPassage

open MeasureTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_approximation

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

noncomputable def density {m : ℕ} (V : E m → ℝ) (x : E m) : ℝ :=
  Real.exp (-V x)

noncomputable def mean {m : ℕ} (f : E m → ℝ) : E m := ∫ x, f x • x

noncomputable def covariance {m : ℕ} (f : E m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ x, f x * (x i - mean f i) * (x j - mean f j)

noncomputable def entropy {m : ℕ} (f : E m → ℝ) : ℝ :=
  -∫ x, f x * Real.log (f x)

/-- The differential part of the regularity condition in Lemma 5.2. -/
def SmoothPotential {m : ℕ} (V : E m → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧
  ∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : E m,
    cmin * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧
    (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖ ^ 2

def Regular {m : ℕ} (V : E m → ℝ) : Prop :=
  SmoothPotential V ∧ Integrable (density V) volume ∧
  (∫ x, density V x) = 1 ∧
  Integrable (fun x => density V x * ‖x‖ ^ 2) volume ∧
  Integrable (fun x => density V x * Real.log (density V x)) volume

lemma SmoothPotential.add_const {m : ℕ} {V : E m → ℝ}
    (hV : SmoothPotential V) (c : ℝ) : SmoothPotential (fun x => V x + c) := by
  refine ⟨hV.1.add contDiff_const, ?_⟩
  have hd : fderiv ℝ (fun x => V x + c) = fderiv ℝ V :=
    funext fun x => fderiv_add_const c
  rw [hd]
  exact hV.2

lemma density_add_const {m : ℕ} (V : E m → ℝ) (c : ℝ) (x : E m) :
    density (fun y => V y + c) x = Real.exp (-c) * density V x := by
  simp only [density, neg_add, Real.exp_add]
  ring

lemma density_normalize {m : ℕ} (V : E m → ℝ) {Z : ℝ} (hZ : 0 < Z) (x : E m) :
    density (fun y => V y + Real.log Z) x = Z⁻¹ * density V x := by
  rw [density_add_const, Real.exp_neg, Real.exp_log hZ]

lemma mass_pos {m : ℕ} {V : E m → ℝ} (hi : Integrable (density V) volume) :
    0 < ∫ x, density V x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi).2
  have hs : Function.support (density V) = Set.univ := by
    ext x
    simp [density, Real.exp_ne_zero]
  change 0 < volume (Function.support (density V))
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

lemma normalized_entropy_integrand {m : ℕ} (V : E m → ℝ) {Z : ℝ}
    (hZ : 0 < Z) (x : E m) :
    density (fun y => V y + Real.log Z) x *
        Real.log (density (fun y => V y + Real.log Z) x) =
      Z⁻¹ * (density V x * Real.log (density V x)) -
        (Z⁻¹ * Real.log Z) * density V x := by
  rw [density_normalize V hZ]
  have hv : density V x ≠ 0 := Real.exp_ne_zero _
  rw [Real.log_mul (inv_ne_zero hZ.ne') hv, Real.log_inv]
  ring

lemma normalized_regular {m : ℕ} {V : E m → ℝ}
    (hs : SmoothPotential V) (hi : Integrable (density V) volume)
    (hi2 : Integrable (fun x => density V x * ‖x‖ ^ 2) volume)
    (hie : Integrable (fun x => density V x * Real.log (density V x)) volume) :
    Regular (fun x => V x + Real.log (∫ y, density V y)) := by
  let Z := ∫ x, density V x
  have hZ : 0 < Z := mass_pos hi
  change Regular (fun x => V x + Real.log Z)
  refine ⟨hs.add_const _, ?_, ?_, ?_, ?_⟩
  · change Integrable (fun x => density (fun y => V y + Real.log Z) x) volume
    simpa only [density_normalize V hZ] using hi.const_mul Z⁻¹
  · simp only [density_normalize V hZ, integral_const_mul]
    exact inv_mul_cancel₀ hZ.ne'
  · simpa only [density_normalize V hZ, mul_assoc] using hi2.const_mul Z⁻¹
  · simp only [normalized_entropy_integrand V hZ]
    exact (hie.const_mul Z⁻¹).sub (hi.const_mul (Z⁻¹ * Real.log Z))

lemma entropy_normalize {m : ℕ} {V : E m → ℝ}
    (hi : Integrable (density V) volume)
    (hie : Integrable (fun x => density V x * Real.log (density V x)) volume) :
    entropy (density (fun x => V x + Real.log (∫ y, density V y))) =
      (∫ y, density V y)⁻¹ * entropy (density V) + Real.log (∫ y, density V y) := by
  let Z := ∫ x, density V x
  have hZ : 0 < Z := mass_pos hi
  change entropy (density (fun x => V x + Real.log Z)) =
    Z⁻¹ * entropy (density V) + Real.log Z
  simp only [entropy, normalized_entropy_integrand V hZ]
  rw [integral_sub (hie.const_mul _) (hi.const_mul _), integral_const_mul,
    integral_const_mul]
  change -(Z⁻¹ * _ - (Z⁻¹ * Real.log Z) * Z) = Z⁻¹ * (-_) + Real.log Z
  field_simp
  ring

lemma integral_normalize_mul {m : ℕ} (V : E m → ℝ)
    (hi : Integrable (density V) volume) (w : E m → ℝ) :
    (∫ x, density (fun y => V y + Real.log (∫ z, density V z)) x * w x) =
      (∫ z, density V z)⁻¹ * ∫ x, density V x * w x := by
  simp only [density_normalize V (mass_pos hi), mul_assoc, integral_const_mul]

lemma mean_normalize {m : ℕ} (V : E m → ℝ)
    (hi : Integrable (density V) volume) :
    mean (density (fun y => V y + Real.log (∫ z, density V z))) =
      (∫ z, density V z)⁻¹ • mean (density V) := by
  simp only [mean, density_normalize V (mass_pos hi), mul_smul, integral_smul]

end Submission.Obl.Entropy__smooth_approximation
