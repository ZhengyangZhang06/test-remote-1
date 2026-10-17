import Submission.Obl.Entropy__gaussian_covariance_variational.HermiteTests
import Submission.Obl.Entropy__gaussian_covariance_variational.WeakTesting
import Submission.Obl.Entropy__gaussian_covariance_variational.Lifting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_covariance_variational

open Submission.Obl.Entropy__gaussian_chaos_resolvent

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E

/-- Testing the weak divergence with a Hermite polynomial gives its coefficient identity. -/
lemma weak_gaussianCoeff {D A : E → ℝ} {B : Fin m → E → ℝ}
    (hD : MemLp D 2 γ) (hA : MemLp A 2 γ) (hB : ∀ r, MemLp (B r) 2 γ)
    (hw : ∀ z : E → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z →
      HasCompactSupport z → (∫ x, (A x - D x) * z x ∂γ) =
        ∑ r, ∫ x, B r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂γ)
    (a : Fin m → ℕ) :
    gaussianCoeff (hD.toLp D) a = gaussianCoeff (hA.toLp A) a -
      ∑ r, Real.sqrt (a r : ℝ) * gaussianCoeff ((hB r).toLp (B r)) (lowerIndex a r) := by
  have ht := weak_h1_testing (hA.sub hD) hB hw (hermiteEuclidean a)
    (contDiff_hermiteEuclidean a) (memLp_hermiteEuclidean a) (memLp_hermiteEuclidean_deriv a)
  simp only [Pi.sub_apply, sub_mul] at ht
  erw [integral_sub (hA.integrable_mul (memLp_hermiteEuclidean a))
    (hD.integrable_mul (memLp_hermiteEuclidean a))] at ht
  simp only [Pi.mul_apply] at ht
  simp_rw [fderiv_hermiteEuclidean, mul_left_comm (B _ _) (Real.sqrt _), integral_const_mul] at ht
  simp only [gaussianCoeff_toLp]
  linarith

/-- The centered scalar covariance estimate, before matrix weighting. -/
theorem scalar_centered_bound {F : E → ℝ}
    (hF : Differentiable ℝ F) (hF2 : MemLp F 2 γ)
    (hD : ∀ j, MemLp (fun x => fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) 2 γ)
    (hmean : (∫ x, F x ∂γ) = 0)
    (a : Fin m → E → ℝ) (b : Fin m → Fin m → E → ℝ)
    (ha : ∀ j, MemLp (a j) 2 γ) (hb : ∀ r j, MemLp (b r j) 2 γ)
    (hw : ∀ j z, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
      (∫ x, (a j x - fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) * z x ∂γ) =
        ∑ r, ∫ x, b r j x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂γ) :
    (∫ x, (F x)^2 ∂γ) ≤
      (∑ j, ∫ x, (a j x)^2 ∂γ) + ∑ r, ∑ j, ∫ x, (b r j x)^2 ∂γ := by
  let f : GaussianL2 m := hF2.toLp F
  let d : Fin m → GaussianL2 m := fun j => (hD j).toLp _
  have hf0 : gaussianCoeff f 0 = 0 := by
    simpa [f, gaussianCoeff_toLp] using hmean
  have hd (j α) : gaussianCoeff (d j) α =
      Real.sqrt (α j + 1 : ℝ) * gaussianCoeff f (raiseIndex α j) :=
    gaussianCoeff_deriv j hF hF2 (hD j) α
  have hc := sum_resolvent_inner_eq f f d d hf0 hd hd
  rw [real_inner_self_eq_norm_sq, show ‖f‖^2 = ∫ x, (F x)^2 ∂γ from norm_toLp_sq hF2] at hc
  rw [← hc]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    resolvent_dual_bound (d j) ((ha j).toLp (a j)) (fun r => (hb r j).toLp (b r j))
      (weak_gaussianCoeff (hD j) (ha j) (fun r => hb r j) (hw j)))
  simp only [norm_toLp_sq, Finset.sum_add_distrib] at h
  simpa only [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin m))) (f := fun j r => ∫ x, (b r j x)^2 ∂γ)] using h

/-- The sharp Gaussian covariance bound for a weak gradient decomposition. -/
theorem scalar_covariance_bound (m : ℕ) : ScalarCovarianceBound m := by
  intro F hF hF2 hD a b ha hb hw
  let c : ℝ := ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have hG : Differentiable ℝ (fun x => F x - c) := hF.sub_const c
  have hG2 : MemLp (fun x => F x - c) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    hF2.sub (memLp_const c)
  have hd (x : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fun x => F x - c) x = fderiv ℝ F x := fderiv_sub_const _
  have hmean : (∫ x, F x - c ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0 := by
    rw [integral_sub (hF2.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  apply scalar_centered_bound hG hG2 (fun j => by simpa only [hd] using hD j)
    hmean a b ha hb
  intro j z hz hzs
  simpa only [hd] using hw j z hz hzs

end Submission.Obl.Entropy__gaussian_covariance_variational
