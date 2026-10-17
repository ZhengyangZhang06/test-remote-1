import Submission.Obl.Entropy__gaussian_covariance_variational.Indices
import Submission.Obl.Entropy__gaussian_chaos_resolvent.ScalarInverse

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_covariance_variational

open Submission.Obl.Entropy__gaussian_chaos_resolvent

lemma contDiff_hermiteFunction (n : ℕ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (hermiteFunction n) := by
  change ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
    (fun x : ℝ => (hermitePoly n).eval x / Real.sqrt (n.factorial : ℝ))
  apply ContDiff.div_const
  convert! (hermitePoly n).contDiff_aeval (𝕜 := ℝ) ((⊤ : ENat) : WithTop ENat) using 1

lemma hasDerivAt_hermiteFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFunction n) (Real.sqrt (n : ℝ) * hermiteFunction (n - 1) x) x := by
  cases n with
  | zero =>
    have he : hermiteFunction 0 = fun _ => (1 : ℝ) := funext hermiteFunction_zero
    simpa [he] using hasDerivAt_const x (1 : ℝ)
  | succ n =>
    have h : HasDerivAt (hermiteFunction (n+1))
        ((hermitePoly (n+1)).derivative.eval x / Real.sqrt ((n+1).factorial : ℝ)) x :=
      ((hermitePoly (n+1)).hasDerivAt x).div_const _
    have he : Real.sqrt ((n+1 : ℕ) : ℝ) * hermiteFunction n x =
        (hermitePoly (n+1)).derivative.eval x / Real.sqrt ((n+1).factorial : ℝ) := by
      simp only [derivative_hermitePoly_succ, Polynomial.eval_mul, Polynomial.eval_C,
        hermiteFunction, sqrt_factorial_succ, Nat.cast_add, Nat.cast_one]
      have h1 : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
      have h2 : Real.sqrt (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, he] using h

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E

lemma contDiff_hermiteEuclidean (a : Fin m → ℕ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (hermiteEuclidean a) := by
  unfold hermiteEuclidean hermiteTensor
  apply contDiff_prod
  intro i _
  exact (contDiff_hermiteFunction (a i)).comp (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff

lemma hasFDerivAt_hermiteEuclidean (a : Fin m → ℕ) (x : E) :
    HasFDerivAt (hermiteEuclidean a)
      (∑ r : Fin m, (∏ s ∈ Finset.univ.erase r, hermiteFunction (a s) (x s)) •
        ((Real.sqrt (a r : ℝ) * hermiteFunction (a r - 1) (x r)) •
          (EuclideanSpace.proj r : E →L[ℝ] ℝ))) x := by
  unfold hermiteEuclidean hermiteTensor
  apply HasFDerivAt.finsetProd (g := fun r (y : E) => hermiteFunction (a r) (y r))
  intro r _
  exact (hasDerivAt_hermiteFunction (a r) (x r)).comp_hasFDerivAt x
    (EuclideanSpace.proj r : E →L[ℝ] ℝ).hasFDerivAt

lemma fderiv_hermiteEuclidean (a : Fin m → ℕ) (r : Fin m) (x : E) :
    fderiv ℝ (hermiteEuclidean a) x (PiLp.single 2 r (1 : ℝ)) =
      Real.sqrt (a r : ℝ) * hermiteEuclidean (lowerIndex a r) x := by
  classical
  rw [(hasFDerivAt_hermiteEuclidean a x).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj, PiLp.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : hermiteEuclidean (lowerIndex a r) x =
      hermiteFunction (a r - 1) (x r) * ∏ s ∈ Finset.univ.erase r, hermiteFunction (a s) (x s) := by
    unfold hermiteEuclidean hermiteTensor
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    simp only [lowerIndex, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  rw [he]
  ring

lemma memLp_hermiteEuclidean_deriv (a : Fin m → ℕ) (r : Fin m) :
    MemLp (fun x : E => fderiv ℝ (hermiteEuclidean a) x (PiLp.single 2 r (1 : ℝ))) 2 γ := by
  simp_rw [fderiv_hermiteEuclidean]
  exact (memLp_hermiteEuclidean (lowerIndex a r)).const_mul _

end Submission.Obl.Entropy__gaussian_covariance_variational
