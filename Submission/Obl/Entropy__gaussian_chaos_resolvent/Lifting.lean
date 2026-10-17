/- Adapted from session x0073, commit 42bad91, on this obligation. -/
import Submission.Obl.Entropy__gaussian_chaos_resolvent.Assembly
import Submission.Obl.Entropy__gaussian_chaos_resolvent.ScalarInverse

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

/-- The scalar inverse may be chosen once per unordered entry pair, giving
pointwise Hermitian representatives without changing any scalar estimates. -/
theorem matrix_resolvent {m : ℕ} (hm : 1 ≤ m) (Y : E m → M m)
    (hY : ∀ x, (Y x).IsHermitian)
    (hsm : ∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => Y x i j))
    (hL : MatrixL2 Y) (hD : ∀ r, MatrixL2 (matrixDeriv Y r))
    (hmean : ∀ i j, (∫ x, Y x i j ∂gaussian m) = 0)
    (hfirst : ∀ r i j, (∫ x, x r * Y x i j ∂gaussian m) = 0) :
    ∃ g : Fin m → E m → M m,
      (∀ r x, (g r x).IsHermitian) ∧ (∀ r, MatrixL2 (g r)) ∧
      (∀ i j (z : E m → ℝ), ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z →
        HasCompactSupport z →
        (∫ x, Y x i j*z x ∂gaussian m) =
          ∑ r, ∫ x, g r x i j*coordDeriv z r x ∂gaussian m) ∧
      energy Y - (∑ r, energy (matrixDeriv Y r)) +
        (∫ x, ∑ r, ∑ i, ∑ j, quadratic (matrixDeriv Y r x i j)
          (g r x i j-matrixDeriv Y r x i j/2) ∂gaussian m) ≤ -(7/50)*energy Y := by
  classical
  let f : Fin m → Fin m → E m → ℝ := fun i j x => Y x i j
  have hex : ∀ i j, ∃ v : Fin m → E m → ℝ,
      (∀ r, MemLp (v r) 2 (gaussian m)) ∧
      (∀ z : E m → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z →
        HasCompactSupport z → (∫ x, f i j x*z x ∂gaussian m) =
          ∑ r, ∫ x, v r x*coordDeriv z r x ∂gaussian m) ∧
      (∑ r, ∫ x, v r x*coordDeriv (f i j) r x ∂gaussian m) =
        (∫ x, (f i j x)^2 ∂gaussian m) ∧
      (∑ r, ∫ x, (v r x)^2 ∂gaussian m) ≤ (∫ x, (f i j x)^2 ∂gaussian m)/2 := by
    intro i j
    exact second_chaos_inverse m hm (f i j)
      (hsm i j) (hL i j) (fun r => hD r i j) (hmean i j) (fun r => hfirst r i j)
  choose v hvL hvDiv hvCross hvNorm using hex
  have hsymf (i j : Fin m) : f j i = f i j := by
    funext x
    exact (hY x).apply i j
  have hordered (i j : Fin m) : f (min i j) (max i j) = f i j := by
    by_cases h : i ≤ j
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
      exact hsymf i j
  let g : Fin m → E m → M m := fun r x => Matrix.of
    (fun i j => v (min i j) (max i j) r x)
  have hgL (r : Fin m) : MatrixL2 (g r) := fun i j => hvL (min i j) (max i j) r
  refine ⟨g, ?_, hgL, ?_, ?_⟩
  · intro r x
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [g, Matrix.of_apply, star_trivial, min_comm j i, max_comm j i]
  · intro i j z hz hzc
    have h := hvDiv (min i j) (max i j) z hz hzc
    rw [hordered i j] at h
    exact h
  · have hc (i j : Fin m) :
        (∑ r, ∫ x, g r x i j * matrixDeriv Y r x i j ∂gaussian m) =
          (∫ x, (Y x i j)^2 ∂gaussian m) := by
      have h := hvCross (min i j) (max i j)
      rw [hordered i j] at h
      exact h
    have hn (i j : Fin m) :
        (∑ r, ∫ x, (g r x i j)^2 ∂gaussian m) ≤
          (∫ x, (Y x i j)^2 ∂gaussian m)/2 := by
      have h := hvNorm (min i j) (max i j)
      rw [hordered i j] at h
      exact h
    have hgap (i j : Fin m) :
        2*(∫ x, (Y x i j)^2 ∂gaussian m) ≤
          ∑ r, ∫ x, (matrixDeriv Y r x i j)^2 ∂gaussian m :=
      second_chaos_gap m hm (f i j)
        (hsm i j) (hL i j) (fun r => hD r i j) (hmean i j) (fun r => hfirst r i j)
    have hclose (i j : Fin m) := scalar_closing
      (fun r => hD r i j) (fun r => hgL r i j) (hgap i j) (hc i j) (hn i j)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hclose i j))
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have hderiv : (∑ r, energy (matrixDeriv Y r)) =
        ∑ i, ∑ j, ∑ r, ∫ x, (matrixDeriv Y r x i j)^2 ∂gaussian m := by
      simp_rw [energy_eq_sum (hD _)]
      rw [Finset.sum_comm]
      congr 1
      funext i
      exact Finset.sum_comm
    rw [energy_eq_sum hL, hderiv, quadratic_energy_eq_sum hD hgL]
    exact hsum

end Submission.Obl.Entropy__gaussian_chaos_resolvent
