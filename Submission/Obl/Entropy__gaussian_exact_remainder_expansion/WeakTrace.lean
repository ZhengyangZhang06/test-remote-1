import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.GaussianFirst
import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.CutoffTests

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

lemma defect₂_zero_of_test {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (hr : FCRegular A)
    {g : Fin m → E m → Mat m} (hgs : ∀ r x, (g r x).IsHermitian)
    (hgl : ∀ r, MatrixLp (γ m) 2 (g r))
    (htest : ∀ i j a b, (∫ x, Y A x i j*c A k x a b ∂γ m) =
      ∑ r, ∫ x, g r x i j*K A r x a b ∂γ m) :
    (∫ x, defect₂ A g x ∂γ m) = 0 := by
  have hY := hr.Y_lp hA
  have hC := hr.lp smooth_k 2
  let R (x : E m) : Mat m := Y A x*c A k x-∑ r, g r x*K A r x
  have hYC : MatrixLp (γ m) 1 (fun x => Y A x*c A k x) := hY.mul hC
  have hgK (r) : MatrixLp (γ m) 1 (fun x => g r x*K A r x) := (hgl r).mul (hr.K_lp r)
  have hsum : MatrixLp (γ m) 1 (fun x => ∑ r, g r x*K A r x) := MatrixLp.sum hgK
  have hR : MatrixLp (γ m) 1 R := hYC.sub hsum
  have hz (i j : Fin m) : (∫ x, R x i j ∂γ m) = 0 := by
    change (∫ x, (Y A x*c A k x) i j-(∑ r, g r x*K A r x) i j ∂γ m) = 0
    erw [integral_sub (memLp_one_iff_integrable.mp (hYC i j))
      (memLp_one_iff_integrable.mp (hsum i j)), sub_eq_zero]
    calc
      _ = ∑ a, ∫ x, Y A x i a*c A k x a j ∂γ m := by
        simp only [Matrix.mul_apply]
        exact integral_finsetSum _ (fun a _ => (hY i a).integrable_mul (hC a j))
      _ = ∑ a, ∑ r, ∫ x, g r x i a*K A r x a j ∂γ m := by
        apply Finset.sum_congr rfl
        intro a _
        exact htest i a a j
      _ = _ := by
        simp only [Matrix.sum_apply, Matrix.mul_apply]
        symm
        calc
          _ = ∑ r, ∫ x, ∑ a, g r x i a*K A r x a j ∂γ m :=
            integral_finsetSum _ (fun r _ => integrable_finsetSum _
              (fun a _ => (hgl r i a).integrable_mul (hr.K_lp r a j)))
          _ = ∑ r, ∑ a, ∫ x, g r x i a*K A r x a j ∂γ m := by
            apply Finset.sum_congr rfl
            intro r _
            exact integral_finsetSum _ (fun a _ => (hgl r i a).integrable_mul (hr.K_lp r a j))
          _ = _ := Finset.sum_comm
  have hT := (resolvent_relations hA).2.1
  have he (x : E m) : defect₂ A g x = (T A*R x).trace := by
    simp only [defect₂, R, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sum,
      Matrix.trace_sum, ← Matrix.mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    have hk : (K A r x).transpose = K A r x := by
      have hh : (K A r x).IsHermitian := d_hermitian (fun y => cfc_predicate k (A y)) r x
      simpa using hh.eq
    have hg : (g r x).transpose = g r x := by simpa using (hgs r x).eq
    simpa only [hk,hg] using Submission.Lib.MatrixEntropy.trace_cross_transpose hT (K A r x) (g r x)
  rw [funext he]
  exact integral_trace_left_zero hR hz (T A)

lemma defect₂_zero {m : ℕ} {A : E m → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (hr : FCRegular A)
    {g : Fin m → E m → Mat m} (hgs : ∀ r x, (g r x).IsHermitian)
    (hgl : ∀ r, MatrixLp (γ m) 2 (g r)) (hdiv : Div (Y A) g) :
    (∫ x, defect₂ A g x ∂γ m) = 0 := by
  apply defect₂_zero_of_test hA hr hgs hgl
  intro i j a b
  obtain ⟨hs,⟨C,_,hC⟩,hd⟩ := hr k smooth_k
  exact weak_test_bounded_c1 ((hr.Y_lp hA i j).integrable (by norm_num))
    (fun r => hgl r i j) (hdiv i j) (hs a b)
    (fun x => by simpa only [Real.norm_eq_abs] using hC x a b) (fun r => hd r a b)

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
