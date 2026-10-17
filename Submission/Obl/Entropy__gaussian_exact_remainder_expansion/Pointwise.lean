import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Fields
import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Algebra
import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.ScalarCFC
import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Integrate

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

variable {m : ℕ}

noncomputable def defect₁ (A : E m → Mat m) (x : E m) : ℝ :=
  (T A*((A x-Y A x)*c A f x-∑ r, X A r*d (c A f) r x)).trace
noncomputable def defect₂ (A : E m → Mat m) (g : Fin m → E m → Mat m) (x : E m) : ℝ :=
  (T A*Y A x*c A k x).trace-(T A*(∑ r, K A r x*g r x)).trace

lemma expansion_with_defects (A : E m → Mat m) (hA : ∀ x, (A x).IsHermitian)
    (g : Fin m → E m → Mat m) (hg : ∀ r x, (g r x).IsHermitian) (x : E m) :
    (T A*E2 A x).trace+((u A x).transpose*S A*u A x).trace+
      (∑ r, ((v A g r x).transpose*S A*v A g r x).trace) =
    (T A).trace+(Core A g x+Comm A g x)+defect₁ A x+(3/2:ℝ)*defect₂ A g x := by
  obtain ⟨hS,hT,hSM,hMSM⟩ := resolvent_relations hA
  obtain ⟨he,hp,hh⟩ := cfc_scalar_identities (A x) (hA x)
  have hk (r) : (K A r x).IsHermitian := d_hermitian (fun y => cfc_predicate k (A y)) r x
  have ht := pointwise_expansion (A x) (Y A x) (c A t x) (c A k x) (c A b x)
    (c A l x) (c A f x) (c A (deriv f) x) (c A p x) (c A h x)
    (B A) (S A) (T A) (H A) (F A x)
    (fun r => K A r x) (X A) (fun r => D A r x) (fun r => L A r x)
    (fun r => d (c A f) r x) (fun r => M A g r x) (fun r => g r x)
    (fun r => v A g r x) (fun r => w A g r x)
    hT hS (B_posSemidef hA).isHermitian (cfc_predicate b (A x)) (cfc_predicate l (A x))
    hk (X_hermitian hA) (fun r => hg r x)
    (fun r => by simp only [D, add_sub_cancel]) rfl rfl hSM hMSM he hp hh rfl
    (fun r => rfl) (fun r => rfl)
  simpa only [E2,u,Core,Comm,defect₁,defect₂,two_smul] using ht

lemma FCRegular.defect₁_integrable {A : E m → Mat m} (hr : FCRegular A)
    (hA : ∀ x, (A x).IsHermitian) : Integrable (defect₁ A) (γ m) := by
  have ha := (hr.A_lp hA).sub (hr.Y_lp hA)
  have hp : MatrixLp (γ m) 1 (fun x => (A x-Y A x)*c A f x) := ha.mul (hr.lp smooth_f 2)
  have hd : MatrixLp (γ m) 1 (fun x => ∑ r, X A r*d (c A f) r x) :=
    (MatrixLp.sum fun r => ((hr f smooth_f).2.2 r).const_mul (X A r)).mono (by norm_num)
  exact ((hp.sub hd).const_mul (T A)).integrable_trace

lemma FCRegular.defect₂_integrable {A : E m → Mat m} (hr : FCRegular A)
    (hA : ∀ x, (A x).IsHermitian) {g : Fin m → E m → Mat m}
    (hg : ∀ r, MatrixLp (γ m) 2 (g r)) : Integrable (defect₂ A g) (γ m) :=
  (((hr.Y_lp hA).const_mul (T A)).mul (hr.lp smooth_k 2)).integrable_trace.sub
    ((MatrixLp.sum fun r => (hr.K_lp r).mul (hg r)).const_mul (T A)).integrable_trace

lemma exact_of_defects (A : E m → Mat m) (hA : ∀ x, (A x).IsHermitian) (hr : FCRegular A)
    (g : Fin m → E m → Mat m) (hgs : ∀ r x, (g r x).IsHermitian)
    (hgl : ∀ r, MatrixLp (γ m) 2 (g r))
    (h₁ : ∫ x, defect₁ A x ∂γ m = 0) (h₂ : ∫ x, defect₂ A g x ∂γ m = 0) :
    (∫ x, (T A*E2 A x).trace ∂γ m)+(∫ x, ((u A x).transpose*S A*u A x).trace ∂γ m)+
      (∑ r, ∫ x, ((v A g r x).transpose*S A*v A g r x).trace ∂γ m) =
    (T A).trace+∫ x, Core A g x+Comm A g x ∂γ m :=
  integrate_expansion (T A).trace (hr.E2_lp.const_mul (T A)).integrable_trace
    ((hr.u_lp hA).integrable_weighted_square (S A))
    (fun r => (hr.v_lp hgl r).integrable_weighted_square (S A))
    (hr.defect₁_integrable hA) (hr.defect₂_integrable hA hgl) h₁ h₂
    (expansion_with_defects A hA g hgs)

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
