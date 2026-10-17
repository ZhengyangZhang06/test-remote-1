import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.Data
import Submission.Obl.Entropy__c1_bounded_matrix_calculus

open scoped ContDiff

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

lemma regularity_of_bounded {m : ℕ} (hm : 1 ≤ m) {A : Field m}
    (hA : ∀ x, (A x).IsHermitian)
    (hsm : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    (hZ : ∀ r, MatrixLp (gaussian m) 2 (coordDeriv A r)) : Regularity A := by
  intro f hf
  have hc1 (i j) := (hsm i j).of_le (show (1 : WithTop ENat) ≤ ∞ by simp)
  obtain ⟨hc, hbound⟩ := Submission.Entropy.c1_bounded_matrix_calculus m hm A hA hc1 hb f
    (hf.of_le (by simp))
  refine ⟨hc, hbound, fun r => ?_⟩
  exact Submission.Obl.Entropy__c1_bounded_matrix_calculus.memLp_entryDirectionalDerivative_cfc_of_bounded
    A (fun i j => (hsm i j).continuous) hA hb (hf.of_le (by simp))
    (fun x i j => (hsm i j).differentiable (by simp) x)
    (PiLp.single 2 r (1 : ℝ)) (hZ r)

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
