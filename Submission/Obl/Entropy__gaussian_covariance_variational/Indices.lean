import Submission.Obl.Entropy__gaussian_chaos_resolvent.Coefficients

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_covariance_variational

open Submission.Obl.Entropy__gaussian_chaos_resolvent

variable {m : ℕ}

noncomputable def lowerIndex (a : Fin m → ℕ) (r : Fin m) : Fin m → ℕ :=
  Function.update a r (a r - 1)

@[simp] lemma lowerIndex_raiseIndex (a : Fin m → ℕ) (r : Fin m) :
    lowerIndex (raiseIndex a r) r = a := by
  classical
  funext i
  by_cases hi : i = r
  · subst i
    simp [lowerIndex]
  · simp [lowerIndex, raiseIndex, Function.update_of_ne hi]

lemma raiseIndex_lowerIndex (a : Fin m → ℕ) (r : Fin m) (hr : 0 < a r) :
    raiseIndex (lowerIndex a r) r = a := by
  classical
  funext i
  by_cases hi : i = r
  · subst i
    simp only [raiseIndex_self, lowerIndex, Function.update_self]
    omega
  · simp [lowerIndex, raiseIndex, Function.update_of_ne hi]

/-- A lowered coefficient is counted once when summing over its positive successors. -/
lemma tsum_lowerIndex (r : Fin m) (F : (Fin m → ℕ) → ℝ) :
    (∑' a, if 0 < a r then F (lowerIndex a r) else 0) = ∑' a, F a := by
  classical
  have hs : Function.support (fun a => if 0 < a r then F (lowerIndex a r) else 0) ⊆
      Set.range (fun a => raiseIndex a r) := by
    intro a ha
    apply (mem_range_raiseIndex r a).2
    by_contra hn
    exact ha (by simp [hn])
  simpa using ((raiseIndex_injective r).tsum_eq hs).symm

lemma summable_lowerIndex (r : Fin m) {F : (Fin m → ℕ) → ℝ} (hF : Summable F) :
    Summable (fun a => if 0 < a r then F (lowerIndex a r) else 0) := by
  classical
  have hz : ∀ a ∉ Set.range (fun a => raiseIndex a r),
      (if 0 < a r then F (lowerIndex a r) else 0) = 0 := by
    intro a ha
    have hn : ¬0 < a r := by simpa only [mem_range_raiseIndex] using ha
    simp [hn]
  apply ((raiseIndex_injective r).summable_iff hz).1
  simpa [Function.comp_def] using hF

/-- One Gaussian adjoint coefficient obeys the sharp H-minus-one dual bound. -/
lemma coefficient_dual_bound (a : Fin m → ℕ) (A : ℝ) (B : Fin m → ℝ) :
    (A - ∑ r, Real.sqrt (a r : ℝ) * B r)^2 / (chaosDegree a + 1 : ℝ) ≤
      A^2 + ∑ r, if 0 < a r then (B r)^2 else 0 := by
  classical
  let u : Option (Fin m) → ℝ := Option.elim' 1 (fun r => Real.sqrt (a r : ℝ))
  let v : Option (Fin m) → ℝ := Option.elim' A
    (fun r => if 0 < a r then -B r else 0)
  have hsum : (∑ i, u i * v i) = A - ∑ r, Real.sqrt (a r : ℝ) * B r := by
    simp only [u, v, Fintype.sum_option, Option.elim'_none, Option.elim'_some, one_mul]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : 0 < a r
    · simp [hr]
    · have h0 : a r = 0 := by omega
      simp [h0]
  have hu : (∑ i, (u i)^2) = (chaosDegree a + 1 : ℝ) := by
    simp [u, Fintype.sum_option, Real.sq_sqrt (Nat.cast_nonneg _), chaosDegree, add_comm]
  have hv : (∑ i, (v i)^2) = A^2 + ∑ r, if 0 < a r then (B r)^2 else 0 := by
    simp only [v, Fintype.sum_option, Option.elim'_none, Option.elim'_some]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  rw [hsum, hu, hv] at h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < chaosDegree a + 1)).2
  simpa [mul_comm] using h

/-- Parseval and the one-step coefficient bound control the Gaussian resolvent form. -/
theorem resolvent_dual_bound (D A : GaussianL2 m) (B : Fin m → GaussianL2 m)
    (heq : ∀ a, gaussianCoeff D a = gaussianCoeff A a -
      ∑ r, Real.sqrt (a r : ℝ) * gaussianCoeff (B r) (lowerIndex a r)) :
    inner ℝ (resolventComponent D) D ≤ ‖A‖^2 + ∑ r, ‖B r‖^2 := by
  classical
  have hs (r : Fin m) := summable_lowerIndex r (summable_gaussianCoeff_sq (B r))
  have hsum : (∑' a, ((gaussianCoeff A a)^2 +
      ∑ r, if 0 < a r then (gaussianCoeff (B r) (lowerIndex a r))^2 else 0)) =
      ‖A‖^2 + ∑ r, ‖B r‖^2 := by
    rw [Summable.tsum_add (summable_gaussianCoeff_sq A) (summable_sum (fun r _ => hs r)),
      tsum_gaussianCoeff_sq, Summable.tsum_finsetSum (fun r _ => hs r)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    exact (tsum_lowerIndex r (fun a => (gaussianCoeff (B r) a)^2)).trans
      (tsum_gaussianCoeff_sq (B r))
  rw [← tsum_gaussianCoeff_mul, ← hsum]
  apply Summable.tsum_le_tsum _ (summable_gaussianCoeff_mul _ _)
    ((summable_gaussianCoeff_sq A).add (summable_sum (fun r _ => hs r)))
  intro a
  rw [gaussianCoeff_resolventComponent, div_mul_eq_mul_div, ← pow_two, heq]
  exact coefficient_dual_bound a (gaussianCoeff A a)
    (fun r => gaussianCoeff (B r) (lowerIndex a r))

end Submission.Obl.Entropy__gaussian_covariance_variational
