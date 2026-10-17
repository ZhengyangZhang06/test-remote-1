import Submission.Obl.Entropy__normalized_remainder.CFCSobolev

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__normalized_remainder

/-- Polynomial antiderivatives used for approximation in the C1 norm. -/
lemma exists_polynomial_antiderivative (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      exact ⟨P + Q, by simp [hP, hQ]⟩
  | monomial k a =>
      refine ⟨Polynomial.monomial (k + 1) (a / (k + 1 : ℝ)), ?_⟩
      rw [Polynomial.derivative_monomial_succ]
      congr 1
      field_simp

lemma exists_polynomial_deriv_near {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ t ∈ Set.Icc a b, |deriv f t - deriv p.eval t| ≤ ε := by
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (deriv f)
    (hf.continuous_deriv (by norm_num)).continuousOn ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_antiderivative q
  refine ⟨p, fun t ht => ?_⟩
  simpa only [Polynomial.deriv, hp, abs_sub_comm] using (hq t ht).le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma contDiff_matrix_aeval {A : E → Matrix n n ℝ} {k : WithTop ℕ∞}
    (hA : ContDiff ℝ k A) (p : Polynomial ℝ) :
    ContDiff ℝ k (fun x => Polynomial.aeval (A x) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial d a =>
      simpa only [Polynomial.aeval_monomial] using contDiff_const.mul (hA.pow d)

lemma contDiff_cfc_polynomial {A : E → Matrix n n ℝ} {k : WithTop ℕ∞}
    (hA : ContDiff ℝ k A) (hAH : ∀ x, (A x).IsHermitian) (p : Polynomial ℝ) :
    ContDiff ℝ k (fun x => cfc p.eval (A x)) := by
  have he : (fun x => cfc p.eval (A x)) = fun x => Polynomial.aeval (A x) p := by
    funext x
    exact cfc_polynomial p (A x) (hAH x).isSelfAdjoint
  rw [he]
  exact contDiff_matrix_aeval hA p

lemma entryDirectionalDerivative_sub_cfc (A : E → Matrix n n ℝ)
    (hAc : Continuous A) (hAH : ∀ x, (A x).IsHermitian)
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {x : E} (hAd : DifferentiableAt ℝ A x) (v : E) :
    entryDirectionalDerivative (fun y => cfc (fun t => f t - g t) (A y)) x v =
      entryDirectionalDerivative (fun y => cfc f (A y)) x v -
        entryDirectionalDerivative (fun y => cfc g (A y)) x v := by
  have hFd := (hasFDerivAt_cfc hAc hAH hf hAd.hasFDerivAt).differentiableAt
  have hGd := (hasFDerivAt_cfc hAc hAH hg hAd.hasFDerivAt).differentiableAt
  have he : (fun y => cfc (fun t => f t - g t) (A y)) =
      (fun y => cfc f (A y) - cfc g (A y)) := by
    funext y
    exact cfc_sub f g (A y) hf.continuous.continuousOn hg.continuous.continuousOn
  have hSub : DifferentiableAt ℝ (fun y => cfc f (A y) - cfc g (A y)) x := hFd.sub hGd
  rw [he, entryDirectionalDerivative_eq_fderiv hSub,
    entryDirectionalDerivative_eq_fderiv hFd, entryDirectionalDerivative_eq_fderiv hGd,
    fderiv_fun_sub hFd hGd]
  rfl

lemma entryDirectionalDerivative_cfc_sub_bound (A : E → Matrix n n ℝ)
    (hAc : Continuous A) (hAH : ∀ x, (A x).IsHermitian)
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {x : E} (hAd : DifferentiableAt ℝ A x) (v : E)
    {s : Set ℝ} (hs : Convex ℝ s) (hspec : spectrum ℝ (A x) ⊆ s)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ s, |deriv f t - deriv g t| ≤ δ)
    (henergy : matrixSquareSum (entryDirectionalDerivative A x v) ≤ M^2) (i j : n) :
    |entryDirectionalDerivative (fun y => cfc f (A y)) x v i j -
      entryDirectionalDerivative (fun y => cfc g (A y)) x v i j| ≤ δ * M := by
  have hEntry (i j : n) : DifferentiableAt ℝ (fun y => A y i j) x := by
    let ev : Matrix n n ℝ →L[ℝ] ℝ :=
      { toLinearMap :=
          { toFun := fun M => M i j
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        cont := (continuous_apply j).comp (continuous_apply i) }
    exact ev.differentiableAt.comp x hAd
  have he := entryDirectionalDerivative_cfc_squareSum_le A
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hAc)) hAH
    (hf.sub hg) hEntry v hs hspec hδ (fun t ht => by
      simpa only [deriv_sub (hf t) (hg t)] using hbound t ht)
  change matrixSquareSum (entryDirectionalDerivative
    (fun y => cfc (fun t => f t - g t) (A y)) x v) ≤ _ at he
  rw [entryDirectionalDerivative_sub_cfc A hAc hAH hf hg hAd v] at he
  have hsq := (entry_sq_le_matrixSquareSum
    (entryDirectionalDerivative (fun y => cfc f (A y)) x v -
      entryDirectionalDerivative (fun y => cfc g (A y)) x v) i j).trans he
  have hsq' := hsq.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg δ))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hδ hM)).1
  simpa only [sq_abs, mul_pow, Matrix.sub_apply] using hsq'

end Submission.Obl.Entropy__normalized_remainder
