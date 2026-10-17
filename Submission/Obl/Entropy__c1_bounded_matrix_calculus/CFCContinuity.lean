/-
Adapted from: here:o006
Original matrix functional-calculus derivative proofs by session x0063.
-/

import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCRegularity

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a C1 Hermitian field and a C1 scalar function, every entry of every
fixed directional derivative of the CFC field is continuous. -/
lemma continuous_entryDirectionalDerivative_cfc {A : E → Matrix n n ℝ}
    (hA : ContDiff ℝ 1 A) (hAH : ∀ x, (A x).IsHermitian)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (v : E) (i j : n) :
    Continuous (fun x => entryDirectionalDerivative (fun y => cfc f (A y)) x v i j) := by
  have hAd := hA.differentiable (by norm_num)
  have hfd := hf.differentiable (by norm_num)
  have hH : Continuous (fun x => fderiv ℝ A x v) :=
    (hA.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hS : Continuous (fun x => matrixSquareSum (fderiv ℝ A x v)) := by
    apply continuous_finsetSum
    intro k _
    apply continuous_finsetSum
    intro l _
    exact ((continuous_apply l).comp ((continuous_apply k).comp hH)).pow 2
  rw [continuous_iff_continuousAt]
  intro x₀
  apply Metric.tendsto_nhds.2
  intro ε hε
  let M := |matrixSquareSum (fderiv ℝ A x₀ v)| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg (matrixSquareSum (fderiv ℝ A x₀ v))]
  have hS₀ : matrixSquareSum (fderiv ℝ A x₀ v) < M := by
    dsimp [M]
    linarith [le_abs_self (matrixSquareSum (fderiv ℝ A x₀ v))]
  have hSn : ∀ᶠ x in 𝓝 x₀, matrixSquareSum (fderiv ℝ A x v) < M :=
    hS.continuousAt.eventually (Iio_mem_nhds hS₀)
  let R := ‖A x₀‖ + 1
  have hR₀ : ‖A x₀‖ < R := by dsimp [R]; linarith
  have hRn : ∀ᶠ x in 𝓝 x₀, ‖A x‖ < R :=
    hA.continuous.norm.continuousAt.eventually (Iio_mem_nhds hR₀)
  have hspec (x : E) (hx : ‖A x‖ < R) : spectrum ℝ (A x) ⊆ Set.Icc (-R) R := by
    intro t ht
    have hn := IsometricContinuousFunctionalCalculus.norm_spectrum_le (A x) ht
      (hAH x).isSelfAdjoint
    have ht' : |t| ≤ ‖A x‖ := by simpa only [Real.norm_eq_abs] using hn
    exact abs_le.1 (ht'.trans hx.le)
  let δ := ε / (4 * M)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hM)
  have hδM : δ * M = ε / 4 := by dsimp [δ]; field_simp
  obtain ⟨p, hp⟩ := exists_polynomial_deriv_near hf (-R) R hδ
  have hpc := contDiff_cfc_polynomial hA hAH p
  have hpDc : Continuous (fun x => entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j) := by
    have he : (fun x => entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j) =
        fun x => fderiv ℝ (fun y => cfc p.eval (A y)) x v i j := by
      funext x
      rw [entryDirectionalDerivative_eq_fderiv (hpc.differentiable (by norm_num) x)]
    rw [he]
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((hpc.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  have hpn : ∀ᶠ x in 𝓝 x₀,
      dist (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j)
        (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x₀ v i j) < ε / 2 :=
    (Metric.tendsto_nhds.1 hpDc.continuousAt (ε / 2) (by positivity))
  have herr (x : E) (hxR : ‖A x‖ < R)
      (hxS : matrixSquareSum (fderiv ℝ A x v) < M) :
      |entryDirectionalDerivative (fun y => cfc f (A y)) x v i j -
        entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j| ≤ ε / 4 := by
    rw [← hδM]
    apply entryDirectionalDerivative_cfc_sub_bound A hA.continuous hAH hfd
      p.differentiable (hAd x) v (convex_Icc (-R) R) (hspec x hxR) hδ.le hM.le hp
    rw [entryDirectionalDerivative_eq_fderiv (hAd x)]
    exact hxS.le.trans (by nlinarith)
  filter_upwards [hRn, hSn, hpn] with x hxR hxS hxp
  rw [Real.dist_eq] at hxp ⊢
  have h₁ := herr x hxR hxS
  have h₀ := herr x₀ hR₀ hS₀
  have htri := abs_sub_le
    (entryDirectionalDerivative (fun y => cfc f (A y)) x v i j)
    (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j)
    (entryDirectionalDerivative (fun y => cfc f (A y)) x₀ v i j)
  have htri' := abs_sub_le
    (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x v i j)
    (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x₀ v i j)
    (entryDirectionalDerivative (fun y => cfc f (A y)) x₀ v i j)
  rw [abs_sub_comm (entryDirectionalDerivative (fun y => cfc p.eval (A y)) x₀ v i j)] at htri'
  linarith

/-- C1 real functional calculus preserves C1 Hermitian matrix fields. -/
lemma contDiff_one_cfc {A : E → Matrix n n ℝ} [FiniteDimensional ℝ E]
    (hA : ContDiff ℝ 1 A) (hAH : ∀ x, (A x).IsHermitian)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun x => cfc f (A x)) := by
  have hdiff : Differentiable ℝ (fun x => cfc f (A x)) := fun x =>
    (hasFDerivAt_cfc hA.continuous hAH (hf.differentiable (by norm_num))
      (hA.differentiable (by norm_num) x).hasFDerivAt).differentiableAt
  apply contDiff_one_iff_fderiv.2 ⟨hdiff, ?_⟩
  apply continuous_clm_apply.2
  intro v
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h := continuous_entryDirectionalDerivative_cfc hA hAH hf v i j
  simpa only [entryDirectionalDerivative_eq_fderiv (hdiff _)] using h

/-- Entrywise smoothness is independent of the chosen finite-dimensional matrix norm. -/
lemma contDiff_matrix_of_entries {A : E → Matrix n n ℝ} {k : WithTop ℕ∞}
    (hA : ∀ i j, ContDiff ℝ k (fun x => A x i j)) : ContDiff ℝ k A := by
  let e : (n → n → ℝ) ≃L[ℝ] Matrix n n ℝ :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have hpi : ContDiff ℝ k (fun x i j => A x i j) :=
    contDiff_pi.2 (fun i => contDiff_pi.2 (hA i))
  exact e.contDiff.comp hpi

lemma contDiff_one_cfc_entries {A : E → Matrix n n ℝ} [FiniteDimensional ℝ E]
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∀ i j, ContDiff ℝ 1 (fun x => cfc f (A x) i j) := by
  intro i j
  let ev : Matrix n n ℝ →L[ℝ] ℝ :=
    { toLinearMap :=
        { toFun := fun M => M i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply j).comp (continuous_apply i) }
  exact ev.contDiff.comp (contDiff_one_cfc (contDiff_matrix_of_entries hA) hAH hf)

end Submission.Obl.Entropy__c1_bounded_matrix_calculus
