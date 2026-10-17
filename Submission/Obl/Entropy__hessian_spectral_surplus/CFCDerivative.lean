import Submission.Obl.Entropy__hessian_spectral_surplus.CFCDifference

open scoped BigOperators Topology
open Matrix Filter Asymptotics

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A continuous coefficient can multiply a differentiable factor that vanishes at the base point. -/
lemma hasFDerivAt_mul_of_zero {u v : E → ℝ} {u' : E →L[ℝ] ℝ} {x : E}
    (hu : HasFDerivAt u u' x) (hv : ContinuousAt v x) (hux : u x = 0) :
    HasFDerivAt (fun y => u y * v y) (v x • u') x := by
  have hsmall : (fun y => u y * (v y - v x)) =o[𝓝 x] (fun y => y - x) := by
    have huO : u =O[𝓝 x] (fun y => ‖y - x‖) := by
      simpa only [hux, sub_zero] using hu.isBigO_sub.norm_right
    have hvO : (fun y => v y - v x) =o[𝓝 x] (fun _ : E => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 (by simpa using hv.tendsto.sub_const (v x))
    simpa only [mul_one, isLittleO_norm_right] using huO.mul_isLittleO hvO
  have hz : HasFDerivAt (fun y => u y * (v y - v x)) (0 : E →L[ℝ] ℝ) x := by
    rw [hasFDerivAt_iff_isLittleO]
    simpa only [sub_self, mul_zero, sub_zero, _root_.zero_apply] using hsmall
  have h := ((hu.const_mul (v x)).add hz)
  convert! h using 1
  · ext y
    simp only [Pi.add_apply]
    ring
  · simp

open scoped Matrix.Norms.L2Operator in
/-- Continuous scalar functions act continuously on Hermitian matrix fields. -/
lemma continuous_cfc_matrix {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x => cfc f (A x)) := by
  exact Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) (by simp) hAc hA hf.continuousOn

lemma continuous_dslope_of_differentiable {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (a : ℝ) : Continuous (dslope f a) := by
  rw [← continuousOn_univ, continuousOn_dslope (by simp)]
  exact ⟨hf.continuous.continuousOn, hf a⟩

/-- Directional derivatives of multiplication by fixed coordinate matrices. -/
lemma hasFDerivAt_matrix_conjugate {A : E → Matrix n n ℝ} {x : E}
    {D : n → n → E →L[ℝ] ℝ} (hD : ∀ i j, HasFDerivAt (fun y => A y i j) (D i j) x)
    (P Q : Matrix n n ℝ) (i j : n) :
    HasFDerivAt (fun y => (P * A y * Q) i j)
      (∑ s, ∑ t, (P i t * Q s j) • D t s) x := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  convert! HasFDerivAt.sum fun s (_ : s ∈ Finset.univ) =>
    HasFDerivAt.sum fun t (_ : t ∈ Finset.univ) =>
      (hD t s).const_mul (P i t * Q s j) using 1
  · ext y
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring


open Submission.Lib.PairEstimate

/-- The divided-difference derivative formula, with the eigenbasis fixed at the base point. -/
theorem hasFDerivAt_cfc_conjugate {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ y, (A y).IsHermitian) (hAc : Continuous A)
    {D : n → n → E →L[ℝ] ℝ} (hD : ∀ i j, HasFDerivAt (fun y => A y i j) (D i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i j : n) :
    let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
    HasFDerivAt (fun y => (U.transpose * cfc f (A y) * U) i j)
      (dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) •
        ∑ s, ∑ t, (U t i * U s j) • D t s) x := by
  dsimp only
  let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
  let g := dslope f ((hA x).eigenvalues i)
  let V : E → Matrix n n ℝ := fun y => cfc g (A y) * U
  have hVc : Continuous V :=
    (continuous_cfc_matrix hA hAc (continuous_dslope_of_differentiable hf _)).matrix_mul
      continuous_const
  have hrow (s : n) : HasFDerivAt (fun y => (U.transpose * (A y - A x)) i s)
      (∑ t, U t i • D t s) x := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply] using
      HasFDerivAt.fun_sum (u := Finset.univ) (fun t _ =>
        ((hD t s).sub_const (A x t s)).const_mul (U t i))
  have hprod (s : n) : HasFDerivAt
      (fun y => (U.transpose * (A y - A x)) i s * V y s j)
      (V x s j • ∑ t, U t i • D t s) x := by
    apply hasFDerivAt_mul_of_zero (hrow s)
    · exact ((continuous_apply j).comp ((continuous_apply s).comp hVc)).continuousAt
    · simp
  have hdiff (y : E) :
      (U.transpose * (cfc f (A y) - cfc f (A x)) * U) i j =
        ∑ s, (U.transpose * (A y - A x)) i s * V y s j := by
    calc
      _ = (U.transpose * (A y - A x) * cfc g (A y) * U) i j := by
        change (∑ t, (U.transpose * (cfc f (A y) - cfc f (A x))) i t * U t j) =
          ∑ t, (U.transpose * (A y - A x) * cfc g (A y)) i t * U t j
        apply Finset.sum_congr rfl
        intro t _
        rw [cfc_difference_row (hA x) (hA y) f i t]
      _ = _ := by rw [Matrix.mul_assoc]; rfl
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => hprod s)
  have hright : cfc g (A x) * U = U * Matrix.diagonal (fun t => g ((hA x).eigenvalues t)) := by
    have h := congrArg (fun M : Matrix n n ℝ => U * M) (cfc_in_eigenbasis (hA x) g)
    change U * (U.transpose * cfc g (A x) * U) = _ at h
    have hU : U * U.transpose = 1 := eigenbasis_mul_transpose_self (hA x)
    simpa only [← Matrix.mul_assoc, hU, Matrix.one_mul] using h
  have hcoeff : (∑ s, V x s j • ∑ t, U t i • D t s) =
      dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) •
        ∑ s, ∑ t, (U t i * U s j) • D t s := by
    simp only [V, hright, Matrix.mul_diagonal, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    dsimp [g]
    ring
  rw [hcoeff] at hd
  convert! hd.add_const ((U.transpose * cfc f (A x) * U) i j) using 1
  ext y
  rw [← hdiff]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, sub_add_cancel]
  rfl


/-- Entrywise differentiability of a scalar function of a Hermitian matrix field. -/
theorem differentiableAt_cfc_entry {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ y, (A y).IsHermitian) (hAc : Continuous A)
    (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i j : n) :
    DifferentiableAt ℝ (fun y => cfc f (A y) i j) x := by
  let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
  have hU : U * U.transpose = 1 := eigenbasis_mul_transpose_self (hA x)
  have h := hasFDerivAt_matrix_conjugate
    (fun s t => hasFDerivAt_cfc_conjugate hA hAc (fun i j => (hAd i j).hasFDerivAt) hf s t)
    U U.transpose i j
  convert! h.differentiableAt using 1
  ext y
  change cfc f (A y) i j = (U * (U.transpose * cfc f (A y) * U) * U.transpose) i j
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- Daleckii--Krein's formula in any direction, including repeated eigenvalues. -/
theorem cfc_fderiv_in_eigenbasis {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ y, (A y).IsHermitian) (hAc : Continuous A)
    (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (v : E) (i j : n) :
    let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
    (U.transpose * Matrix.of (fun s t => fderiv ℝ (fun y => cfc f (A y) s t) x v) * U) i j =
      dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        (U.transpose * Matrix.of (fun s t => fderiv ℝ (fun y => A y s t) x v) * U) i j := by
  dsimp only
  let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
  have h₁ := hasFDerivAt_matrix_conjugate
    (fun s t => (differentiableAt_cfc_entry hA hAc hAd hf s t).hasFDerivAt) U.transpose U i j
  have h₂ := hasFDerivAt_cfc_conjugate hA hAc (fun s t => (hAd s t).hasFDerivAt) hf i j
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (h₁.unique h₂)
  simpa only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, U] using h


/-- A bound on scalar divided differences controls the Frobenius norm of the derivative. -/
theorem cfc_fderiv_squareSum_le {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ y, (A y).IsHermitian) (hAc : Continuous A)
    (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ}
    (hC : ∀ i j, dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) ^ 2 ≤ C ^ 2)
    (v : E) :
    (∑ i, ∑ j, (fderiv ℝ (fun y => cfc f (A y) i j) x v) ^ 2) ≤
      C ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fun y => A y i j) x v) ^ 2 := by
  let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
  let Z : Matrix n n ℝ := Matrix.of (fun i j => fderiv ℝ (fun y => A y i j) x v)
  let K : Matrix n n ℝ := Matrix.of (fun i j => fderiv ℝ (fun y => cfc f (A y) i j) x v)
  change (∑ i, ∑ j, (K i j) ^ 2) ≤ C ^ 2 * ∑ i, ∑ j, (Z i j) ^ 2
  have hU : U * U.transpose = 1 := eigenbasis_mul_transpose_self (hA x)
  rw [← squareSum_orthogonal U K hU, ← squareSum_orthogonal U Z hU]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hd := cfc_fderiv_in_eigenbasis hA hAc hAd hf v i j
  change (U.transpose * K * U) i j = _ at hd
  rw [hd, mul_pow]
  exact mul_le_mul_of_nonneg_right (hC i j) (sq_nonneg _)

end Submission.Obl.Entropy__hessian_spectral_surplus
