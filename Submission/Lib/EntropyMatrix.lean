import Mathlib
import Submission.Lib.EntropyTools.Remainder

/-!
# Matrix lemmas for entropy equality

The algebraic part of Section 6, Lemma 6.1 and the general spectral contraction
argument of Lemma 6.2 from the supplied paper. All proofs were written in this
workspace. No scalar Gaussian hazard estimates are assumed implicitly.
-/

namespace Submission.Lib.EntropyMatrix

/-- Commuting symmetric endomorphisms have a common orthonormal eigenbasis. -/
theorem joint_orthonormalBasis {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ι → E →ₗ[ℝ] E) (hT : ∀ r, (T r).IsSymmetric)
    (hcomm : ∀ r s, Commute (T r) (T s))
    {m : ℕ} (hm : Module.finrank ℝ E = m) :
    ∃ b : OrthonormalBasis (Fin m) ℝ E, ∃ eig : ι → Fin m → ℝ,
      ∀ r j, T r (b j) = eig r j • b j := by
  classical
  let χ : (∀ r, Module.End.Eigenvalues (T r)) → (ι → ℝ) := fun u r => u r
  have hχ : Function.Injective χ := by
    intro u v h
    funext r
    exact Subtype.ext (congrFun h r)
  have hO := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT).comp hχ
  have hsup : (⨆ u : ∀ r, Module.End.Eigenvalues (T r),
      ⨅ r, Module.End.eigenspace (T r) (χ u r)) = ⊤ := by
    apply top_unique
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT
      (fun r s _ => hcomm r s)]
    apply iSup_le
    intro u
    by_cases hu : ∀ r, Module.End.HasEigenvalue (T r) (u r)
    · exact le_iSup_of_le (fun r => ⟨u r, hu r⟩) le_rfl
    · obtain ⟨r, hr⟩ := not_forall.mp hu
      have hr' : Module.End.eigenspace (T r) (u r) = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using hr
      exact (iInf_le _ r).trans (hr'.le.trans bot_le)
  have hI := hO.isInternal_iff.mpr (by rw [hsup, Submodule.top_orthogonal_eq_bot])
  refine ⟨hI.subordinateOrthonormalBasis hm hO,
    fun r j => χ (hI.subordinateOrthonormalBasisIndex hm j hO) r, ?_⟩
  intro r j
  exact Module.End.mem_eigenspace_iff.mp
    ((Submodule.mem_iInf _).mp (hI.subordinateOrthonormalBasis_subordinate hm j hO) r)

/-- Matrix formulation of the common eigenbasis. -/
theorem matrix_joint_orthonormalBasis {m : ℕ} (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hcomm : ∀ r s, Commute (X r) (X s)) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ eig : Fin m → Fin m → ℝ,
        ∀ r j, (X r).toEuclideanLin (b j) = eig r j • b j := by
  apply joint_orthonormalBasis (fun r => (X r).toEuclideanLin)
  · intro r
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (hX r)
  · intro r s
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec, (hcomm r s).eq]
  · simp

end Submission.Lib.EntropyMatrix

/-! Algebraic coefficient identities in the rigidity lemma of Section 6. -/

namespace Submission.Lib.EntropyMatrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear symmetric-matrix field determined by its coefficient matrices. -/
def linearField (X : ι → Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ r, x r • X r

/-- The constant compatibility identity is symmetry in the coefficient and column indices. -/
def CoefficientSymmetry (X : ι → Matrix ι ι ℝ) : Prop :=
  ∀ r s i, X r i s = X s i r

omit [DecidableEq ι] in
/-- Coefficient symmetry exchanges the two arguments of the associated bilinear map. -/
theorem linearField_mulVec_comm (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X) (x y : ι → ℝ) :
    linearField X x *ᵥ y = linearField X y *ᵥ x := by
  ext i
  simp only [linearField, mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hX r s i]
  ring

omit [DecidableEq ι] in
/-- The constant and linear terms of Jacobian compatibility force the coefficients to commute. -/
theorem coefficients_commute (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r) :
    ∀ r s, Commute (X r) (X s) := by
  intro r s
  change X r * X s = X s * X r
  ext i t
  have h := h₂ r s t i
  simp only [Matrix.add_apply, mul_apply] at h ⊢
  simp_rw [hX t s, hX t r, hX r s] at h
  exact add_right_cancel h

omit [Fintype ι] in
/-- Once the coefficients are diagonal, coefficient symmetry leaves a single possible entry. -/
theorem diagonal_coefficients (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (hdiag : ∀ r i j, i ≠ j → X r i j = 0) (r : ι) :
    X r = diagonal (Pi.single r (X r r r)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hir : i = r
    · subst i
      simp
    · rw [hX r i i, hdiag i i r hir]
      simp [hir]
  · rw [hdiag r i j hij]
    simp [hij]

/-- The square-sum normalization makes the surviving diagonal entries signs. -/
theorem diagonal_coefficients_signs (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X)
    (hdiag : ∀ r i j, i ≠ j → X r i j = 0)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ r, X r = diagonal (Pi.single r (σ r)) := by
  refine ⟨fun r => X r r r, ?_, diagonal_coefficients X hX hdiag⟩
  intro i
  have hsq' : (∑ r, diagonal (Pi.single r (X r r r)) *
      diagonal (Pi.single r (X r r r))) = 1 := by
    simpa only [← diagonal_coefficients X hX hdiag] using hsq
  have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hsq'
  simp only [diagonal_mul_diagonal, Matrix.sum_apply, diagonal_apply_eq, one_apply_eq] at h
  have hi : X i i i * X i i i = 1 := by
    simpa [Pi.single_apply] using h
  have hfactor : (X i i i - 1) * (X i i i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end Submission.Lib.EntropyMatrix

namespace Submission.Lib.EntropyMatrix

open Matrix

/-- Simultaneous orthogonal diagonalization of the coefficient matrices. -/
theorem simultaneous_diagonalization {m : ℕ} (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hcomm : ∀ r s, Commute (X r) (X s)) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ eig : Fin m → Fin m → ℝ,
        ∀ r, U.transpose * X r * U = diagonal (eig r) := by
  obtain ⟨b, eig, heig⟩ := matrix_joint_orthonormalBasis X hX hcomm
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  let U := e.toBasis.toMatrix b
  have hU : ∀ i j, U i j = b j i := by
    intro i j
    simp [U, e, Module.Basis.toMatrix_apply]
  have hUU : U * U.transpose = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      e.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hUtU : U.transpose * U = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      e.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  refine ⟨U, hUU, hUtU, eig, ?_⟩
  intro r
  have hXU : X r * U = U * diagonal (eig r) := by
    ext i j
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) (heig r j)
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hU]
    simpa only [Matrix.toLpLin_apply, PiLp.smul_apply, Matrix.mulVec, dotProduct,
      smul_eq_mul, mul_comm] using h
  rw [Matrix.mul_assoc, hXU, ← Matrix.mul_assoc, hUtU, Matrix.one_mul]

end Submission.Lib.EntropyMatrix

namespace Submission.Lib.EntropyMatrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change the coordinates of both the domain and the range of a linear matrix field. -/
def rotatedCoefficients (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (r : ι) :
    Matrix ι ι ℝ :=
  U.transpose * linearField X (fun s => U s r) * U

omit [DecidableEq ι] in
/-- Symmetry of the coefficient tensor is invariant under a change of variables. -/
theorem rotatedCoefficients_symmetry (X : ι → Matrix ι ι ℝ)
    (hX : CoefficientSymmetry X) (U : Matrix ι ι ℝ) :
    CoefficientSymmetry (rotatedCoefficients X U) := by
  intro r s i
  have h := congrFun (congrArg (fun v => U.transpose *ᵥ v)
    (linearField_mulVec_comm X hX (fun k => U k r) (fun k => U k s))) i
  change (U.transpose * linearField X (fun k => U k r) * U) i s =
    (U.transpose * linearField X (fun k => U k s) * U) i r
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- Mixing a family by an orthogonal matrix preserves its sum of squares. -/
theorem linearField_sum_square (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) :
    ∑ r, linearField X (fun s => U s r) * linearField X (fun s => U s r) =
      ∑ r, X r * X r := by
  have hu : ∀ s t, ∑ r, U s r * U t r = if s = t then 1 else 0 := by
    intro s t
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix ι ι ℝ => M s t) hU
  simp only [linearField, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hu]
  simp

/-- Orthogonal rotation preserves the normalization on coefficient squares. -/
theorem rotatedCoefficients_sum_square (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ)
    (hUU : U * U.transpose = 1) (hUtU : U.transpose * U = 1)
    (hX : ∑ r, X r * X r = 1) :
    ∑ r, rotatedCoefficients X U r * rotatedCoefficients X U r = 1 := by
  have h (M : Matrix ι ι ℝ) :
      (U.transpose * M * U) * (U.transpose * M * U) =
        U.transpose * (M * M) * U := by
    calc
      _ = U.transpose * M * (U * U.transpose) * M * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [rotatedCoefficients, h]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, linearField_sum_square X U hUU, hX]
  simpa using hUtU

end Submission.Lib.EntropyMatrix

namespace Submission.Lib.EntropyMatrix

open Matrix

/-- The algebraic part of Section 6: compatible normalized coefficients become signed
coordinate projections after rotating both domain and range. -/
theorem signed_coordinate_coefficients {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∀ r, rotatedCoefficients X U r = diagonal (Pi.single r (σ r)) := by
  obtain ⟨U, hUU, hUtU, eig, heig⟩ :=
    simultaneous_diagonalization X hherm (coefficients_commute X hX h₂)
  refine ⟨U, hUU, hUtU, ?_⟩
  apply diagonal_coefficients_signs
  · exact rotatedCoefficients_symmetry X hX U
  · intro r i j hij
    simp only [rotatedCoefficients, linearField, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, heig, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, diagonal_apply_ne _ hij, mul_zero, Finset.sum_const_zero]
  · exact rotatedCoefficients_sum_square X U hUU hUtU hsq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Mixing the input coordinates mixes the coefficient matrices by the columns. -/
theorem linearField_mulVec (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    linearField X (U *ᵥ x) = ∑ r, x r • linearField X (fun s => U s r) := by
  simp only [linearField, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

omit [DecidableEq ι] in
/-- Rotation of the whole field agrees with rotation of its coefficients. -/
theorem rotated_linearField (X : ι → Matrix ι ι ℝ) (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    U.transpose * linearField X (U *ᵥ x) * U =
      linearField (rotatedCoefficients X U) x := by
  rw [linearField_mulVec]
  simp only [linearField, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, rotatedCoefficients]

/-- Signed coordinate coefficients have the expected diagonal linear field. -/
theorem linearField_signed_coordinates (σ x : ι → ℝ) :
    linearField (fun r => diagonal (Pi.single r (σ r))) x =
      diagonal (fun i => σ i * x i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [linearField, Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply, mul_comm]
  · simp [linearField, Matrix.sum_apply, Matrix.smul_apply, hij]

/-- Complete finite-dimensional conclusion for a normalized compatible linear matrix field. -/
theorem signed_coordinate_field {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∀ x, U.transpose * linearField X (U *ᵥ x) * U =
          diagonal (fun i => σ i * x i) := by
  obtain ⟨U, hUU, hUtU, σ, hσ, hcoeff⟩ :=
    signed_coordinate_coefficients X hherm hX h₂ hsq
  refine ⟨U, hUU, hUtU, σ, hσ, ?_⟩
  intro x
  rw [rotated_linearField, show rotatedCoefficients X U =
    (fun r => diagonal (Pi.single r (σ r))) from funext hcoeff,
    linearField_signed_coordinates]

end Submission.Lib.EntropyMatrix

namespace Submission.Lib.EntropyMatrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The square of the Frobenius norm, expressed without choosing a matrix norm instance. -/
def frobeniusSq (M : Matrix ι ι ℝ) : ℝ := (M.transpose * M).trace

omit [DecidableEq ι] in
/-- Entrywise expression for the squared Frobenius norm. -/
theorem frobeniusSq_eq_sum (M : Matrix ι ι ℝ) :
    frobeniusSq M = ∑ i, ∑ j, (M i j) ^ 2 := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, sq]
  rw [Finset.sum_comm]

/-- Independent orthogonal changes of row and column bases preserve the Frobenius norm. -/
theorem frobeniusSq_orthogonal (M U V : Matrix ι ι ℝ)
    (hU : U * U.transpose = 1) (hV : V * V.transpose = 1) :
    frobeniusSq (U.transpose * M * V) = frobeniusSq M := by
  unfold frobeniusSq
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (V.transpose * M.transpose * (U * U.transpose) * M * V).trace := by
      simp only [Matrix.mul_assoc]
    _ = (V.transpose * M.transpose * M * V).trace := by rw [hU, Matrix.mul_one]
    _ = (V * (V.transpose * M.transpose * M)).trace := Matrix.trace_mul_comm _ _
    _ = ((V * V.transpose) * (M.transpose * M)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.one_mul]

/-- Entrywise comparison after choosing the two eigenbases. -/
theorem frobeniusSq_diagonal_difference_le (a b : ι → ℝ) (W : Matrix ι ι ℝ)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    frobeniusSq (diagonal (q ∘ a) * W - W * diagonal (q ∘ b)) ≤
      frobeniusSq (diagonal a * W - W * diagonal b) := by
  rw [frobeniusSq_eq_sum, frobeniusSq_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.mul_diagonal]
  have hab : (q (a i) - q (b j)) ^ 2 ≤ (a i - b j) ^ 2 := by
    exact (sq_le_sq).2 (hq (a i) (b j))
  have hw := mul_le_mul_of_nonneg_right hab (sq_nonneg (W i j))
  dsimp only [Function.comp_apply]
  nlinarith

/-- A scalar contraction acts as a contraction on Hermitian matrices for the Frobenius norm. -/
theorem cfc_frobeniusSq_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    frobeniusSq (cfc q A - cfc q B) ≤ frobeniusSq (A - B) := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let V : Matrix ι ι ℝ := hB.eigenvectorUnitary
  have hUU : U * U.transpose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hVV : V * V.transpose = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hUtU : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hVtV : V.transpose * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have ha : A = U * diagonal hA.eigenvalues * U.transpose := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.spectral_theorem
  have hb : B = V * diagonal hB.eigenvalues * V.transpose := by
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hB.spectral_theorem
  have hqa : cfc q A = U * diagonal (q ∘ hA.eigenvalues) * U.transpose := by
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hqb : cfc q B = V * diagonal (q ∘ hB.eigenvalues) * V.transpose := by
    rw [hB.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [V, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hcross (D E : Matrix ι ι ℝ) :
      U.transpose * (U * D * U.transpose - V * E * V.transpose) * V =
        D * (U.transpose * V) - (U.transpose * V) * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc
      _ = (U.transpose * U) * D * (U.transpose * V) -
          (U.transpose * V) * E * (V.transpose * V) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUtU, hVtV, Matrix.one_mul, Matrix.mul_one]
  have hdiff : U.transpose * (A - B) * V =
      diagonal hA.eigenvalues * (U.transpose * V) -
        (U.transpose * V) * diagonal hB.eigenvalues := by
    calc
      _ = U.transpose * (U * diagonal hA.eigenvalues * U.transpose -
          V * diagonal hB.eigenvalues * V.transpose) * V :=
        congrArg (fun M => U.transpose * M * V) (congrArg₂ (· - ·) ha hb)
      _ = _ := hcross _ _
  rw [← frobeniusSq_orthogonal (cfc q A - cfc q B) U V hUU hVV,
    ← frobeniusSq_orthogonal (A - B) U V hUU hVV, hqa, hqb, hdiff, hcross]
  exact frobeniusSq_diagonal_difference_le hA.eigenvalues hB.eigenvalues
    (U.transpose * V) q hq

/-- Entry-square formulation of the Frobenius spectral contraction, as used in Section 6. -/
theorem cfc_entry_square_sum_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : ℝ → ℝ) (hq : ∀ x y, |q x - q y| ≤ |x - y|) :
    (∑ i, ∑ j, (cfc q A i j - cfc q B i j) ^ 2) ≤
      ∑ i, ∑ j, (A i j - B i j) ^ 2 := by
  simpa only [frobeniusSq_eq_sum, Matrix.sub_apply] using cfc_frobeniusSq_le hA hB q hq

end Submission.Lib.EntropyMatrix



namespace Submission.Lib.EntropyMatrix

/-- A diagonal Jacobian integrates to the coordinate primitives, up to translation.
This is the last differential step of the linear-field rigidity lemma. -/
theorem diagonal_jacobian_primitive {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (t q : ℝ → ℝ) (ht : ∀ s, HasDerivAt t (q s) s)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ^ 2 = 1)
    (hF : ∀ x, HasFDerivAt F
      ((Matrix.diagonal (fun i => q (σ i * x i))).toEuclideanLin.toContinuousLinearMap) x) :
    ∃ w : EuclideanSpace ℝ (Fin m), ∀ x i, F x i = σ i * t (σ i * x i) + w i := by
  let w : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (fun i => F 0 i - σ i * t 0)
  refine ⟨w, ?_⟩
  intro x i
  let p : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := EuclideanSpace.proj i
  have hcoord (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => F z i) (q (σ i * y i) • p) y := by
    convert! p.hasFDerivAt.comp y (hF y) using 1
    ext v
    simp [p, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  have hmodel (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => σ i * t (σ i * z i)) (q (σ i * y i) • p) y := by
    have h := ((ht (σ i * y i)).comp_hasFDerivAt y
      (p.hasFDerivAt.const_mul (σ i))).const_mul (σ i)
    convert! h using 1
    ext v
    simp only [smul_apply, smul_eq_mul]
    calc
      _ = σ i ^ 2 * (q (σ i * y i) * p v) := by rw [hσ i, one_mul]
      _ = _ := by ring
  have hz (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => F z i - σ i * t (σ i * z i))
        (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) y := by
    simpa only [sub_self, Pi.sub_apply] using! (hcoord y).sub (hmodel y)
  have hconst := is_const_of_fderiv_eq_zero
    (fun y => (hz y).differentiableAt) (fun y => (hz y).fderiv) x 0
  change F x i = σ i * t (σ i * x i) + (F 0 i - σ i * t 0)
  simp only [PiLp.zero_apply, mul_zero] at hconst
  linarith

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar functional calculus on a diagonal real matrix. -/
theorem cfc_diagonal_real (q : ℝ → ℝ) (a : ι → ℝ) :
    cfc q (diagonal a) = diagonal (q ∘ a) := by
  have hspec (i : ι) : a i ∈ spectrum ℝ (diagonal a) := by
    rw [spectrum_diagonal]
    exact Set.mem_range_self i
  let φ : C(spectrum ℝ (diagonal a), ℝ) →⋆ₐ[ℝ] Matrix ι ι ℝ :=
    { toFun := fun g => diagonal (fun i => g ⟨a i, hspec i⟩)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by intro f g; simp [Matrix.diagonal_add]
      map_mul' := by intro f g; simp [Matrix.diagonal_mul_diagonal]
      commutes' := by intro r; simp [Matrix.algebraMap_eq_diagonal]
      map_star' := by intro g; simp [Matrix.star_eq_conjTranspose] }
  have hc : Continuous φ := by
    change Continuous (fun g : C(spectrum ℝ (diagonal a), ℝ) =>
      diagonal (fun i => g ⟨a i, hspec i⟩))
    fun_prop
  have hφ : cfcHom (Matrix.isHermitian_diagonal a).isSelfAdjoint = φ :=
    cfcHom_eq_of_continuous_of_map_id _ φ hc (by rfl)
  rw [cfc_apply q (diagonal a) (Matrix.isHermitian_diagonal a).isSelfAdjoint
    ((diagonal a).finite_real_spectrum.continuousOn q), hφ]
  rfl

/-- Functional calculus commutes with orthogonal conjugation. -/
theorem cfc_orthogonal_conjugate (q : ℝ → ℝ) {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (U : Matrix ι ι ℝ) (hU : U * U.transpose = 1) :
    U * cfc q A * U.transpose = cfc q (U * A * U.transpose) := by
  let u : Matrix.unitaryGroup ι ℝ := ⟨U, by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
      using hU⟩
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u
  have hc : Continuous φ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have hφa : IsSelfAdjoint (φ A) := hA.isSelfAdjoint.map φ
  have h := StarAlgHomClass.map_cfc φ q A
    (A.finite_real_spectrum.continuousOn q) hc hA.isSelfAdjoint hφa
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- A diagonalized matrix has diagonalized scalar functional calculus in the same basis. -/
theorem cfc_of_orthogonal_diagonalization (q : ℝ → ℝ)
    {A U : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hU : U.transpose * U = 1) {a : ι → ℝ}
    (hdiag : U.transpose * A * U = diagonal a) :
    U.transpose * cfc q A * U = diagonal (q ∘ a) := by
  have h := cfc_orthogonal_conjugate q hA U.transpose (by simpa using hU)
  simpa only [Matrix.transpose_transpose, hdiag, cfc_diagonal_real] using h

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open Matrix

/-- Integrating a compatible linear-field spectral Jacobian after an orthogonal rotation. -/
theorem linear_field_jacobian_primitive {m : ℕ}
    (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hherm : ∀ r, (X r).IsHermitian)
    (hX : CoefficientSymmetry X)
    (h₂ : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hsq : ∑ r, X r * X r = 1)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (t q : ℝ → ℝ) (ht : ∀ s, HasDerivAt t (q s) s)
    (hF : ∀ x : EuclideanSpace ℝ (Fin m), HasFDerivAt F
      ((cfc q (linearField X x)).toEuclideanLin.toContinuousLinearMap) x) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
      U * U.transpose = 1 ∧ U.transpose * U = 1 ∧
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∃ w : EuclideanSpace ℝ (Fin m), ∀ x i,
          (U.transpose.toEuclideanLin (F (U.toEuclideanLin x))) i =
            σ i * t (σ i * x i) + w i := by
  obtain ⟨U, hUU, hUtU, σ, hσ, hfield⟩ :=
    signed_coordinate_field X hherm hX h₂ hsq
  let V := U.toEuclideanLin.toContinuousLinearMap
  let W := U.transpose.toEuclideanLin.toContinuousLinearMap
  let G := fun x => W (F (V x))
  have hG (x : EuclideanSpace ℝ (Fin m)) : HasFDerivAt G
      ((diagonal (fun i => q (σ i * x i))).toEuclideanLin.toContinuousLinearMap) x := by
    have h := (W.hasFDerivAt.comp (V x) (hF (V x))).comp x V.hasFDerivAt
    have hHerm : (linearField X (V x)).IsHermitian := by
      unfold linearField
      change (∑ r, (V x) r • X r).conjTranspose = ∑ r, (V x) r • X r
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
        (hherm _).eq]
    have hd := cfc_of_orthogonal_diagonalization q hHerm hUtU
      (hfield (fun i => x i))
    convert! h using 1
    ext v i
    have heq := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => (M *ᵥ v) i) hd
    simpa only [V, W, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Function.comp_def] using heq.symm
  obtain ⟨w, hw⟩ := diagonal_jacobian_primitive G t q ht σ
    (fun i => by rcases hσ i with h | h <;> simp [h]) hG
  exact ⟨U, hUU, hUtU, σ, hσ, w, hw⟩

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open Matrix Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The trace of the coefficient square sum is the sum of entry squares. -/
theorem trace_square_sum (X : ι → Matrix ι ι ℝ) (hX : ∀ r, (X r).IsHermitian) :
    (∑ r, X r * X r).trace = ∑ r, ∑ i, ∑ j, (X r i j) ^ 2 := by
  rw [Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : X r j i = X r i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun (hX r).eq i) j
  rw [h, sq]

omit [DecidableEq ι] in
/-- Bounded entry-square sums give a convergent subsequence of all coefficients together. -/
theorem coefficient_subsequence_of_square_bound
    (X : ℕ → ι → Matrix ι ι ℝ) (C : ℝ)
    (hbound : ∀ n, (∑ r, ∑ i, ∑ j, (X n r i j) ^ 2) ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  let v : ℕ → EuclideanSpace ℝ (ι × ι × ι) :=
    fun n => WithLp.toLp 2 (fun p => X n p.1 p.2.1 p.2.2)
  have hv (n : ℕ) : v n ∈ Metric.closedBall 0 (Real.sqrt C) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖v n‖ = Real.sqrt (‖v n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt (by
        simpa only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, v,
          WithLp.ofLp_toLp] using hbound n)
  obtain ⟨y, _, s, hs, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (ι × ι × ι)))
      (r := Real.sqrt C)) hv
  refine ⟨s, hs, fun r i j => y (r, i, j), ?_⟩
  intro r i j
  exact (EuclideanSpace.proj (r, i, j)).continuous.continuousAt.tendsto.comp hlim

omit [DecidableEq ι] in
/-- A bounded trace of the sum of squares suffices for Hermitian coefficient compactness. -/
theorem hermitian_coefficient_subsequence
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (C : ℝ) (hbound : ∀ n, (∑ r, X n r * X n r).trace ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  apply coefficient_subsequence_of_square_bound X C
  intro n
  simpa only [trace_square_sum _ (hX n)] using hbound n

/-- If the square sum tends to the identity, a subsequence converges to normalized
Hermitian coefficients. This is the finite-dimensional compactness step of Section 6. -/
theorem normalized_coefficient_subsequence
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (hB : ∀ i j, Tendsto (fun n => (∑ r, X n r * X n r) i j) atTop
      (𝓝 ((1 : Matrix ι ι ℝ) i j))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      (∀ r, (Y r).IsHermitian) ∧ (∑ r, Y r * Y r = 1) ∧
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) := by
  have ht : Tendsto (fun n => (∑ r, X n r * X n r).trace) atTop
      (𝓝 ((1 : Matrix ι ι ℝ).trace)) := by
    exact tendsto_finsetSum _ (fun i _ => hB i i)
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  obtain ⟨s, hs, Y, hY⟩ := hermitian_coefficient_subsequence X hX C
    (fun n => hC (Set.mem_range_self n))
  have hsym (n : ℕ) (r i j : ι) : X n r j i = X n r i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrFun (congrFun (hX n r).eq i) j
  refine ⟨s, hs, Y, ?_, ?_, hY⟩
  · intro r
    ext i j
    change star (Y r j i) = Y r i j
    simp only [star_trivial]
    exact tendsto_nhds_unique (hY r j i) (by simpa only [hsym] using hY r i j)
  · ext i j
    have hlim := (hB i j).comp hs.tendsto_atTop
    have hprod : Tendsto (fun n => ∑ r, ∑ k, X (s n) r i k * X (s n) r k j) atTop
        (𝓝 (∑ r, ∑ k, Y r i k * Y r k j)) := by
      apply tendsto_finsetSum
      intro r _
      apply tendsto_finsetSum
      intro k _
      exact (hY r i k).mul (hY r k j)
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    exact tendsto_nhds_unique hprod (by
      simpa only [Matrix.sum_apply, Matrix.mul_apply, Function.comp_def] using! hlim)

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open Submission.Lib.EntropyTools

/-- The cutoff in the strict remainder is uniformly positive on a bounded interval. -/
theorem rigidityCutoff_ge_tenth {a : ℝ} (ha : 0 ≤ a) (ha100 : a ≤ 100) :
    (1 : ℝ) / 10 ≤ rigidityCutoff a := by
  unfold rigidityCutoff
  split_ifs with h
  · norm_num
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (lt_of_le_of_ne ha (Ne.symm h))
    have hs10 : Real.sqrt a ≤ 10 := by
      nlinarith [Real.sq_sqrt ha]
    apply le_min (by norm_num)
    apply (le_div_iff₀ (by positivity : 0 < 25 * Real.sqrt a)).mpr
    nlinarith

/-- On a fixed bounded interval, the remainder controls squared distance from one. -/
theorem rigidityWeight_controls_square {a : ℝ} (ha : 0 ≤ a) (ha100 : a ≤ 100) :
    (a - 1) ^ 2 ≤ 10000 * rigidityWeight a := by
  have hd : 0 < 37 + 3 * a := by positivity
  have hfirst : 3 / 337 * (a - 1) ^ 2 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (a - 1), mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ 100 - a by linarith)]
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by
    exact le_add_of_nonneg_right (by positivity)
  have hcut := rigidityCutoff_ge_tenth ha ha100
  have h := mul_le_mul
    (mul_le_mul hfirst hsecond (by positivity) (by positivity)) hcut
    (by positivity) (by positivity)
  unfold rigidityWeight
  nlinarith [sq_nonneg (a - 1)]

/-- A coefficient far out on the positive axis has a fixed positive remainder. -/
theorem rigidityWeight_ge_half {a : ℝ} (ha : 100 ≤ a) :
    (1 : ℝ) / 2 ≤ rigidityWeight a := by
  have ha0 : 0 < a := by linarith
  have hd : 0 < 37 + 3 * a := by positivity
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hs10 : 10 ≤ Real.sqrt a := by nlinarith [Real.sq_sqrt ha0.le]
  have hfirst : a / 2 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ a - 100 by linarith) (show 0 ≤ a by linarith)]
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a)) := by
    exact le_add_of_nonneg_right (by positivity)
  have hcut : (Real.sqrt a)⁻¹ ≤ rigidityCutoff a := by
    unfold rigidityCutoff
    rw [if_neg ha0.ne']
    apply le_min
    · rw [inv_eq_one_div]
      exact (div_le_iff₀ hs).mpr (by nlinarith)
    · rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hs (by positivity : 0 < 25 * Real.sqrt a)).mpr
      nlinarith
  have h := mul_le_mul
    (mul_le_mul hfirst hsecond (by positivity) (by positivity)) hcut
    (by positivity) (by positivity)
  have hsmall : (1 : ℝ) / 2 ≤ (a / 2 * (3 / 20)) * (Real.sqrt a)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hs).mpr
    nlinarith [Real.sq_sqrt ha0.le,
      mul_nonneg (show 0 ≤ Real.sqrt a - 10 by linarith) (show 0 ≤ Real.sqrt a by positivity)]
  exact hsmall.trans h

/-- Vanishing strict remainder forces each nonnegative scalar parameter to one. -/
theorem tendsto_one_of_rigidityWeight {α : Type*} {l : Filter α}
    (u : α → ℝ) (hu : ∀ n, 0 ≤ u n)
    (h : Filter.Tendsto (fun n => rigidityWeight (u n)) l (nhds 0)) :
    Filter.Tendsto u l (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := h.eventually (gt_mem_nhds
    (show (0 : ℝ) < min (1 / 2) (ε ^ 2 / 10000) by positivity))
  filter_upwards [hsmall] with n hn
  have hwsmall : rigidityWeight (u n) < 1 / 2 := (lt_min_iff.mp hn).1
  have hu100 : u n ≤ 100 := by
    by_contra hn100
    have := rigidityWeight_ge_half (le_of_lt (lt_of_not_ge hn100))
    linarith
  have hcontrol := rigidityWeight_controls_square (hu n) hu100
  have hsmall' := (lt_min_iff.mp hn).2
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- When a finite sum of the nonnegative weights vanishes, every parameter tends to one. -/
theorem tendsto_one_of_sum_rigidityWeight {α ι : Type*} [Fintype ι]
    {l : Filter α} (u : α → ι → ℝ) (hu : ∀ n i, 0 ≤ u n i)
    (h : Filter.Tendsto (fun n => ∑ i, rigidityWeight (u n i)) l (nhds 0))
    (i : ι) : Filter.Tendsto (fun n => u n i) l (nhds 1) := by
  apply tendsto_one_of_rigidityWeight _ (fun n => hu n i)
  apply squeeze_zero (fun n => rigidityWeight_nonneg (hu n i)) _ h
  intro n
  exact Finset.single_le_sum (fun j _ => rigidityWeight_nonneg (hu n j)) (Finset.mem_univ i)

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open Matrix Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distance from the identity is the sum of squared eigenvalue deviations. -/
theorem frobeniusSq_sub_one {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    frobeniusSq (A - 1) = ∑ i, (hA.eigenvalues i - 1) ^ 2 := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hUU : U * U.transpose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hUtU : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hdiag : U.transpose * A * U = diagonal hA.eigenvalues := by
    simpa [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag' : U.transpose * (A - 1) * U = diagonal (fun i => hA.eigenvalues i - 1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag, Matrix.mul_one, hUtU]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.sub_apply, hij]
  rw [← frobeniusSq_orthogonal (A - 1) U U hUU hUU, hdiag', frobeniusSq_eq_sum]
  simp [Matrix.diagonal_apply]

/-- Eigenvalues converging to one force every matrix entry to converge to the identity,
without requiring convergence of eigenbases. -/
theorem hermitian_tendsto_one_of_eigenvalues {α : Type*} {l : Filter α}
    (A : α → Matrix ι ι ℝ) (hA : ∀ n, (A n).IsHermitian)
    (heig : ∀ i, Tendsto (fun n => (hA n).eigenvalues i) l (𝓝 1)) :
    ∀ i j, Tendsto (fun n => A n i j) l (𝓝 ((1 : Matrix ι ι ℝ) i j)) := by
  have hsq : Tendsto (fun n => frobeniusSq (A n - 1)) l (𝓝 0) := by
    simp_rw [frobeniusSq_sub_one (hA _)]
    simpa using tendsto_finsetSum Finset.univ (fun i _ => ((heig i).sub (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1))).pow 2)
  intro i j
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := hsq.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [hsmall] with n hn
  have hbound : (A n i j - (1 : Matrix ι ι ℝ) i j) ^ 2 ≤ frobeniusSq (A n - 1) := by
    rw [frobeniusSq_eq_sum]
    exact (Finset.single_le_sum (fun k _ => sq_nonneg ((A n - 1) i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun t _ => sq_nonneg ((A n - 1) k t)))
        (Finset.mem_univ i))
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Vanishing rigidity weights imply convergence of a positive semidefinite matrix to identity. -/
theorem posSemidef_tendsto_one_of_weight {α : Type*} {l : Filter α}
    (A : α → Matrix ι ι ℝ) (hA : ∀ n, (A n).PosSemidef)
    (hweight : Tendsto (fun n => ∑ i,
      Submission.Lib.EntropyTools.rigidityWeight ((hA n).isHermitian.eigenvalues i)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun n => A n i j) l (𝓝 ((1 : Matrix ι ι ℝ) i j)) := by
  apply hermitian_tendsto_one_of_eigenvalues A (fun n => (hA n).isHermitian)
  exact tendsto_one_of_sum_rigidityWeight _ (fun n i => (hA n).eigenvalues_nonneg i) hweight

/-- The complete coefficient extraction from vanishing eigenvalue slack in Section 6. -/
theorem coefficient_subsequence_of_vanishing_weight
    (X : ℕ → ι → Matrix ι ι ℝ) (hX : ∀ n r, (X n r).IsHermitian)
    (hB : ∀ n, (∑ r, X n r * X n r).PosSemidef)
    (hweight : Tendsto (fun n => ∑ i,
      Submission.Lib.EntropyTools.rigidityWeight ((hB n).isHermitian.eigenvalues i)) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ Y : ι → Matrix ι ι ℝ,
      (∀ r, (Y r).IsHermitian) ∧ (∑ r, Y r * Y r = 1) ∧
      ∀ r i j, Tendsto (fun n => X (s n) r i j) atTop (𝓝 (Y r i j)) :=
  normalized_coefficient_subsequence X hX
    (posSemidef_tendsto_one_of_weight _ hB hweight)

end Submission.Lib.EntropyMatrix


namespace Submission.Lib.EntropyMatrix

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Gaussian orthogonality expressed for a scalar linear form. -/
theorem gaussian_linear_form_square (a : ι → ℝ) :
    (∫ x : EuclideanSpace ℝ ι, (∑ i, x i * a i) ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ∑ i, (a i) ^ 2 := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  let L := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) v
  have hL : ∀ x, L x = ∑ i, x i * a i := by
    intro x
    simp [L, v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.aemeasurable, integral_strongDual_stdGaussian,
    show ‖L‖ = ‖v‖ from (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).norm_map v,
    EuclideanSpace.real_norm_sq_eq] at h
  simpa only [hL, sub_zero] using h

/-- Every scalar entry of a linear matrix field is square integrable for Gaussian measure. -/
theorem gaussian_linear_form_square_integrable (a : ι → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => (∑ i, x i * a i) ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  let L := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) v
  simpa [L, v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using
    (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ ι)) L 2 (by norm_num)).integrable_sq

/-- Gaussian orthogonality identifies the L2 size of a linear matrix field with its coefficients. -/
theorem gaussian_linear_field_square (X : ι → Matrix ι ι ℝ) :
    (∫ x : EuclideanSpace ℝ ι, (∑ i, ∑ j, (linearField X x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∑ i, ∑ j, ∑ r, (X r i j) ^ 2 := by
  simp only [linearField, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => gaussian_linear_form_square_integrable (fun r => X r i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => gaussian_linear_form_square_integrable (fun r => X r i j))]
  simp_rw [gaussian_linear_form_square]

/-- The same identity for differences of linear fields. -/
theorem gaussian_linear_field_sub_square (X Y : ι → Matrix ι ι ℝ) :
    (∫ x : EuclideanSpace ℝ ι,
      (∑ i, ∑ j, (linearField X x i j - linearField Y x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∑ i, ∑ j, ∑ r, (X r i j - Y r i j) ^ 2 := by
  simpa only [linearField, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib] using
    gaussian_linear_field_square (fun r => X r - Y r)

/-- Coefficient convergence gives Gaussian L2 convergence of the linear matrix fields. -/
theorem gaussian_linear_field_L2_tendsto {α : Type*} {l : Filter α}
    (X : α → ι → Matrix ι ι ℝ) (Y : ι → Matrix ι ι ℝ)
    (hX : ∀ r i j, Filter.Tendsto (fun n => X n r i j) l (nhds (Y r i j))) :
    Filter.Tendsto (fun n => ∫ x : EuclideanSpace ℝ ι,
      (∑ i, ∑ j, (linearField (X n) x i j - linearField Y x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) l (nhds 0) := by
  simp_rw [gaussian_linear_field_sub_square]
  have h (r i j : ι) : Filter.Tendsto (fun n => (X n r i j - Y r i j) ^ 2) l (nhds 0) := by
    simpa using ((hX r i j).sub_const (Y r i j)).pow 2
  simpa using tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      tendsto_finsetSum Finset.univ (fun r _ => h r i j)))

end Submission.Lib.EntropyMatrix
