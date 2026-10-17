import Mathlib

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
