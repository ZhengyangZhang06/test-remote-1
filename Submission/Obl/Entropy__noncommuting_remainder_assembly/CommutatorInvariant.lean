import Submission.Obl.Entropy__noncommuting_remainder_assembly.Commutator

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ι]

omit [DecidableEq ι] in
lemma starAlgEquiv_transpose (φ : Matrix ι ι ℝ ≃⋆ₐ[ℝ] Matrix ι ι ℝ)
    (A : Matrix ι ι ℝ) : φ A.transpose = (φ A).transpose := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using map_star φ A

lemma trace_unitary_conj (U : unitary (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    Matrix.trace (Unitary.conjStarAlgAut ℝ _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]

lemma squareSum_unitary_conj (U : unitary (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    squareSum (Unitary.conjStarAlgAut ℝ _ U A) = squareSum A := by
  rw [squareSum_trace, squareSum_trace, ← starAlgEquiv_transpose, ← map_mul,
    trace_unitary_conj]

/-- A right inverse relation determines the Gram matrix in an eigenbasis of `S`. -/
lemma diagonal_gram_of_inverse (φ : Matrix ι ι ℝ ≃⋆ₐ[ℝ] Matrix ι ι ℝ)
    (B S : Matrix ι ι ℝ) {s α : ℝ} (hs : 0 < s) (hα : 0 < α)
    (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (hS : φ S = Matrix.diagonal e)
    (hinv : (s⁻¹ • (1 : Matrix ι ι ℝ) + α • B) * S = 1) :
    φ B = Matrix.diagonal (fun i => (1 - e i / s) / (α * s * (e i / s))) := by
  have hprod := congrArg φ hinv
  simp only [map_mul, map_add, map_smul, map_one, hS] at hprod
  ext i j
  have hentry := congrFun (congrFun hprod i) j
  simp only [Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq] at hentry
    simp only [Matrix.diagonal_apply_eq]
    have hs0 := ne_of_gt hs
    have hα0 := ne_of_gt hα
    have he0 := ne_of_gt (he i)
    apply (eq_div_iff (by positivity : α * s * (e i / s) ≠ 0)).2
    rw [show α * s * (e i / s) = α * e i by field_simp]
    simp only [mul_one] at hentry
    have heq : s⁻¹ * e i = e i / s := by ring
    rw [add_mul, heq] at hentry
    nlinarith
  · simp only [Matrix.one_apply_ne hij, mul_zero, zero_add] at hentry
    simp only [Matrix.diagonal_apply_ne _ hij]
    exact (mul_eq_zero.mp (mul_eq_zero.mp hentry |>.resolve_right (ne_of_gt (he j)))).resolve_left
      (ne_of_gt hα)

/-- The compensated commutator estimate, with no commutation hypothesis on `b`. -/
lemma commutator_bound (X W : ν → Matrix ι ι ℝ) (b S : Matrix ι ι ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (hS : S.PosDef) (hb : b.transpose = b)
    (hinv : (s⁻¹ • (1 : Matrix ι ι ℝ) + α • (∑ r, X r * (X r).transpose)) * S = 1) :
    let B := ∑ r, X r * (X r).transpose;
    let T := S - 1;
    -Matrix.trace (T * b * B * b - T * B * b * b) -
      2 * Matrix.trace ((T * b - b * T) * (∑ r, X r * W r)) -
      Matrix.trace (T * (∑ r, (W r).transpose * W r)) ≤
        (1 + s / 8) * (∑ r, squareSum (W r)) := by
  let U := star hS.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  let e := hS.isHermitian.eigenvalues
  let u := fun i => e i / s
  let B := ∑ r, X r * (X r).transpose
  have he (i : ι) : 0 < e i := hS.eigenvalues_pos i
  have hu (i : ι) : 0 < u i := div_pos (he i) hs
  have hdiag : φ S = Matrix.diagonal e := by
    simpa [φ, U, e, Function.comp_def] using hS.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hB : φ B = Matrix.diagonal (fun i => (1 - u i) / (α * s * u i)) :=
    diagonal_gram_of_inverse φ B S hs hα e he hdiag hinv
  have hX : (∑ r, φ (X r) * (φ (X r)).transpose) =
      Matrix.diagonal (fun i => (1 - u i) / (α * s * u i)) := by
    rw [← hB]
    simp only [B, map_sum, map_mul, starAlgEquiv_transpose]
  have hT : φ (S - 1) = Matrix.diagonal (fun i => s * u i - 1) := by
    rw [map_sub, map_one, hdiag, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    congr 1
    funext i
    simp [u, mul_div_cancel₀ _ (ne_of_gt hs)]
  have hb' : (φ b).transpose = φ b := by rw [← starAlgEquiv_transpose, hb]
  have h := resolvent_commutator_diagonal (fun r => φ (X r)) (φ b) (fun r => φ (W r))
    hs hα u hu hb' hX
  dsimp only at h
  rw [← hT, ← hB] at h
  have htr (A : Matrix ι ι ℝ) : Matrix.trace (φ A) = Matrix.trace A := trace_unitary_conj U A
  have hsq (A : Matrix ι ι ℝ) : squareSum (φ A) = squareSum A := squareSum_unitary_conj U A
  simp only [hsq, ← starAlgEquiv_transpose, ← map_mul, ← map_sum, ← map_sub, htr] at h
  exact h

/-- The paper's fixed constants, with positivity discharged from the Gram structure. -/
lemma commutator_bound_constants (X W : ν → Matrix ι ι ℝ) (b : Matrix ι ι ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hb : b.IsHermitian) :
    let B := ∑ r, X r * X r;
    let S := ((37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B)⁻¹;
    let T := S - 1;
    -Matrix.trace (T * b * B * b - T * B * b * b) -
      2 * Matrix.trace ((T * b - b * T) * (∑ r, X r * W r)) -
      Matrix.trace (T * (∑ r, (W r).transpose * W r)) ≤
        (42 / 37 : ℝ) * (∑ r, ∑ i, ∑ j, (W r i j) ^ 2) := by
  have hXs (r : ν) : (X r).transpose = X r := by simpa using (hX r).eq
  have hbs : b.transpose = b := by simpa using hb.eq
  let B := ∑ r, X r * (X r).transpose
  let M := (37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B
  have hB : B.PosSemidef := Matrix.posSemidef_sum _ fun r _ => by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (X r)
  have hM : M.PosDef := (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 37 / 40)).add_posSemidef
    (hB.smul (by norm_num : (0 : ℝ) ≤ 3 / 40))
  have hInv : ((40 / 37 : ℝ)⁻¹ • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B) * M⁻¹ = 1 := by
    norm_num
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hM.isUnit)
  have h := commutator_bound X W b M⁻¹ (s := 40 / 37) (α := 3 / 40)
    (by norm_num) (by norm_num) hM.inv hbs hInv
  norm_num only [show (1 : ℝ) + (40 / 37) / 8 = 42 / 37 by norm_num] at h
  simpa only [M, B, hXs, squareSum] using h


end Submission.Obl.Entropy__noncommuting_remainder_assembly
