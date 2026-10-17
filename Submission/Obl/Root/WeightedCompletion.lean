import Submission.Obl.Root.MatrixSquares

open scoped BigOperators MatrixOrder

namespace Submission.Obl.Root

/-- Two positive semidefinite matrices have nonnegative trace pairing. -/
lemma trace_mul_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let R := CFC.sqrt B
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h := (hA.mul_mul_conjTranspose_same R).trace_nonneg
  rw [hR.isHermitian.eq, Matrix.trace_mul_cycle] at h
  rw [Matrix.trace_mul_comm A B]
  simpa [Matrix.mul_assoc, hRR] using h

/-- Weighted completion with unrelated positive weights on the row and column spaces. -/
theorem matrix_weighted_completion {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι κ ℝ) {K : Matrix ι ι ℝ} {P : Matrix κ κ ℝ}
    (hK : K.PosDef) (hP : P.PosDef) :
    (A.transpose * B).trace ≤ (A.transpose * K⁻¹ * A * P).trace +
      (1 / 4) * (B.transpose * K * B * P⁻¹).trace := by
  have hKsym : K.transpose = K := by simpa using hK.isHermitian.eq
  have hPsym : P⁻¹.transpose = P⁻¹ := by simpa using hP.inv.isHermitian.eq
  have hKi : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K
    ((Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit)
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P
    ((Matrix.isUnit_iff_isUnit_det P).1 hP.isUnit)
  let Z := A - (1 / 2 : ℝ) • (K * B * P⁻¹)
  have hZ : (Z.transpose * K⁻¹ * Z).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hK.inv.posSemidef.conjTranspose_mul_mul_same Z
  have hn := trace_mul_nonneg_of_posSemidef hZ hP.posSemidef
  have h1 : (A.transpose * K⁻¹ * (K * B * P⁻¹) * P).trace =
      (A.transpose * B).trace := by
    have he : A.transpose * K⁻¹ * (K * B * P⁻¹) * P =
        A.transpose * (K⁻¹ * K) * B * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [he, hKi, hPi, Matrix.mul_one, Matrix.mul_one]
  have h2 : ((K * B * P⁻¹).transpose * K⁻¹ * A * P).trace =
      (A.transpose * B).trace := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hKsym, hPsym]
    have he : P⁻¹ * (B.transpose * K) * K⁻¹ * A * P =
        P⁻¹ * B.transpose * (K * K⁻¹) * A * P := by simp only [Matrix.mul_assoc]
    rw [he, Matrix.mul_nonsing_inv K ((Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit),
      Matrix.mul_one, Matrix.trace_mul_cycle]
    have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P
      ((Matrix.isUnit_iff_isUnit_det P).1 hP.isUnit)
    simp only [← Matrix.mul_assoc, hPi', Matrix.one_mul]
    rw [← Matrix.trace_transpose (B.transpose * A), Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have h3 : ((K * B * P⁻¹).transpose * K⁻¹ * (K * B * P⁻¹) * P).trace =
      (B.transpose * K * B * P⁻¹).trace := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hKsym, hPsym]
    have he : P⁻¹ * (B.transpose * K) * K⁻¹ * (K * B * P⁻¹) * P =
        P⁻¹ * B.transpose * K * (K⁻¹ * K) * B * (P⁻¹ * P) := by
      simp only [Matrix.mul_assoc]
    rw [he, hKi, hPi, Matrix.mul_one, Matrix.mul_one]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm P⁻¹ (B.transpose * K * B)
  dsimp [Z] at hn
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hn
  rw [h1, h2, h3] at hn
  linarith

lemma trace_right_sqrt {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (S : Matrix ι ι ℝ) {P : Matrix κ κ ℝ}
    (hP : P.PosSemidef) :
    ((A * CFC.sqrt P).transpose * S * (A * CFC.sqrt P)).trace =
      (A.transpose * S * A * P).trace := by
  let R := CFC.sqrt P
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hs : R.transpose = R := by simpa using hR.isHermitian.eq
  have hRR : R * R = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  change ((A * R).transpose * S * (A * R)).trace = _
  calc
    _ = (R * (A.transpose * S * A) * R).trace := by
      rw [Matrix.transpose_mul, hs]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]

/-- The block estimate with an arbitrary positive right-hand matrix weight. -/
theorem matrix_block_bound_right_weight {ρ ι ν : Type*} [Fintype ρ] [Fintype ι]
    [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (X : ρ → Matrix ι ι ℝ) (L : ρ → Matrix ι ν ℝ) (a : Matrix ι ν ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (S : Matrix ι ι ℝ)
    (hS : S.PosDef) {P : Matrix ν ν ℝ} (hP : P.PosSemidef)
    (hinv : S⁻¹ = s⁻¹ • (1 : Matrix ι ι ℝ) +
      α • ∑ r, X r * (X r).transpose) :
    let F := a + ∑ r, X r * L r
    (F.transpose * S * F * P).trace ≤
      s * (a.transpose * a * P).trace +
        α⁻¹ * ∑ r, ((L r).transpose * L r * P).trace := by
  classical
  let R := CFC.sqrt P
  have h := matrix_block_bound_add X (fun r => L r * R) (a * R) hs hα S hS hinv
  have he : a * R + ∑ r, X r * (L r * R) = (a + ∑ r, X r * L r) * R := by
    simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc]
  dsimp only at h
  rw [he] at h
  rw [trace_right_sqrt _ S hP] at h
  have hn (M : Matrix ι ν ℝ) : ((M * R).transpose * (M * R)).trace =
      (M.transpose * M * P).trace := by
    simpa only [Matrix.mul_one] using trace_right_sqrt M 1 hP
  simpa only [hn] using h

/-- Completion of the noncommuting weighted term, followed by block Cauchy--Schwarz.

The positive weight on the column space need not commute with any other matrix.
The term `T * K⁻¹ * T` can be singular; no inverse of it is used.
-/
theorem matrix_weighted_block_completion {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι]
    (X L : ρ → Matrix ι ι ℝ) (a T : Matrix ι ι ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α)
    {K P : Matrix ι ι ℝ} (hK : K.PosDef) (hP : P.PosDef) (hT : T.IsHermitian)
    (hinv : K⁻¹ = s⁻¹ • (1 : Matrix ι ι ℝ) +
      α • ∑ r, X r * (X r).transpose) :
    (T * (a + ∑ r, X r * L r)).trace ≤
      (T * K⁻¹ * T * P).trace +
      (s / 4) * (a.transpose * a * P⁻¹).trace +
      (1 / (4 * α)) * ∑ r, ((L r).transpose * L r * P⁻¹).trace := by
  have hTs : T.transpose = T := by simpa using hT.eq
  have hc := matrix_weighted_completion T (a + ∑ r, X r * L r) hK hP
  rw [hTs] at hc
  have hb := matrix_block_bound_right_weight X L a hs hα K hK hP.inv.posSemidef hinv
  have he : (1 : ℝ) / (4 * α) = α⁻¹ / 4 := by ring
  rw [he]
  linarith

/-- Section 3's weighted completion, retaining the exact `H (I - rho)` reserve.

Here `rho = ε I + (κ/s) S`. Only `T` and `S` must commute; the positive
matrix `P` may fail to commute with either of them.
-/
theorem entropy_weighted_completion {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι] (X L : ρ → Matrix ι ι ℝ) (a T H S P : Matrix ι ι ℝ)
    {s α ε κ : ℝ} (hs : 0 < s) (hα : 0 < α) (hε : 0 < 1 - ε)
    (hεκ : 0 < 1 - ε - κ) (hS : S.PosDef) (hP : P.PosDef)
    (hT : T.IsHermitian) (hTS : Commute T S)
    (hinv : S⁻¹ = s⁻¹ • (1 : Matrix ι ι ℝ) + α • ∑ r, X r * (X r).transpose)
    (hT2 : T * T = α • (H * S)) :
    (T * (a + ∑ r, X r * L r)).trace ≤
      (H * ((1 - ε) • (1 : Matrix ι ι ℝ) - (κ / s) • S) * P).trace +
      (α * s / (4 * (1 - ε - κ))) * (a.transpose * a * P⁻¹).trace +
      (1 / (4 * (1 - ε))) * ∑ r, ((L r).transpose * L r * P⁻¹).trace := by
  classical
  let B := ∑ r, X r * (X r).transpose
  have hB : B.PosSemidef := Matrix.posSemidef_sum _ fun r _ => by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (X r)
  let δ := (1 - ε - κ) / (α * s)
  have hδ : 0 < δ := div_pos hεκ (mul_pos hα hs)
  let D := δ • (1 : Matrix ι ι ℝ) + (1 - ε) • B
  have hD : D.PosDef := (Matrix.PosDef.one.smul hδ).add_posSemidef (hB.smul hε.le)
  let K := D⁻¹
  have hK : K.PosDef := hD.inv
  have hKinv : K⁻¹ = D := Matrix.nonsing_inv_nonsing_inv D
    ((Matrix.isUnit_iff_isUnit_det D).1 hD.isUnit)
  have hDexpr : D = α⁻¹ • ((1 - ε) • S⁻¹ - (κ / s) • (1 : Matrix ι ι ℝ)) := by
    rw [hinv]
    ext i j
    simp only [D, δ, B, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hSleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit)
  have hSright : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit)
  have hTSi : S⁻¹ * T = T * S⁻¹ := by
    calc
      _ = S⁻¹ * T * (S * S⁻¹) := by rw [hSright, mul_one]
      _ = S⁻¹ * (T * S) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (S * T) * S⁻¹ := by rw [hTS.eq]
      _ = _ := by simp only [← Matrix.mul_assoc, hSleft, one_mul]
  have hTinv : T * S⁻¹ * T = α • H := by
    rw [Matrix.mul_assoc, hTSi, ← Matrix.mul_assoc, hT2, Matrix.smul_mul,
      Matrix.mul_assoc, hSright, Matrix.mul_one]
  have hTD : T * D * T = H * ((1 - ε) • (1 : Matrix ι ι ℝ) - (κ / s) • S) := by
    rw [hDexpr]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hTinv, hT2, smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  have hnew : K⁻¹ = (α * s / (1 - ε - κ))⁻¹ • (1 : Matrix ι ι ℝ) +
      (1 - ε) • ∑ r, X r * (X r).transpose := by
    rw [hKinv]
    simp [D, δ, B, div_eq_mul_inv, mul_comm]
  have h := matrix_weighted_block_completion X L a T
    (div_pos (mul_pos hα hs) hεκ) hε hK hP hT hnew
  rw [hKinv, hTD] at h
  simpa only [div_div, mul_comm (1 - ε - κ) 4] using h

end Submission.Obl.Root
