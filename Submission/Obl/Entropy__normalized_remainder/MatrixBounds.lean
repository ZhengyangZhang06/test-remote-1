import Submission.Obl.Entropy__normalized_remainder.FirstChaos

/-!
# Matrix bounds in Section 3

The supporting plane for the log determinant and the regularized inverse
chosen from the first Gaussian chaos.
-/

namespace Submission.Obl.Entropy__normalized_remainder

open scoped BigOperators MatrixOrder

/-- The scalar inequality `log x ≤ x - 1`, summed over the spectrum. -/
theorem log_det_le_trace_sub_dim {m : ℕ} {C : Mat m} (hC : C.PosDef) :
    Real.log C.det ≤ Matrix.trace C - (m : ℝ) := by
  rw [hC.isHermitian.det_eq_prod_eigenvalues,
    hC.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hC.eigenvalues_pos i).ne')]
  calc
    ∑ i, Real.log (hC.isHermitian.eigenvalues i) ≤
        ∑ i, (hC.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hC.eigenvalues_pos i)
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- The log-determinant supporting plane used in the deficit reduction. -/
theorem log_det_supporting_plane {m : ℕ} {C S : Mat m}
    (hC : C.PosDef) (hS : S.PosDef) :
    Real.log C.det + (m : ℝ) ≤ Matrix.trace (S * C) - Real.log S.det := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRu : IsUnit R := (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
  have hRCR : (R * C * R).PosDef := by
    simpa only [hR.eq] using
      hC.conjTranspose_mul_mul_same (B := R) (Matrix.mulVec_injective_iff_isUnit.mpr hRu)
  have hdet : (R * C * R).det = S.det * C.det := by
    calc
      (R * C * R).det = (R * R).det * C.det := by simp only [Matrix.det_mul]; ring
      _ = _ := by rw [hRR]
  have htrace : Matrix.trace (R * C * R) = Matrix.trace (S * C) := by
    rw [Matrix.trace_mul_cycle, hRR]
  have h := log_det_le_trace_sub_dim hRCR
  rw [hdet, htrace, Real.log_mul hS.det_pos.ne' hC.det_pos.ne'] at h
  linarith

/-- `I/s + αB` with the paper's exact constants. -/
noncomputable def dualDenom {m : ℕ} (B : Mat m) : Mat m :=
  (37 / 40 : ℝ) • 1 + (3 / 40 : ℝ) • B

noncomputable def dualS {m : ℕ} (B : Mat m) : Mat m := (dualDenom B)⁻¹
noncomputable def dualT {m : ℕ} (B : Mat m) : Mat m := dualS B - 1
noncomputable def dualH {m : ℕ} (B : Mat m) : Mat m := -(dualT B * (B - 1))
noncomputable def dualRho {m : ℕ} (B : Mat m) : Mat m :=
  (3 / 20 : ℝ) • 1 + (1813 / 4000 : ℝ) • dualS B

theorem dualDenom_posDef {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    (dualDenom B).PosDef := by
  exact (Matrix.PosDef.one.smul (show (0 : ℝ) < 37 / 40 by norm_num)).add_posSemidef
    (hB.smul (show (0 : ℝ) ≤ 3 / 40 by norm_num))

theorem dualS_posDef {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    (dualS B).PosDef := (dualDenom_posDef hB).inv

theorem dualS_mul_denom {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualS B * dualDenom B = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (dualDenom_posDef hB).det_pos.ne')

theorem dualDenom_mul_S {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualDenom B * dualS B = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (dualDenom_posDef hB).det_pos.ne')

/-- The regularized inverse commutes with the first-chaos Gram matrix. -/
theorem dualS_commute {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    Commute (dualS B) B := by
  change dualS B * B = B * dualS B
  ext i j
  have h₁ := congrArg (fun M : Mat m => M i j) (dualS_mul_denom hB)
  have h₂ := congrArg (fun M : Mat m => M i j) (dualDenom_mul_S hB)
  simp only [dualDenom, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul] at h₁ h₂
  linarith

/-- The upper Loewner bound for the supporting matrix. -/
theorem dualS_le {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualS B ≤ (40 / 37 : ℝ) • (1 : Mat m) := by
  rw [Matrix.le_iff]
  have hid : (40 / 37 : ℝ) • (1 : Mat m) - dualS B =
      (3 / 37 : ℝ) • (dualS B * B) := by
    ext i j
    have h := congrArg (fun M : Mat m => M i j) (dualS_mul_denom hB)
    simp only [dualDenom, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  rw [hid]
  exact (Matrix.nonneg_iff_posSemidef.mp <|
    Commute.mul_nonneg (dualS_posDef hB).posSemidef.nonneg hB.nonneg
      (dualS_commute hB)).smul (by norm_num)

/-- The deviation is a weighted first-chaos defect (the paper's dual relations). -/
theorem dualT_eq {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualT B = -(3 / 40 : ℝ) • (dualS B * (B - 1)) := by
  ext i j
  have h := congrArg (fun M : Mat m => M i j) (dualS_mul_denom hB)
  simp only [dualDenom, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
  simp only [dualT, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  linarith

/-- The retained first-chaos defect is a positive weighted square. -/
theorem dualH_eq {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualH B = (3 / 40 : ℝ) • (dualS B * (B - 1) ^ 2) := by
  simp only [dualH, dualT_eq hB, Matrix.smul_mul, neg_smul, Matrix.neg_mul, neg_neg,
    pow_two, Matrix.mul_assoc]

theorem dualH_posSemidef {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    (dualH B).PosSemidef := by
  rw [dualH_eq hB]
  have hD : (B - 1).IsHermitian := hB.isHermitian.sub Matrix.isHermitian_one
  have hD2 : 0 ≤ (B - 1) ^ 2 := by
    apply Matrix.nonneg_iff_posSemidef.mpr
    rw [pow_two]
    have hpos := Matrix.posSemidef_conjTranspose_mul_self (B - 1)
    have heq : (B - 1).conjTranspose * (B - 1) = (B - 1) * (B - 1) :=
      congrArg (fun M : Mat m => M * (B - 1)) hD.eq
    exact heq ▸ hpos
  exact (Matrix.nonneg_iff_posSemidef.mp <|
    Commute.mul_nonneg (dualS_posDef hB).posSemidef.nonneg hD2
      (((dualS_commute hB).sub_right (Commute.one_right _)).pow_right 2)).smul
      (by norm_num)

/-- The completion-of-squares relation, with the exact factor `α = 3/40`. -/
theorem dualT_square {m : ℕ} {B : Mat m} (hB : B.PosSemidef) :
    dualT B ^ 2 = (3 / 40 : ℝ) • (dualH B * dualS B) := by
  have hcomm := ((dualS_commute hB).sub_right (Commute.one_right _)).eq
  calc
    dualT B ^ 2 = dualT B * (-(3 / 40 : ℝ) • (dualS B * (B - 1))) := by
      conv_lhs => rw [pow_two]; rhs; rw [dualT_eq hB]
    _ = (3 / 40 : ℝ) • (-(dualT B * (B - 1)) * dualS B) := by
      rw [Matrix.mul_smul, hcomm, ← Matrix.mul_assoc, neg_smul, Matrix.neg_mul, smul_neg]
    _ = _ := rfl

end Submission.Obl.Entropy__normalized_remainder
