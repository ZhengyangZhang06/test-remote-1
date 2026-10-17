import Submission.Lib.Cone

open MeasureTheory Set SimplexIsotropic Matrix Submission.Lib.Cone
open scoped ENNReal NNReal

namespace Submission.Obl.Cone__moments

lemma density_second_moment {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K)
    (i j : Fin (n+1)) :
    (∫ z, density K z * (z i * z j)) =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((vol K)⁻¹ *
        ∫ x in K, join 1 x i * join 1 x j) := by
  rw [homogeneous_integral (k := 2) hK (by fun_prop)
    (by intro t ht z; simp only [PiLp.smul_apply, smul_eq_mul]; ring)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hv := ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

noncomputable def coneCov {n : ℕ} (K : Set (E n)) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => ∫ z, density K z * (z i - ((n : ℝ)+1) * join 1 (centroid K) i) *
    (z j - ((n : ℝ)+1) * join 1 (centroid K) j)

lemma coneCov_raw {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) (i j : Fin (n+1)) :
    coneCov K i j = ((n : ℝ)+1) * ((n : ℝ)+2) *
      ((vol K)⁻¹ * ∫ x in K, join 1 x i * join 1 x j) -
      (((n : ℝ)+1) * join 1 (centroid K) i) * (((n : ℝ)+1) * join 1 (centroid K) j) := by
  let b := ((n : ℝ)+1) • join 1 (centroid K)
  change (∫ z, density K z * (z i - b i) * (z j - b j)) = _
  rw [show (fun z => density K z * (z i - b i) * (z j - b j)) =
    (fun z => density K z * (z i * z j) - (density K z * z i) * b j -
      (density K z * z j) * b i + density K z * (b i * b j)) by funext z; ring]
  have hraw := density_coordinates_integrable hK i j
  have hij := (density_coordinate_integrable hK i).mul_const (b j)
  have hji := (density_coordinate_integrable hK j).mul_const (b i)
  have hb := (density_integrable hK).mul_const (b i * b j)
  have hs : Integrable (fun z => density K z * (z i * z j) - (density K z * z i) * b j) :=
    hraw.sub hij
  have hss : Integrable (fun z => density K z * (z i * z j) - (density K z * z i) * b j -
      (density K z * z j) * b i) := hs.sub hji
  rw [integral_add hss hb, integral_sub hs hji, integral_sub hraw hij]
  rw [integral_mul_const, integral_mul_const, integral_mul_const,
    density_integral hK, density_first_moment hK, density_first_moment hK,
    density_second_moment hK]
  dsimp [b]
  ring

lemma coneCov_zero_zero {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    coneCov K 0 0 = (n : ℝ)+1 := by
  rw [coneCov_raw hK]
  simp only [join_zero, mul_one, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  change ((n : ℝ)+1) * ((n : ℝ)+2) * ((vol K)⁻¹ * vol K) - _ = _
  rw [inv_mul_cancel₀ (ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK))]
  ring

lemma coneCov_zero_succ {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) (j : Fin n) :
    coneCov K 0 j.succ = ((n : ℝ)+1) * centroid K j := by
  rw [coneCov_raw hK]
  simp only [join_zero, join_succ, one_mul, mul_one,
    Submission.Lib.BodyMoments.body_first_moment hK]
  rw [← mul_assoc (vol K)⁻¹, inv_mul_cancel₀
    (ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK))]
  ring

lemma coneCov_succ_zero {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) (i : Fin n) :
    coneCov K i.succ 0 = ((n : ℝ)+1) * centroid K i := by
  rw [coneCov_raw hK]
  simp only [join_zero, join_succ, mul_one,
    Submission.Lib.BodyMoments.body_first_moment hK]
  rw [← mul_assoc (vol K)⁻¹, inv_mul_cancel₀
    (ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK))]
  ring

lemma coneCov_succ_succ {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) (i j : Fin n) :
    coneCov K i.succ j.succ = ((n : ℝ)+1) *
      (((n : ℝ)+2) * covMatrix K i j + centroid K i * centroid K j) := by
  rw [coneCov_raw hK, Submission.Lib.BodyMoments.body_covMatrix_raw_moment hK]
  simp only [join_succ]
  ring

private def blockIndex (n : ℕ) : Fin (n+1) ≃ PUnit.{1} ⊕ Fin n :=
  ((finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))).trans
    (Equiv.sumComm (Fin n) PUnit.{1})

private lemma blockIndex_zero (n : ℕ) : blockIndex n 0 = Sum.inl PUnit.unit := by
  simp [blockIndex]

private lemma blockIndex_succ {n : ℕ} (i : Fin n) : blockIndex n i.succ = Sum.inr i := by
  simp [blockIndex]

lemma coneCov_det {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    (coneCov K).det = ((n : ℝ)+1) ^ (n+1) * ((n : ℝ)+2) ^ n * (covMatrix K).det := by
  let B : Matrix PUnit.{1} (Fin n) ℝ := fun _ j => centroid K j
  let C : Matrix (Fin n) PUnit.{1} ℝ := fun i _ => centroid K i
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ((n : ℝ)+2) * covMatrix K i j + centroid K i * centroid K j
  let M : Matrix (PUnit.{1} ⊕ Fin n) (PUnit.{1} ⊕ Fin n) ℝ := Matrix.fromBlocks 1 B C D
  have hmat : coneCov K = ((n : ℝ)+1) • M.submatrix (blockIndex n) (blockIndex n) := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [Matrix.fromBlocks, M, Matrix.submatrix_apply, blockIndex_zero, coneCov_zero_zero hK]
    · simp [Matrix.fromBlocks, M, B, Matrix.submatrix_apply, blockIndex_zero, blockIndex_succ, coneCov_zero_succ hK]
    · simp [Matrix.fromBlocks, M, C, Matrix.submatrix_apply, blockIndex_zero, blockIndex_succ, coneCov_succ_zero hK]
    · simp [Matrix.fromBlocks, M, D, Matrix.submatrix_apply, blockIndex_succ, coneCov_succ_succ hK]
  have hschur : D - C * B = ((n : ℝ)+2) • covMatrix K := by
    ext i j
    change D i j - ∑ k : PUnit.{1}, C i k * B k j = ((n : ℝ)+2) * covMatrix K i j
    simp [B, C, D]
  rw [hmat, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Fintype.card_fin]
  change ((n : ℝ)+1) ^ (n+1) * (Matrix.fromBlocks 1 B C D).det = _
  rw [Matrix.det_fromBlocks_one₁₁, hschur, Matrix.det_smul, Fintype.card_fin]
  ring

end Submission.Obl.Cone__moments
