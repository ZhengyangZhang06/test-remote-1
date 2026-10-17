import Submission.Obl.Entropy__noncommuting_remainder_assembly.Completion

open scoped BigOperators

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

lemma adjoint_column_energy [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (C : Matrix ι ι ℝ) (ev : ι → ℝ)
    (hX : ∑ r, X r * (X r).transpose = Matrix.diagonal ev) (j : ι) :
    (∑ r, ∑ k, (((X r).transpose * C) k j) ^ 2) =
      ∑ i, ev i * (C i j) ^ 2 := by
  have h := sum_squareSum_adjoint X (Matrix.of fun i (_ : Unit) => C i j)
  rw [hX] at h
  simpa [squareSum, pairing, Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply, pow_two,
    mul_assoc, mul_left_comm] using h

lemma adjoint_column_energy_weighted [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (C : Matrix ι ι ℝ) (ev d : ι → ℝ)
    (hX : ∑ r, X r * (X r).transpose = Matrix.diagonal ev) :
    (∑ r, ∑ k, ∑ j, (((X r).transpose * C) k j) ^ 2 / d j) =
      ∑ i, ∑ j, ev i * (C i j) ^ 2 / d j := by
  calc
    _ = ∑ r, ∑ j, ∑ k, (((X r).transpose * C) k j) ^ 2 / d j := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ j, ∑ r, ∑ k, (((X r).transpose * C) k j) ^ 2 / d j := Finset.sum_comm
    _ = ∑ j, (∑ i, ev i * (C i j) ^ 2) / d j := by
      simp only [← Finset.sum_div, adjoint_column_energy X C ev hX]
    _ = _ := by simp only [Finset.sum_div]; exact Finset.sum_comm

lemma skew_pairing (X : ν → Matrix ι κ ℝ) (C : Matrix ι ι ℝ)
    (W : ν → Matrix κ ι ℝ) (hC : C.transpose = -C) :
    (∑ r, pairing ((X r).transpose * C) (W r)) =
      -Matrix.trace (C * (∑ r, X r * W r)) := by
  simp_rw [← pairing_mul_left]
  rw [← pairing_sum_right, pairing_trace, hC, Matrix.neg_mul, Matrix.trace_neg]

lemma commutator_resolvent_coefficient {s α u v : ℝ}
    (hs : 0 < s) (hα : 0 < α) (hu : 0 < u) (hv : 0 < v) :
    ((1 - u) / (α * s * u)) / (s * (v + 1 / 8)) +
      ((1 - v) / (α * s * v)) / (s * (u + 1 / 8)) ≤
        1 / (α * s ^ 2 * u * v) := by
  have hu' : u + 1 / 8 ≠ 0 := by positivity
  have hv' : v + 1 / 8 ≠ 0 := by positivity
  calc
    _ = (v * (1 - u) / (v + 1 / 8) + u * (1 - v) / (u + 1 / 8)) /
        (α * s ^ 2 * u * v) := by
      field_simp
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right (commutator_coefficient hu.le hv.le) (by positivity)

lemma commutator_compensation_coefficient {s α u v : ℝ}
    (hs : s ≠ 0) (hα : α ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    ((s * u - 1) - (s * v - 1)) *
      ((1 - v) / (α * s * v) - (1 - u) / (α * s * u)) =
        (s * (u - v)) ^ 2 / (α * s ^ 2 * u * v) := by
  field_simp
  <;> ring

/-- A symmetric double sum is its average with the transpose. -/
lemma sum_pair_average (f : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, (f i j + f j i)) / 2 := by
  have h : (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm
  simp only [Finset.sum_add_distrib]
  rw [h]
  ring

lemma diagonal_compensation [DecidableEq ι]
    (t ev : ι → ℝ) (b : Matrix ι ι ℝ) (hb : b.transpose = b) :
    Matrix.trace (Matrix.diagonal t * b * Matrix.diagonal ev * b -
      Matrix.diagonal t * Matrix.diagonal ev * b * b) =
        (∑ i, ∑ j, (t i - t j) * (ev j - ev i) * (b i j) ^ 2) / 2 := by
  have hb' (i j : ι) : b j i = b i j := congrFun (congrFun hb i) j
  have hraw : Matrix.trace (Matrix.diagonal t * b * Matrix.diagonal ev * b -
      Matrix.diagonal t * Matrix.diagonal ev * b * b) =
        ∑ i, ∑ j, t i * (ev j - ev i) * (b i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_ite, mul_zero, Finset.sum_ite_eq]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hb' i j]
    ring
  rw [hraw, sum_pair_average (fun i j => t i * (ev j - ev i) * (b i j) ^ 2)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hb' j i]
  ring

lemma diagonal_right_energy [DecidableEq ι] (t : ι → ℝ) (W : Matrix κ ι ℝ) :
    Matrix.trace (Matrix.diagonal t * (W.transpose * W)) =
      ∑ i, ∑ j, t j * (W i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, pow_two]
  rw [Finset.sum_comm]

/-- A diagonal commutator bound reduced to its scalar paired coefficients. -/
lemma diagonal_commutator_bound [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (b : Matrix ι ι ℝ) (W : ν → Matrix κ ι ℝ)
    (t ev : ι → ℝ) (c : ℝ) (hb : b.transpose = b)
    (hd : ∀ j, 0 < t j + c)
    (hX : ∑ r, X r * (X r).transpose = Matrix.diagonal ev)
    (hcoeff : ∀ i j, (t i - t j) ^ 2 *
      (ev i / (t j + c) + ev j / (t i + c)) ≤
        (t i - t j) * (ev j - ev i)) :
    -Matrix.trace (Matrix.diagonal t * b * Matrix.diagonal ev * b -
      Matrix.diagonal t * Matrix.diagonal ev * b * b) -
      2 * Matrix.trace ((Matrix.diagonal t * b - b * Matrix.diagonal t) *
        (∑ r, X r * W r)) -
      Matrix.trace (Matrix.diagonal t * (∑ r, (W r).transpose * W r)) ≤
        c * (∑ r, squareSum (W r)) := by
  let C := Matrix.diagonal t * b - b * Matrix.diagonal t
  have hC : C.transpose = -C := by
    dsimp [C]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_transpose, hb]
    abel
  have hb' (i j : ι) : b j i = b i j := congrFun (congrFun hb i) j
  have hCij (i j : ι) : C i j = (t i - t j) * b i j := by
    simp [C, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hyoung := Finset.sum_le_sum (s := Finset.univ)
    (fun r _ => pairing_young_columns ((X r).transpose * C) (W r)
      (fun j => t j + c) hd)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hyoung
  rw [skew_pairing X C W hC, adjoint_column_energy_weighted X C ev _ hX] at hyoung
  have hp : (∑ i, ∑ j, ev i * (C i j) ^ 2 / (t j + c)) ≤
      Matrix.trace (Matrix.diagonal t * b * Matrix.diagonal ev * b -
        Matrix.diagonal t * Matrix.diagonal ev * b * b) := by
    rw [sum_pair_average (fun i j => ev i * (C i j) ^ 2 / (t j + c)),
      diagonal_compensation t ev b hb]
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right (hcoeff i j) (sq_nonneg (b i j))
    convert h using 1 <;> rw [hCij i j, hCij j i, hb' i j] <;> ring
  have hweight : (∑ r, ∑ i, ∑ j, (t j + c) * (W r i j) ^ 2) =
      Matrix.trace (Matrix.diagonal t * (∑ r, (W r).transpose * W r)) +
        c * (∑ r, squareSum (W r)) := by
    simp only [Matrix.mul_sum, Matrix.trace_sum, diagonal_right_energy,
      squareSum, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  change -_ - 2 * Matrix.trace (C * _) - _ ≤ _
  linarith


/-- Lemma 3.4 in an eigenbasis of the supporting-plane matrix. -/
lemma resolvent_commutator_diagonal [DecidableEq ι]
    (X : ν → Matrix ι κ ℝ) (b : Matrix ι ι ℝ) (W : ν → Matrix κ ι ℝ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (u : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hb : b.transpose = b)
    (hX : ∑ r, X r * (X r).transpose =
      Matrix.diagonal (fun i => (1 - u i) / (α * s * u i))) :
    let T := Matrix.diagonal (fun i => s * u i - 1);
    let B := Matrix.diagonal (fun i => (1 - u i) / (α * s * u i));
    -Matrix.trace (T * b * B * b - T * B * b * b) -
      2 * Matrix.trace ((T * b - b * T) * (∑ r, X r * W r)) -
      Matrix.trace (T * (∑ r, (W r).transpose * W r)) ≤
        (1 + s / 8) * (∑ r, squareSum (W r)) := by
  refine diagonal_commutator_bound X b W _ _ (1 + s / 8) hb ?_ hX ?_
  · intro j
    nlinarith [mul_pos hs (hu j)]
  · intro i j
    have h := mul_le_mul_of_nonneg_left
      (commutator_resolvent_coefficient hs hα (hu i) (hu j))
      (sq_nonneg (s * (u i - u j)))
    rw [commutator_compensation_coefficient (ne_of_gt hs) (ne_of_gt hα)
      (ne_of_gt (hu i)) (ne_of_gt (hu j))]
    convert h using 1 <;> first | rfl | ring


end Submission.Obl.Entropy__noncommuting_remainder_assembly
