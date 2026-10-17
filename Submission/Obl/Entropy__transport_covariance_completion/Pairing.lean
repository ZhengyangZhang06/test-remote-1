import Submission.Obl.Entropy__transport_covariance_completion.Assembly

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory Matrix
open scoped BigOperators

set_option linter.unusedSectionVars false

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
  {μ : Measure Ω}

/-- The row-weighted integral pairing, written entrywise. -/
noncomputable def pairing (P : Matrix n n ℝ) (F G : Ω → Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, P k j * ∫ x, F x k i * G x j i ∂μ

theorem pairing_eq_trace (P : Matrix n n ℝ) {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ) :
    pairing (μ := μ) P F G = ∫ x, ((F x).transpose * P * G x).trace ∂μ := by
  have hi (i j k : n) : Integrable (fun x => F x k i * P k j * G x j i) μ := by
    simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using
      ((hF k i).integrable_mul (hG j i)).const_mul (P k j)
  simp only [trace, diag_apply, mul_apply, transpose_apply, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k)))]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem pairing_add_left (P : Matrix n n ℝ) {F G H : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ)
    (hH : ∀ i j, MemLp (fun x => H x i j) 2 μ) :
    pairing (μ := μ) P (fun x => F x + G x) H = pairing (μ := μ) P F H + pairing (μ := μ) P G H := by
  have hadd (i j k : n) :
      (∫ x, (F x k i + G x k i) * H x j i ∂μ) =
      (∫ x, F x k i * H x j i ∂μ) + (∫ x, G x k i * H x j i ∂μ) := by
    simp only [add_mul]
    exact integral_add ((hF k i).integrable_mul (hH j i))
      ((hG k i).integrable_mul (hH j i))
  simp only [pairing, Matrix.add_apply, hadd, mul_add, Finset.sum_add_distrib]

theorem pairing_sub_left (P : Matrix n n ℝ) {F G H : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ)
    (hH : ∀ i j, MemLp (fun x => H x i j) 2 μ) :
    pairing (μ := μ) P (fun x => F x - G x) H = pairing (μ := μ) P F H - pairing (μ := μ) P G H := by
  have hsub (i j k : n) :
      (∫ x, (F x k i - G x k i) * H x j i ∂μ) =
      (∫ x, F x k i * H x j i ∂μ) - (∫ x, G x k i * H x j i ∂μ) := by
    simp only [sub_mul]
    exact integral_sub ((hF k i).integrable_mul (hH j i))
      ((hG k i).integrable_mul (hH j i))
  simp only [pairing, Matrix.sub_apply, hsub, mul_sub, Finset.sum_sub_distrib]

theorem pairing_comm {P : Matrix n n ℝ} (hP : P.IsHermitian)
    (F G : Ω → Matrix n n ℝ) :
    pairing (μ := μ) P F G = pairing (μ := μ) P G F := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hp : P j k = P k j := by simpa using congrFun (congrFun hP.eq k) j
  rw [hp]
  congr 1
  congr 1
  funext x
  exact mul_comm _ _

theorem pairing_add_self {P : Matrix n n ℝ} (hP : P.IsHermitian)
    {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ) :
    pairing (μ := μ) P (fun x => F x + G x) (fun x => F x + G x) =
      pairing (μ := μ) P F F + 2 * pairing (μ := μ) P F G + pairing (μ := μ) P G G := by
  rw [pairing_add_left P (H := fun x => F x + G x) hF hG (fun i j => (hF i j).add (hG i j))]
  rw [pairing_comm hP F (fun x => F x + G x), pairing_add_left P hF hG hF,
    pairing_comm hP G (fun x => F x + G x), pairing_add_left P hF hG hG, pairing_comm hP G F]
  ring

theorem pairing_sub_self {P : Matrix n n ℝ} (hP : P.IsHermitian)
    {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ) :
    pairing (μ := μ) P (fun x => F x - G x) (fun x => F x - G x) =
      pairing (μ := μ) P F F - 2 * pairing (μ := μ) P F G + pairing (μ := μ) P G G := by
  rw [pairing_sub_left P (H := fun x => F x - G x) hF hG (fun i j => (hF i j).sub (hG i j))]
  rw [pairing_comm hP F (fun x => F x - G x), pairing_sub_left P hF hG hF,
    pairing_comm hP G (fun x => F x - G x), pairing_sub_left P hF hG hG, pairing_comm hP G F]
  ring

end Submission.Obl.Entropy__transport_covariance_completion
