import Submission.Obl.Entropy__transport_covariance_completion.Pairing
import Submission.Obl.Entropy__gaussian_weak_h1_testing

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

section Gaussian
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "γ" => stdGaussian E

/-- The scalar H1 extension, summed with the constant matrix weight. -/
theorem pairing_weak_testing (P : M) {H k : E → M} {v K : Fin m → E → M}
    (hH : ∀ i j, MemLp (fun x => H x i j) 2 γ)
    (hv : ∀ r i j, MemLp (fun x => v r x i j) 2 γ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 γ)
    (hK : ∀ r i j, MemLp (fun x => K r x i j) 2 γ)
    (hks : ∀ i j, ContDiff ℝ ∞ (fun x => k x i j))
    (hder : ∀ r x i j, K r x i j = fderiv ℝ (fun y => k y i j) x (PiLp.single 2 r (1 : ℝ)))
    (hweak : ∀ i j, ∀ z : E → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, H x i j * z x ∂γ) = ∑ r, ∫ x, v r x i j *
        fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂γ) :
    pairing (μ := γ) P H k = ∑ r, pairing (μ := γ) P (v r) (K r) := by
  have he (i j l : Fin m) :
      (∫ x, H x l i * k x j i ∂γ) = ∑ r, ∫ x, v r x l i * K r x j i ∂γ := by
    have hd r : MemLp (fun x => fderiv ℝ (fun y => k y j i) x
        (PiLp.single 2 r (1 : ℝ))) 2 γ := by
      simpa only [← hder] using hK r j i
    have h := Submission.Entropy.gaussian_weak_h1_testing m
      (fun x => H x l i) (fun r x => v r x l i) (hH l i) (fun r => hv r l i)
      (hweak l i) (fun x => k x j i) (hks j i) (hk j i) hd
    simpa only [← hder] using h
  simp only [pairing, he, Finset.mul_sum]
  trans ∑ i, ∑ j, ∑ r, ∑ l, P l j * ∫ x, v r x l i * K r x j i ∂γ
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  trans ∑ i, ∑ r, ∑ j, ∑ l, P l j * ∫ x, v r x l i * K r x j i ∂γ
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  exact Finset.sum_comm
end Gaussian

section Algebra
variable {Ω n r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
  [Fintype r] {μ : Measure Ω}

/-- Expanding the two energies uses exactly the cross term supplied by weak testing. -/
theorem pairing_completion {P : Matrix n n ℝ} (hP : P.IsHermitian)
    {J k u : Ω → Matrix n n ℝ} {K v : r → Ω → Matrix n n ℝ}
    (hJ : ∀ i j, MemLp (fun x => J x i j) 2 μ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 μ)
    (hu : ∀ i j, MemLp (fun x => u x i j) 2 μ)
    (hK : ∀ s i j, MemLp (fun x => K s x i j) 2 μ)
    (hv : ∀ s i j, MemLp (fun x => v s x i j) 2 μ)
    (hc : pairing (μ := μ) P (fun x => u x - (J x - k x)) k =
      ∑ s, pairing (μ := μ) P (fun x => v s x - K s x) (K s)) :
    pairing (μ := μ) P (fun x => k x + u x) (fun x => k x + u x) +
        ∑ s, pairing (μ := μ) P (fun x => v s x - K s x) (fun x => v s x - K s x) =
      2 * pairing (μ := μ) P J k - pairing (μ := μ) P k k -
        ∑ s, pairing (μ := μ) P (K s) (K s) + pairing (μ := μ) P u u +
        ∑ s, pairing (μ := μ) P (v s) (v s) := by
  have hjk : ∀ i j, MemLp (fun x => (J x - k x) i j) 2 μ :=
    fun i j => (hJ i j).sub (hk i j)
  rw [pairing_sub_left P hu hjk hk, pairing_sub_left P hJ hk hk] at hc
  have hsub s := pairing_sub_left P (hv s) (hK s) (hK s)
  simp_rw [hsub] at hc
  rw [Finset.sum_sub_distrib] at hc
  rw [pairing_add_self hP hk hu, pairing_comm hP k u]
  have hs s := pairing_sub_self hP (hv s) (hK s)
  simp_rw [hs]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-- Cyclicity places a row weight in front of the matrix product. -/
theorem pairing_eq_trace_mul (P : Matrix n n ℝ) {F G : Ω → Matrix n n ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 μ)
    (hFs : ∀ x, (F x).IsHermitian) :
    pairing (μ := μ) P F G = ∫ x, (P * (G x * F x)).trace ∂μ := by
  rw [pairing_eq_trace P hF hG]
  apply integral_congr_ae
  filter_upwards [] with x
  have ht : (F x).transpose = F x := by simpa using (hFs x).eq
  rw [ht, trace_mul_cycle, Matrix.mul_assoc]
end Algebra

end Submission.Obl.Entropy__transport_covariance_completion
