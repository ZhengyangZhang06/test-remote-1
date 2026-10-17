import Submission.Obl.Entropy__transport_covariance_completion.Pairing
import Submission.Obl.Entropy__transport_covariance_completion.WeakTesting

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
    have h := weak_h1_testing (μ := γ) (fun r : Fin m => PiLp.single 2 r (1 : ℝ))
      (hH l i) (fun r => hv r l i) (hweak l i) (hks j i) (hk j i) hd
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
  rw [ht, trace_mul_cycle, trace_mul_cycle, Matrix.mul_assoc]

/-- All entries of the covariance correction are integrable. -/
theorem integrable_completion {T k : Ω → Matrix n n ℝ} {K : r → Ω → Matrix n n ℝ}
    (hT : ∀ i j, Integrable (fun x => T x i j) μ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 μ)
    (hK : ∀ s i j, MemLp (fun x => K s x i j) 2 μ) :
    ∀ i j, Integrable (fun x => (2 • T x - k x * k x - ∑ s, K s x * K s x) i j) μ := by
  intro i j
  have hsum : Integrable (fun x => ∑ s, (K s x * K s x) i j) μ :=
    integrable_finsetSum _ fun s _ => integrable_matrix_mul (hK s) (hK s) i j
  simp only [two_smul, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply]
  exact (((hT i j).add (hT i j)).sub (integrable_matrix_mul hk hk i j)).sub hsum

/-- Integration of the weighted matrix correction is linear. -/
theorem integral_weighted_completion (P : Matrix n n ℝ)
    {T k : Ω → Matrix n n ℝ} {K : r → Ω → Matrix n n ℝ}
    (hT : ∀ i j, Integrable (fun x => T x i j) μ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 μ)
    (hK : ∀ s i j, MemLp (fun x => K s x i j) 2 μ) :
    (∫ x, (P * (2 • T x - k x * k x - ∑ s, K s x * K s x)).trace ∂μ) =
      2 * (∫ x, (P * T x).trace ∂μ) - (∫ x, (P * (k x * k x)).trace ∂μ) -
        ∑ s, (∫ x, (P * (K s x * K s x)).trace ∂μ) := by
  have hiT := integrable_trace_const_mul P hT
  have hik := integrable_trace_const_mul P (integrable_matrix_mul hk hk)
  have hiK s := integrable_trace_const_mul P (integrable_matrix_mul (hK s) (hK s))
  simp only [two_smul, mul_sub, mul_add, Finset.mul_sum, trace_sub, trace_add, trace_sum]
  simp only [← two_mul]
  have hs := integral_sub ((hiT.const_mul 2).sub hik)
    (integrable_finsetSum Finset.univ fun s _ => hiK s)
  simp only [Pi.sub_apply] at hs
  rw [hs, integral_sub (hiT.const_mul 2) hik, integral_const_mul,
    integral_finsetSum Finset.univ (fun s _ => hiK s)]

/-- The exact weighted square completion in Lemma 3.2. -/
theorem completed_energy {P : Matrix n n ℝ} (hP : P.IsHermitian)
    {J k u T : Ω → Matrix n n ℝ} {K v : r → Ω → Matrix n n ℝ}
    (hJ : ∀ i j, MemLp (fun x => J x i j) 2 μ)
    (hk : ∀ i j, MemLp (fun x => k x i j) 2 μ)
    (hu : ∀ i j, MemLp (fun x => u x i j) 2 μ)
    (hK : ∀ s i j, MemLp (fun x => K s x i j) 2 μ)
    (hv : ∀ s i j, MemLp (fun x => v s x i j) 2 μ)
    (hT : ∀ i j, Integrable (fun x => T x i j) μ)
    (hJs : ∀ x, (J x).IsHermitian) (hks : ∀ x, (k x).IsHermitian)
    (hKs : ∀ s x, (K s x).IsHermitian) (hkJ : ∀ x, k x * J x = T x)
    (hc : pairing (μ := μ) P (fun x => u x - (J x - k x)) k =
      ∑ s, pairing (μ := μ) P (fun x => v s x - K s x) (K s)) :
    (∫ x, ((k x + u x).transpose * P * (k x + u x)).trace ∂μ) +
        ∑ s, (∫ x, ((v s x - K s x).transpose * P * (v s x - K s x)).trace ∂μ) =
      (∫ x, (P * (2 • T x - k x * k x - ∑ s, K s x * K s x)).trace ∂μ) +
        (∫ x, ((u x).transpose * P * u x).trace ∂μ) +
        ∑ s, (∫ x, ((v s x).transpose * P * v s x).trace ∂μ) := by
  have htrace := integral_weighted_completion P hT hk hK
  have ht : pairing (μ := μ) P J k = ∫ x, (P * T x).trace ∂μ := by
    rw [pairing_eq_trace_mul P hJ hk hJs]
    simp only [hkJ]
  have hkr s := pairing_eq_trace_mul P (hK s) (hK s) (hKs s)
  rw [← ht, ← pairing_eq_trace_mul P hk hk hks] at htrace
  simp_rw [← hkr] at htrace
  rw [htrace]
  have hku : ∀ i j, MemLp (fun x => (k x + u x) i j) 2 μ :=
    fun i j => (hk i j).add (hu i j)
  have hvk s : ∀ i j, MemLp (fun x => (v s x - K s x) i j) 2 μ :=
    fun i j => (hv s i j).sub (hK s i j)
  have hsum s := pairing_eq_trace P (hvk s) (hvk s)
  have hvv s := pairing_eq_trace P (hv s) (hv s)
  rw [← pairing_eq_trace P hku hku, ← pairing_eq_trace P hu hu]
  simp_rw [← hsum, ← hvv]
  exact pairing_completion hP hJ hk hu hK hv hc

end Algebra

end Submission.Obl.Entropy__transport_covariance_completion
