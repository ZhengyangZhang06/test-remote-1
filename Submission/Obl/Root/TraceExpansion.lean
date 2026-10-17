import Mathlib

/-!
# Exact noncommuting trace identities for Section 3

These identities retain transposes on the nonsymmetric derivative residuals.
-/

open scoped BigOperators

namespace Submission.Obl.Root

lemma trace_cross_transpose {ι : Type*} [Fintype ι]
    {T : Matrix ι ι ℝ} (hT : T.IsHermitian) (A B : Matrix ι ι ℝ) :
    (T * A.transpose * B).trace = (T * B.transpose * A).trace := by
  have hTs : T.transpose = T := by simpa using hT.eq
  rw [← Matrix.trace_transpose (T * A.transpose * B)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hTs, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]

/-- Moving a factor around a trace leaves an explicit commutator correction. -/
lemma trace_commutator_reorder {ι : Type*} [Fintype ι]
    (T b X D : Matrix ι ι ℝ) :
    (T * b * X * D).trace = (T * X * D * b).trace +
      ((T * b - b * T) * X * D).trace := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub]
  have he : (b * T * X * D).trace = (T * X * D * b).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm b (T * X * D)
  rw [he]
  ring

/-- Energy expansion for `K = X b + D`, where `D` need not be symmetric. -/
lemma trace_energy_expansion {ι : Type*} [Fintype ι]
    (T K X b D : Matrix ι ι ℝ) (hT : T.IsHermitian) (hK : K.IsHermitian)
    (hX : X.IsHermitian) (hb : b.IsHermitian) (hKD : K = X * b + D) :
    (T * (K * K)).trace = (T * b * (X * X) * b).trace +
      2 * (T * b * X * D).trace + (T * D.transpose * D).trace := by
  have hKs : K.transpose = K := by simpa using hK.eq
  have hXs : X.transpose = X := by simpa using hX.eq
  have hbs : b.transpose = b := by simpa using hb.eq
  have he : K * K = (X * b + D).transpose * (X * b + D) := by
    rw [← hKD, hKs]
  rw [he]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hXs, hbs,
    Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  have hcross : (T * D.transpose * (X * b)).trace = (T * b * X * D).trace := by
    rw [trace_cross_transpose hT D (X * b)]
    simp only [Matrix.transpose_mul, hXs, hbs, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc] at hcross ⊢
  rw [hcross]
  ring

lemma trace_energy_expansion_sum {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (T b : Matrix ι ι ℝ) (K X D : ρ → Matrix ι ι ℝ)
    (hT : T.IsHermitian) (hb : b.IsHermitian)
    (hK : ∀ r, (K r).IsHermitian) (hX : ∀ r, (X r).IsHermitian)
    (hKD : ∀ r, K r = X r * b + D r) :
    (T * ∑ r, K r * K r).trace =
      (T * b * (∑ r, X r * X r) * b).trace +
      2 * (T * b * ∑ r, X r * D r).trace +
      (T * ∑ r, (D r).transpose * D r).trace := by
  simp only [Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Matrix.mul_assoc] using trace_energy_expansion T (K r) (X r) b (D r)
    hT (hK r) (hX r) hb (hKD r)

/-- Completing a square with a possibly indefinite symmetric left weight. -/
lemma trace_square_completion {ι : Type*} [Fintype ι]
    (T D g : Matrix ι ι ℝ) (γ : ℝ) (hT : T.IsHermitian) (hg : g.IsHermitian) :
    -(T * D.transpose * D).trace + 2 * γ * (T * D.transpose * g).trace =
      -(T * (D - γ • g).transpose * (D - γ • g)).trace +
        γ ^ 2 * (T * (g * g)).trace := by
  have hgs : g.transpose = g := by simpa using hg.eq
  have hcross : (T * g * D).trace = (T * D.transpose * g).trace := by
    simpa only [hgs] using trace_cross_transpose hT g D
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, hgs,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hcross, ← Matrix.mul_assoc]
  ring

lemma trace_weighted_pair_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : Matrix ι ι ℝ} (hS : S.IsHermitian) (A B : Matrix ι κ ℝ) :
    (A.transpose * S * B).trace = (B.transpose * S * A).trace := by
  have hs : S.transpose = S := by simpa using hS.eq
  rw [← Matrix.trace_transpose (A.transpose * S * B)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]

lemma trace_transpose_left {ι : Type*} [Fintype ι]
    (F T b : Matrix ι ι ℝ) (hT : T.IsHermitian) (hb : b.IsHermitian) :
    (F.transpose * T * b).trace = (T * F * b).trace := by
  have hTs : T.transpose = T := by simpa using hT.eq
  have hbs : b.transpose = b := by simpa using hb.eq
  calc
    _ = (b * T * F).trace := by
      rw [← Matrix.trace_transpose (F.transpose * T * b)]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hTs, hbs, Matrix.mul_assoc]
    _ = _ := by simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm b (T * F)

/-- The initial weighted square expansion from Lemma 3.3. -/
lemma trace_initial_weighted_square {ι : Type*} [Fintype ι]
    (F M b S T H : Matrix ι ι ℝ) (α : ℝ)
    (hM : M.IsHermitian) (hb : b.IsHermitian) (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSM : S * M = -α⁻¹ • T) (hMSM : M * S * M = α⁻¹ • H) :
    ((F + M * b).transpose * S * (F + M * b)).trace =
      (F.transpose * S * F).trace + α⁻¹ * (H * (b * b)).trace -
        2 * α⁻¹ * (T * F * b).trace := by
  have hMs : M.transpose = M := by simpa using hM.eq
  have hbs : b.transpose = b := by simpa using hb.eq
  have h1 : (F.transpose * S * (M * b)).trace = -α⁻¹ * (T * F * b).trace := by
    calc
      _ = (F.transpose * (S * M) * b).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hSM, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
          trace_transpose_left F T b hT hb]
  have h2 : ((M * b).transpose * S * F).trace = -α⁻¹ * (T * F * b).trace := by
    rw [trace_weighted_pair_symm hS, h1]
  have h3 : ((M * b).transpose * S * (M * b)).trace = α⁻¹ * (H * (b * b)).trace := by
    calc
      _ = (b * (M * S * M) * b).trace := by
        simp only [Matrix.transpose_mul, hMs, hbs, Matrix.mul_assoc]
      _ = α⁻¹ * (b * H * b).trace := by
        rw [hMSM, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      _ = _ := by
        congr 1
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm b (H * b)
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  rw [h1, h2, h3]
  ring

end Submission.Obl.Root
