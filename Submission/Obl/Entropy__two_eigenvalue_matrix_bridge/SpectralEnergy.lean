import Submission.Lib.PairEstimate.SpectralAlgebra
import Submission.Lib.PairEstimate.Integration

/-!
The threshold projectors are measurable by continuous ramp approximation.
Commutators with `v(A)` encode spectral gaps without differentiating eigenvectors.
-/

open scoped BigOperators Topology
open Matrix MeasureTheory Filter

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def squareEnergy (M : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

noncomputable def iterComm (L : Matrix n n ℝ) : ℕ → Matrix n n ℝ → Matrix n n ℝ
  | 0, Z => Z
  | k + 1, Z => L * iterComm L k Z - iterComm L k Z * L

noncomputable def cut (t a : ℝ) : ℝ := if t ≤ a then 1 else 0

lemma cut_sq (t a : ℝ) : cut t a ^ 2 = cut t a := by
  unfold cut
  split <;> norm_num

lemma cut_abs_le (t a : ℝ) : |cut t a| ≤ 1 := by
  unfold cut
  split <;> norm_num

lemma iterComm_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) (k : ℕ) (i j : n) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * iterComm (cfc v A) k Z *
      hA.eigenvectorUnitary) i j =
      (v (hA.eigenvalues i) - v (hA.eigenvalues j)) ^ k *
        ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
          hA.eigenvectorUnitary) i j := by
  induction k with
  | zero => simp [iterComm]
  | succ k ih =>
    simp only [iterComm, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
    rw [conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA),
      conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA), cfc_in_eigenbasis]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, ih]
    ring

lemma projected_iterComm_energy {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) (t : ℝ) (k : ℕ) :
    squareEnergy (cfc (cut t) A * iterComm (cfc v A) k Z * cfc (cut t) A) =
      ∑ i, ∑ j, cut t (hA.eigenvalues i) * cut t (hA.eigenvalues j) *
        ((v (hA.eigenvalues i) - v (hA.eigenvalues j)) ^ k *
          ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
            hA.eigenvectorUnitary) i j) ^ 2 := by
  unfold squareEnergy
  rw [← squareSum_orthogonal _ _ (eigenbasis_mul_transpose_self hA)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA),
    conjugate_mul _ _ _ (eigenbasis_mul_transpose_self hA), cfc_in_eigenbasis]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, iterComm_eigenbasis,
    mul_pow, cut_sq]
  ring

lemma iterComm_energy {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) (k : ℕ) :
    squareEnergy (iterComm (cfc v A) k Z) =
      ∑ i, ∑ j, ((v (hA.eigenvalues i) - v (hA.eigenvalues j)) ^ k *
        ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
          hA.eigenvectorUnitary) i j) ^ 2 := by
  unfold squareEnergy
  rw [← squareSum_orthogonal _ _ (eigenbasis_mul_transpose_self hA)]
  simp only [iterComm_eigenbasis]

noncomputable def cutRamp (t : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  min 1 (max 0 (1 + (k : ℝ) * (a - t)))

lemma continuous_cutRamp (t : ℝ) (k : ℕ) : Continuous (cutRamp t k) := by
  unfold cutRamp
  fun_prop

lemma cutRamp_eventually (t a : ℝ) : ∀ᶠ k : ℕ in atTop, cutRamp t k a = cut t a := by
  by_cases h : t ≤ a
  · apply Eventually.of_forall
    intro k
    simp only [cut, if_pos h, cutRamp]
    have : 1 ≤ 1 + (k : ℝ) * (a - t) := by
      have := mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr h)
      linarith
    rw [max_eq_right (by linarith), min_eq_left this]
  · have ha : 0 < t - a := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - a)⁻¹)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (t - a)⁻¹ < (k : ℝ) := hN.trans_le (Nat.cast_le.mpr hk)
    have hmul : 1 < (k : ℝ) * (t - a) := by
      simpa only [inv_mul_cancel₀ ha.ne'] using mul_lt_mul_of_pos_right hk' ha
    simp only [cut, if_neg h, cutRamp]
    rw [max_eq_left (by nlinarith), min_eq_right (by norm_num)]

lemma cfc_cutRamp_eventually {A : Matrix n n ℝ} (hA : A.IsHermitian) (t : ℝ) :
    ∀ᶠ k : ℕ in atTop, cfc (cutRamp t k) A = cfc (cut t) A := by
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i : n,
      cutRamp t k (hA.eigenvalues i) = cut t (hA.eigenvalues i) :=
    eventually_all.mpr fun i => cutRamp_eventually t _
  filter_upwards [hall] with k hk
  apply cfc_congr
  intro a ha
  rw [hA.spectrum_real_eq_range_eigenvalues] at ha
  obtain ⟨i, rfl⟩ := ha
  exact hk i

open scoped Matrix.Norms.L2Operator in
/-- A closed spectral threshold is measurable even through eigenvalue collisions. -/
lemma measurable_cfc_cut {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (A : Ω → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) (t : ℝ) (i j : n) :
    Measurable (fun x => cfc (cut t) (A x) i j) := by
  have hn (k : ℕ) : Continuous (fun x => cfc (cutRamp t k) (A x) i j) := by
    have hcfc : Continuous (fun x => cfc (cutRamp t k) (A x)) :=
      hc.cfc_of_mem_nhdsSet _ (s := Set.univ) Filter.univ_mem
        (fun x => (hA x).isSelfAdjoint) (continuous_cutRamp t k).continuousOn
    exact (continuous_apply j).comp ((continuous_apply i).comp hcfc)
  apply measurable_of_tendsto_metrizable (fun k => (hn k).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  have heq : (fun k => cfc (cutRamp t k) (A x) i j) =ᶠ[atTop]
      (fun _ => cfc (cut t) (A x) i j) :=
    (cfc_cutRamp_eventually (hA x) t).mono
      fun k hk => congrArg (fun M : Matrix n n ℝ => M i j) hk
  exact tendsto_const_nhds.congr' heq.symm

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
