/-
Adapted from: here:o006
Original matrix functional-calculus derivative proofs by session x0063.
-/

import Mathlib

open scoped BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℝ}

/-- The rank-one projections supplied by a fixed orthonormal eigenbasis. -/
noncomputable def spectralProjector (hA : A.IsHermitian) (i : n) : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℝ)))

lemma sum_spectralProjector (hA : A.IsHermitian) :
    ∑ i, spectralProjector hA i = 1 := by
  simp only [spectralProjector, ← map_sum]
  have h : (∑ i : n, Matrix.diagonal (Pi.single i (1 : ℝ))) = (1 : Matrix n n ℝ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [Matrix.sum_apply, Pi.single_apply]
    · simp [Matrix.sum_apply, hjk]
  rw [h, map_one]

lemma spectralProjector_mul_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) (i : n) :
    spectralProjector hA i * cfc f A = f (hA.eigenvalues i) • spectralProjector hA i := by
  rw [hA.cfc_eq]
  simp only [spectralProjector, Matrix.IsHermitian.cfc, ← map_mul, ← map_smul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

lemma spectralProjector_mul_self (hA : A.IsHermitian) (i : n) :
    spectralProjector hA i * A = hA.eigenvalues i • spectralProjector hA i := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  simpa only [hid] using spectralProjector_mul_cfc hA (fun x : ℝ => x) i

lemma cfc_eq_sum_spectralProjector (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (hA.eigenvalues i) • spectralProjector hA i := by
  conv_lhs => rw [← one_mul (cfc f A), ← sum_spectralProjector hA, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => spectralProjector_mul_cfc hA f i)

/-- The scalar divided-difference identity lifted to one Hermitian matrix. -/
lemma sub_smul_cfc_dslope (hB : B.IsHermitian) (f : ℝ → ℝ) (a : ℝ) :
    B * cfc (dslope f a) B - a • cfc (dslope f a) B = cfc f B - f a • 1 := by
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn g
  have hid : cfc (fun t : ℝ => t) B = B := cfc_id' ℝ B hB.isSelfAdjoint
  calc
    B * cfc (dslope f a) B - a • cfc (dslope f a) B =
        cfc (fun t => t * dslope f a t - a * dslope f a t) B := by
      rw [cfc_sub _ _ _ (hc _) (hc _), cfc_mul _ _ _ (hc _) (hc _),
        cfc_const_mul a (dslope f a) B (hc _), hid]
    _ = cfc (fun t => f t - f a) B := by
      apply cfc_congr
      intro t _
      simpa only [smul_eq_mul, sub_mul] using sub_smul_dslope f a t
    _ = cfc f B - f a • 1 := by
      rw [cfc_sub _ _ _ (hc _) (hc _)]
      congr 1
      simpa only [Algebra.algebraMap_eq_smul_one] using cfc_const (f a) B hB.isSelfAdjoint

/-- A divided-difference identity with projectors fixed at the base matrix.
It does not require distinct eigenvalues or regular eigenvector choices. -/
lemma cfc_sub_eq_sum_projector (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f B - cfc f A = ∑ i, spectralProjector hA i * (B - A) *
      cfc (dslope f (hA.eigenvalues i)) B := by
  have hterm (i : n) :
      spectralProjector hA i * (B - A) * cfc (dslope f (hA.eigenvalues i)) B =
        spectralProjector hA i * cfc f B - f (hA.eigenvalues i) • spectralProjector hA i := by
    rw [mul_sub, sub_mul, spectralProjector_mul_self, smul_mul_assoc, mul_assoc,
      ← mul_smul_comm, ← mul_sub, sub_smul_cfc_dslope hB, mul_sub,
      mul_smul_comm, mul_one]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_spectralProjector, one_mul,
    ← cfc_eq_sum_spectralProjector hA f]

end Submission.Obl.Entropy__c1_bounded_matrix_calculus
