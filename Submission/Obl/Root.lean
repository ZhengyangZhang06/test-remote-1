import Mathlib
import ChallengeDeps
import Submission.Obl.Root.Algebra
import Submission.Obl.Entropy__lower_bound
import Submission.Obl.Entropy__equality_cases
import Submission.Obl.Cone__moments
import Submission.Obl.Cone__simplex_iff_product

open SimplexIsotropic

namespace Submission.Obl.Root

noncomputable def densityMean {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  MeasureTheory.integral MeasureTheory.volume (fun x => f x • x)

noncomputable def densityCov {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => MeasureTheory.integral MeasureTheory.volume
    (fun x => f x * (x i - densityMean f i) * (x j - densityMean f j))

noncomputable def densityEntropy {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x))

/-- The cone density from Section 7, with the height coordinate first. -/
noncomputable def coneDensity {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  Set.indicator
    {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i}
    (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * vol K))

/-- Reversibility of the logarithmic step of the cone reduction. -/
theorem cone_entropy_eq_iff_det_eq (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hv : 0 < vol K)
    (hd : 0 < (covMatrix K).det)
    (hH : densityEntropy (coneDensity K) =
      (n : ℝ) + 1 + Real.log ((n.factorial : ℝ) * vol K))
    (hC : (densityCov (coneDensity K)).det =
      ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (covMatrix K).det) :
    (densityEntropy (coneDensity K) =
      (n + 1 : ℕ) + Real.log (densityCov (coneDensity K)).det / 2) ↔
    ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (covMatrix K).det =
      (n.factorial : ℝ) ^ 2 * vol K ^ 2 := by
  have ha : 0 < (n.factorial : ℝ) * vol K := by positivity
  have hc : 0 < ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
      (covMatrix K).det := by positivity
  rw [hH, hC, Nat.cast_add, Nat.cast_one]
  constructor
  · intro h
    have hlog :
        Real.log (((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
          (covMatrix K).det) = Real.log (((n.factorial : ℝ) * vol K) ^ 2) := by
      rw [Real.log_pow]
      norm_num
      linarith
    have heq := Real.log_injOn_pos hc (sq_pos_of_pos ha) hlog
    simpa only [mul_pow] using heq
  · intro h
    have hpow :
        ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n * (covMatrix K).det =
          ((n.factorial : ℝ) * vol K) ^ 2 := by
      simpa only [mul_pow] using h
    rw [hpow, Real.log_pow]
    push_cast
    ring

end Submission.Obl.Root

namespace Submission

open Obl.Root

theorem theorem_1_1_ineq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K ≤ simplexBound n := by
  obtain ⟨hv, hd, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, hH, hC⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hbound := Entropy.lower_bound (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  rw [hH, hC, Nat.cast_add, Nat.cast_one] at hbound
  have ha : 0 < (n.factorial : ℝ) * vol K := by positivity
  have hc : 0 < ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
      (covMatrix K).det := by positivity
  have hlog :
      Real.log (((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 2) ^ n *
        (covMatrix K).det) ≤ Real.log (((n.factorial : ℝ) * vol K) ^ 2) := by
    rw [Real.log_pow]
    norm_num
    linarith
  apply (isotropicConstant_le_iff_det_le n hn K hv hd.le).mpr
  have hdet := (Real.log_le_log_iff hc (sq_pos_of_pos ha)).mp hlog
  simpa only [mul_pow] using hdet

theorem theorem_1_1_eq (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    isotropicConstant K = simplexBound n ↔ IsSimplex K := by
  obtain ⟨hv, hd, hnonneg, hupper, hconcave, hint, hmass, hsecond, hent, hH, hC⟩ :=
    Cone.moments n hn K hK (coneDensity K) rfl
      (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
      (densityEntropy (coneDensity K)) rfl
  have hequality := Entropy.equality_cases (n + 1) (by omega) (coneDensity K)
    hnonneg hupper hconcave hint hmass hsecond hent
    (densityMean (coneDensity K)) rfl (densityCov (coneDensity K)) rfl
    (densityEntropy (coneDensity K)) rfl
  exact (isotropicConstant_eq_iff_det_eq n hn K hv hd.le).trans
    ((cone_entropy_eq_iff_det_eq n K hv hd hH hC).symm.trans
      (hequality.trans (Cone.simplex_iff_product n hn K hK (coneDensity K) rfl)))

end Submission
