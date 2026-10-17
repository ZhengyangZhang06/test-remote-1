import Submission.Obl.Cone__moments.Integration
import Submission.Lib.BodyMoments

open MeasureTheory Set SimplexIsotropic
open scoped ENNReal NNReal

namespace Submission.Obl.Cone__moments

lemma density_integrable {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    Integrable (density K) := by
  simpa only [mul_one] using homogeneous_integrable (k := 0) hK
    (g := fun _ => (1 : ℝ)) continuous_const (by intros; simp)

lemma density_integral {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    (∫ z, density K z) = 1 := by
  have h := homogeneous_integral (k := 0) hK
    (g := fun _ => (1 : ℝ)) continuous_const (by intros; simp)
  simp only [mul_one, Nat.add_zero, integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul] at h
  rw [h]
  change (n.factorial : ℝ) / ((n.factorial : ℝ) * vol K) * vol K = 1
  field_simp [ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)]

lemma density_coordinate_integrable {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K)
    (i : Fin (n+1)) : Integrable (fun z => density K z * z i) := by
  apply homogeneous_integrable (k := 1) hK (by fun_prop)
  intro t ht z
  simp

lemma density_coordinates_integrable {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K)
    (i j : Fin (n+1)) : Integrable (fun z => density K z * (z i * z j)) := by
  apply homogeneous_integrable (k := 2) hK (by fun_prop)
  intro t ht z
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma density_norm_sq_integrable {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    Integrable (fun z => density K z * ‖z‖ ^ 2) := by
  apply homogeneous_integrable (k := 2) hK (by fun_prop)
  intro t ht z
  rw [norm_smul, Real.norm_of_nonneg ht.le, mul_pow]

lemma density_first_moment {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K)
    (i : Fin (n+1)) :
    (∫ z, density K z * z i) = ((n : ℝ) + 1) * join 1 (centroid K) i := by
  rw [homogeneous_integral (k := 1) hK (by fun_prop)
    (by intro t ht z; simp)]
  have hv := ne_of_gt (Submission.Lib.ConvexBody.body_vol_pos hK)
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [join_zero, integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
      mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    change ((n : ℝ) + 1) * n.factorial / (n.factorial * vol K) * vol K = _
    field_simp
  · simp only [join_succ, Submission.Lib.BodyMoments.body_first_moment hK,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

lemma density_mean {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    (∫ z, density K z • z) = ((n : ℝ) + 1) • join 1 (centroid K) := by
  ext i
  rw [eval_integral_piLp (fun j => density_coordinate_integrable hK j)]
  exact density_first_moment hK i

lemma density_log_product {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) (z : E (n+1)) :
    density K z * Real.log (density K z) =
      -(density K z * z 0) - density K z * Real.log ((n.factorial : ℝ) * vol K) := by
  classical
  by_cases hz : z ∈ cone K
  · rw [log_density hK hz]
    ring
  · simp [density, indicator_of_notMem hz]

lemma density_entropy_integrable {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    Integrable (fun z => density K z * Real.log (density K z)) := by
  simp_rw [density_log_product hK]
  exact (density_coordinate_integrable hK 0).neg.sub
    ((density_integrable hK).mul_const _)

lemma density_entropy {n : ℕ} {K : Set (E n)} (hK : IsConvexBody K) :
    -(∫ z, density K z * Real.log (density K z)) =
      (n : ℝ) + 1 + Real.log ((n.factorial : ℝ) * vol K) := by
  simp_rw [density_log_product hK]
  have hneg : Integrable (fun z => -(density K z * z 0)) :=
    (density_coordinate_integrable hK 0).neg
  have hlog : Integrable (fun z => density K z * Real.log ((n.factorial : ℝ) * vol K)) :=
    (density_integrable hK).mul_const _
  rw [integral_sub hneg hlog, integral_neg, integral_mul_const,
    density_first_moment hK, density_integral hK, join_zero]
  ring

end Submission.Obl.Cone__moments
