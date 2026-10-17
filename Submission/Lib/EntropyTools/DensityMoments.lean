/-
Adapted from: here:o001

Original proofs by session x0004.
-/

import Mathlib

/-!
# Covariance of a Lebesgue probability density

The positivity argument at the end of Section 5 of the supplied paper does not
require log concavity. A finite second moment gives integrability of the entries;
a zero quadratic form would concentrate the density on a null hyperplane.
-/

open MeasureTheory
open scoped Matrix

namespace Submission.Lib.EntropyTools

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}

/-- A second moment controls any measurable scalar factor with quadratic growth. -/
theorem integrable_density_mul_of_quadratic_bound
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : AEStronglyMeasurable g volume)
    (c : ℝ) (hbound : ∀ x, |g x| ≤ c * (1 + ‖x‖ ^ 2)) :
    Integrable (fun x => f x * g x) volume := by
  apply ((hf.add hf2).const_mul c).mono' (hf.aestronglyMeasurable.mul hg)
  filter_upwards [] with x
  change ‖f x * g x‖ ≤ c * (f x + f x * ‖x‖ ^ 2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x)]
  calc
    f x * |g x| ≤ f x * (c * (1 + ‖x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound x) (hf0 x)
    _ = c * (f x + f x * ‖x‖ ^ 2) := by ring

/-- The vector first moment is a genuine Bochner integral. -/
theorem integrable_density_smul
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume) :
    Integrable (fun x => f x • x) volume := by
  apply (hf.add hf2).mono'
    (hf.aestronglyMeasurable.smul continuous_id.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x • x‖ ≤ f x + f x * ‖x‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  have h : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  nlinarith [mul_le_mul_of_nonneg_left h (hf0 x)]

/-- Coordinate evaluation commutes with the vector first moment. -/
theorem density_mean_apply
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume) (i : Fin m) :
    (∫ x, f x • x) i = ∫ x, f x * x i := by
  simpa using ((EuclideanSpace.proj i).integral_comp_comm
    (integrable_density_smul hf0 hf hf2)).symm

/-- Every centered second-moment integrand is integrable. -/
theorem integrable_density_centered_mul
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    Integrable (fun x => f x * (x i - b i) * (x j - b j)) volume := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin m) =>
      (x i - b i) * (x j - b j)) := by fun_prop
  have hb (x : EuclideanSpace ℝ (Fin m)) (k : Fin m) :
      |x k - b k| ≤ ‖x‖ + ‖b‖ := by
    exact (norm_sub_le (x k) (b k)).trans
      (add_le_add (PiLp.norm_apply_le x k) (PiLp.norm_apply_le b k))
  have hi := integrable_density_mul_of_quadratic_bound hf0 hf hf2
    hc.aestronglyMeasurable (2 + 2 * ‖b‖ ^ 2) (fun x => by
      rw [abs_mul]
      calc
        |x i - b i| * |x j - b j| ≤ (‖x‖ + ‖b‖) * (‖x‖ + ‖b‖) :=
          mul_le_mul (hb x i) (hb x j) (abs_nonneg _) (by positivity)
        _ ≤ (2 + 2 * ‖b‖ ^ 2) * (1 + ‖x‖ ^ 2) := by
          nlinarith [sq_nonneg (‖x‖ - ‖b‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖b‖)])
  simpa only [mul_assoc] using hi

/-- The second-moment matrix around an arbitrary center. -/
noncomputable def densityCovariance (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => ∫ x, f x * (x i - b i) * (x j - b j)

/-- Symmetry needs no integrability assumptions. -/
theorem densityCovariance_isHermitian (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : (densityCovariance f b).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, densityCovariance]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem quadratic_integrand_expansion (b x : EuclideanSpace ℝ (Fin m))
    (u : Fin m → ℝ) :
    f x * (∑ i, u i * (x i - b i)) ^ 2 =
      ∑ i, ∑ j, (u i * u j) * (f x * (x i - b i) * (x j - b j)) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The weighted square of every centered linear form is integrable. -/
theorem integrable_density_quadratic
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) (u : Fin m → ℝ) :
    Integrable (fun x => f x * (∑ i, u i * (x i - b i)) ^ 2) volume := by
  simp_rw [quadratic_integrand_expansion b _ u]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_density_centered_mul hf0 hf hf2 b i j).const_mul (u i * u j)

/-- Evaluation of the covariance quadratic form as an integral of a square. -/
theorem densityCovariance_quadratic
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) (u : Fin m → ℝ) :
    u ⬝ᵥ (densityCovariance f b *ᵥ u) =
      ∫ x, f x * (∑ i, u i * (x i - b i)) ^ 2 := by
  simp_rw [quadratic_integrand_expansion b _ u]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrable_density_centered_mul hf0 hf hf2 b i j).const_mul (u i * u j)))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (integrable_density_centered_mul hf0 hf hf2 b _ j).const_mul (_ * u j)),
    integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, densityCovariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonzero linear form equals its value at a fixed point only on a null set. -/
theorem ae_centered_linearForm_ne_zero (b : EuclideanSpace ℝ (Fin m))
    (u : Fin m → ℝ) (hu : u ≠ 0) :
    ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂volume,
      (∑ i, u i * (x i - b i)) ≠ 0 := by
  let F : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := ∑ i, u i • EuclideanSpace.proj i
  have hF (x : EuclideanSpace ℝ (Fin m)) : F x = ∑ i, u i * x i := by
    simp [F, EuclideanSpace.proj]
  have hF0 : F.toLinearMap ≠ 0 := by
    intro h
    apply hu
    funext i
    have he := LinearMap.congr_fun h (PiLp.single 2 i (1 : ℝ))
    change F (PiLp.single 2 i (1 : ℝ)) = 0 at he
    simpa [hF, PiLp.single_apply] using he
  have hker : volume (F.toLinearMap.ker : Set (EuclideanSpace ℝ (Fin m))) = 0 :=
    Measure.addHaar_submodule volume _ (fun h => hF0 (LinearMap.ker_eq_top.mp h))
  have hnull := (measure_preimage_add_right volume (-b)
    (F.toLinearMap.ker : Set (EuclideanSpace ℝ (Fin m)))).trans hker
  rw [ae_iff]
  convert hnull using 1
  congr 1
  ext x
  simp [LinearMap.mem_ker, hF, ← sub_eq_add_neg]

/-- A nonzero Lebesgue density has strictly positive second-moment matrix about any center. -/
theorem densityCovariance_posDef
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hprob : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) : (densityCovariance f b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (densityCovariance_isHermitian f b)
  intro u hu
  simp only [star_trivial]
  rw [densityCovariance_quadratic hf0 hf hf2]
  have hnonneg (x) : 0 ≤ f x * (∑ i, u i * (x i - b i)) ^ 2 :=
    mul_nonneg (hf0 x) (sq_nonneg _)
  by_contra h
  have hzero : (∫ x, f x * (∑ i, u i * (x i - b i)) ^ 2) = 0 :=
    le_antisymm (le_of_not_gt h) (integral_nonneg hnonneg)
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg
    (integrable_density_quadratic hf0 hf hf2 b u)).mp hzero
  have hfzero : f =ᵐ[volume] 0 := by
    filter_upwards [hae, ae_centered_linearForm_ne_zero b u hu] with x hx hlin
    exact (mul_eq_zero.mp hx).resolve_right (pow_ne_zero _ hlin)
  have : (1 : ℝ) = 0 := by simpa [hprob] using integral_congr_ae hfzero
  exact one_ne_zero this

/-- This positivity justifies continuity of the covariance log determinant. -/
theorem densityCovariance_det_pos
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hprob : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) : 0 < (densityCovariance f b).det :=
  (densityCovariance_posDef hf0 hf hprob hf2 b).det_pos

/-- Scalar first moments inherit integrability from the vector first moment. -/
theorem integrable_density_coord
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume) (i : Fin m) :
    Integrable (fun x => f x * x i) volume := by
  simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp
    (integrable_density_smul hf0 hf hf2)

/-- Centering the raw second moment subtracts the product of the means. -/
theorem densityCovariance_eq_raw_moments
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hprob : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : EuclideanSpace ℝ (Fin m)) (hb : b = ∫ x, f x • x) (i j : Fin m) :
    densityCovariance f b i j = (∫ x, f x * x i * x j) - b i * b j := by
  have hi := integrable_density_coord hf0 hf hf2 i
  have hj := integrable_density_coord hf0 hf hf2 j
  have hij : Integrable (fun x => f x * x i * x j) volume := by
    simpa using integrable_density_centered_mul hf0 hf hf2 0 i j
  have hmi : ∫ x, f x * x i = b i := by rw [hb, density_mean_apply hf0 hf hf2]
  have hmj : ∫ x, f x * x j = b j := by rw [hb, density_mean_apply hf0 hf hf2]
  calc
    densityCovariance f b i j = ∫ x,
        ((f x * x i * x j - (f x * x i) * b j) - b i * (f x * x j)) +
          (b i * b j) * f x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x, f x * x i * x j) - b i * b j := by
      have hs₁ := integral_sub hij (hi.mul_const (b j))
      have hs₂ := integral_sub (hij.sub (hi.mul_const (b j))) (hj.const_mul (b i))
      have ha := integral_add ((hij.sub (hi.mul_const (b j))).sub (hj.const_mul (b i)))
        (hf.const_mul (b i * b j))
      simp only [Pi.sub_apply] at hs₁ hs₂ ha
      rw [ha, hs₂, hs₁]
      simp only [integral_const_mul, integral_mul_const, hmi, hmj, hprob]
      ring

end Submission.Lib.EntropyTools
