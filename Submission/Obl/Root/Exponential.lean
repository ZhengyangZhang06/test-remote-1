import Submission.Obl.Root.DensityAffine
import Submission.Lib.Cone.Integration

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open Submission.Lib.EntropyTools

namespace Submission.Obl.Root.DensityAffine

/-- The real density of a mean-one exponential variable. -/
noncomputable def expDensity (x : ℝ) : ℝ :=
  (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) x

/-- The density of independent mean-one exponential coordinates. -/
noncomputable def productExpDensity {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i, expDensity (x i)

theorem expDensity_nonneg (x : ℝ) : 0 ≤ expDensity x := by
  exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x

theorem productExpDensity_nonneg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ productExpDensity x :=
  Finset.prod_nonneg (fun i _ => expDensity_nonneg (x i))

/-- Every nonnegative integer moment of the one-dimensional exponential law. -/
theorem integral_expDensity_pow (k : ℕ) :
    (∫ x : ℝ, expDensity x * x ^ k) = (k.factorial : ℝ) := by
  have h : (fun x : ℝ => expDensity x * x ^ k) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * x ^ k) := by
    ext x
    by_cases hx : x ∈ Ici (0 : ℝ) <;> simp [expDensity, hx]
  rw [h, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact Submission.Lib.Cone.integral_gamma_nat k

theorem integrable_expDensity_pow (k : ℕ) :
    Integrable (fun x : ℝ => expDensity x * x ^ k) := by
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ k) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (Submission.Lib.Cone.integrable_gamma_nat k)
  convert! hi.integrable_indicator measurableSet_Ici using 1
  ext x
  by_cases hx : x ∈ Ici (0 : ℝ) <;> simp [expDensity, hx]

/-- Mixed moments factor as factorials by Fubini. -/
theorem integral_productExpDensity_monomial {n : ℕ} (k : Fin n → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x * ∏ i, (x i) ^ k i) =
      ∏ i, ((k i).factorial : ℝ) := by
  have hc := (PiLp.volume_preserving_ofLp (Fin n)).integral_comp'
    (f := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm)
    (fun x : Fin n → ℝ => ∏ i, expDensity (x i) * (x i) ^ k i)
  have hp := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin n => (volume : Measure ℝ))
    (fun i : Fin n => fun x : ℝ => expDensity x * x ^ k i)
  have ht := hc.trans hp
  simpa only [productExpDensity, Finset.prod_mul_distrib, Function.comp_def,
    MeasurableEquiv.coe_toLp_symm, integral_expDensity_pow] using ht

theorem integrable_productExpDensity_monomial {n : ℕ} (k : Fin n → ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      productExpDensity x * ∏ i, (x i) ^ k i) := by
  have hi := Integrable.fintype_prod (fun i : Fin n => integrable_expDensity_pow (k i))
  have hc := (PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    (g := fun x : Fin n → ℝ => ∏ i, expDensity (x i) * (x i) ^ k i)
  apply hc.mpr at hi
  simpa only [Function.comp_def, productExpDensity, Finset.prod_mul_distrib] using hi

theorem integral_productExpDensity (n : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x) = 1 := by
  simpa using integral_productExpDensity_monomial (fun _ : Fin n => 0)

theorem integrable_productExpDensity (n : ℕ) :
    Integrable (productExpDensity : EuclideanSpace ℝ (Fin n) → ℝ) := by
  simpa using integrable_productExpDensity_monomial (fun _ : Fin n => 0)

private theorem monomial_single {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (k : ℕ) :
    (∏ j, x j ^ (if j = i then k else 0)) = x i ^ k := by
  simp [apply_ite]

/-- Every coordinate of the exponential product has the one-dimensional moments. -/
theorem integral_productExpDensity_coord_pow {n : ℕ} (i : Fin n) (k : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x * x i ^ k) =
      (k.factorial : ℝ) := by
  have h := integral_productExpDensity_monomial (fun j : Fin n => if j = i then k else 0)
  simp only [monomial_single] at h
  simpa [apply_ite] using h

theorem integrable_productExpDensity_coord_pow {n : ℕ} (i : Fin n) (k : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => productExpDensity x * x i ^ k) := by
  simpa only [monomial_single] using
    integrable_productExpDensity_monomial (fun j : Fin n => if j = i then k else 0)

/-- The raw cross moments of the independent exponential coordinates. -/
theorem integral_productExpDensity_coord_mul {n : ℕ} (i j : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x * x i * x j) =
      if i = j then 2 else 1 := by
  by_cases hij : i = j
  · subst j
    simpa [pow_two, mul_assoc] using integral_productExpDensity_coord_pow i 2
  · have h := integral_productExpDensity_monomial
      (fun k : Fin n => (if k = i then 1 else 0) + (if k = j then 1 else 0))
    have hprod (x : EuclideanSpace ℝ (Fin n)) :
        (∏ k, x k ^ ((if k = i then 1 else 0) + (if k = j then 1 else 0))) = x i * x j := by
      simp only [pow_add, Finset.prod_mul_distrib, monomial_single, pow_one]
    simp_rw [hprod] at h
    have hfac (k : Fin n) :
        (((if k = i then 1 else 0) + (if k = j then 1 else 0) : ℕ).factorial : ℝ) = 1 := by
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j <;> simp [hki, hkj, Ne.symm hij]
    simp_rw [hfac] at h
    simpa [hij, mul_assoc] using h

theorem integrable_second_productExpDensity (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => productExpDensity x * ‖x‖ ^ 2) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_productExpDensity_coord_pow i 2)

/-- The mean vector has every coordinate equal to one. -/
theorem mean_productExpDensity_apply {n : ℕ} (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x • x) i = 1 := by
  rw [density_mean_apply productExpDensity_nonneg (integrable_productExpDensity n)
    (integrable_second_productExpDensity n)]
  simpa using integral_productExpDensity_coord_pow i 1

/-- The exponential product has identity covariance. -/
theorem covariance_productExpDensity (n : ℕ) :
    densityCovariance (productExpDensity : EuclideanSpace ℝ (Fin n) → ℝ)
      (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x • x) = 1 := by
  ext i j
  rw [densityCovariance_eq_raw_moments productExpDensity_nonneg (integrable_productExpDensity n)
    (integral_productExpDensity n) (integrable_second_productExpDensity n) _ rfl,
    mean_productExpDensity_apply, mean_productExpDensity_apply,
    integral_productExpDensity_coord_mul]
  by_cases hij : i = j <;> norm_num [hij, Matrix.one_apply]

/-- Closed form of the exponential product on the positive orthant. -/
theorem productExpDensity_eq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    productExpDensity x =
      if ∀ i, 0 ≤ x i then Real.exp (-∑ i, x i) else 0 := by
  classical
  by_cases hx : ∀ i, 0 ≤ x i
  · rw [if_pos hx]
    unfold productExpDensity
    simp [expDensity, hx, ← Real.exp_sum, Finset.sum_neg_distrib]
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact indicator_of_notMem hi _

/-- The entropy integrand is the negative sum of the coordinate first moments. -/
theorem productExpDensity_mul_log {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    productExpDensity x * Real.log (productExpDensity x) =
      -∑ i, productExpDensity x * x i := by
  by_cases hx : ∀ i, 0 ≤ x i
  · have hf := productExpDensity_eq x
    rw [if_pos hx] at hf
    rw [hf, Real.log_exp]
    simp [Finset.mul_sum]
  · rw [productExpDensity_eq, if_neg hx]
    simp

theorem integrable_entropy_productExpDensity (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      productExpDensity x * Real.log (productExpDensity x)) := by
  simp_rw [productExpDensity_mul_log]
  apply Integrable.neg
  exact integrable_finsetSum _ (fun i _ => by
    simpa using integrable_productExpDensity_coord_pow i 1)

/-- The entropy of the exponential product equals its dimension. -/
theorem entropy_productExpDensity (n : ℕ) :
    -(∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x * Real.log (productExpDensity x)) = n := by
  simp_rw [productExpDensity_mul_log]
  rw [integral_neg, neg_neg, integral_finsetSum _ (fun i _ => by
    simpa using integrable_productExpDensity_coord_pow i 1)]
  have hm (i : Fin n) :
      (∫ x : EuclideanSpace ℝ (Fin n), productExpDensity x * x i) = 1 := by
    simpa using integral_productExpDensity_coord_pow i 1
  simp [hm]

/-- Every invertible affine image of the exponential product has zero entropy gap. -/
theorem entropy_equality_affine_product {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) :
    -(∫ y, affineDensity e b productExpDensity y *
        Real.log (affineDensity e b productExpDensity y)) =
      (n : ℝ) + Real.log (densityCovariance (affineDensity e b productExpDensity)
        (∫ y, affineDensity e b productExpDensity y • y)).det / 2 := by
  have h := entropy_deficit_affineDensity e b productExpDensity_nonneg
    (integrable_productExpDensity n) (integral_productExpDensity n)
    (integrable_second_productExpDensity n) (integrable_entropy_productExpDensity n)
  rw [entropy_productExpDensity, covariance_productExpDensity, Matrix.det_one, Real.log_one,
    zero_div, sub_zero] at h
  linarith

/-- The exact entropy and covariance determinant of any a.e. affine exponential product. -/
theorem moments_of_ae_affine_product {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : ∀ᵐ x ∂volume, f x = |LinearMap.det L.toLinearMap|⁻¹ *
      (if ∀ i, 0 ≤ L.symm (x - b) i then Real.exp (-∑ i, L.symm (x - b) i) else 0)) :
    -(∫ x, f x * Real.log (f x)) = (n : ℝ) + Real.log |LinearMap.det L.toLinearMap| ∧
      (densityCovariance f (∫ x, f x • x)).det = (LinearMap.det L.toLinearMap) ^ 2 := by
  let e := L.toContinuousLinearEquiv
  have heq : f =ᵐ[volume] affineDensity e b productExpDensity := by
    filter_upwards [h] with x hx
    simpa [affineDensity, productExpDensity_eq, e] using hx
  have hm : (∫ x, f x • x) = ∫ x, affineDensity e b productExpDensity x • x := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  have hc : densityCovariance f (∫ x, f x • x) =
      densityCovariance (affineDensity e b productExpDensity)
        (∫ x, affineDensity e b productExpDensity x • x) := by
    ext i j
    unfold densityCovariance
    rw [hm]
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  have hh : (∫ x, f x * Real.log (f x)) =
      ∫ x, affineDensity e b productExpDensity x *
        Real.log (affineDensity e b productExpDensity x) := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  rw [hh, hc]
  constructor
  · rw [entropy_affineDensity e b (integrable_productExpDensity n)
      (integrable_entropy_productExpDensity n) (integral_productExpDensity n),
      entropy_productExpDensity]
    rfl
  · rw [mean_affineDensity e b (integrable_productExpDensity n)
      (integrable_density_smul productExpDensity_nonneg (integrable_productExpDensity n)
        (integrable_second_productExpDensity n)) (integral_productExpDensity n),
      covariance_det_affineDensity e b _ productExpDensity_nonneg
        (integrable_productExpDensity n) (integrable_second_productExpDensity n),
      covariance_productExpDensity, Matrix.det_one, mul_one]
    rfl

/-- Altering an affine exponential product on a null set leaves its entropy gap zero. -/
theorem entropy_equality_of_ae_affine_product {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : ∀ᵐ x ∂volume, f x = |LinearMap.det L.toLinearMap|⁻¹ *
      (if ∀ i, 0 ≤ L.symm (x - b) i then Real.exp (-∑ i, L.symm (x - b) i) else 0)) :
    -(∫ x, f x * Real.log (f x)) =
      (n : ℝ) + Real.log (densityCovariance f (∫ x, f x • x)).det / 2 := by
  obtain ⟨hH, hC⟩ := moments_of_ae_affine_product L b h
  rw [hH, hC, Real.log_pow, Real.log_abs]
  ring

/-- The nonnegative orthant is closed and convex. -/
theorem orthant_isClosed (n : ℕ) : IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by fun_prop)

theorem orthant_convex (n : ℕ) : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
  intro x hx y hy a b ha hb _ i
  change 0 ≤ a * x i + b * y i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- The exponential-product density is upper semicontinuous, including its boundary. -/
theorem upperSemicontinuous_productExpDensity (n : ℕ) :
    UpperSemicontinuous (productExpDensity : EuclideanSpace ℝ (Fin n) → ℝ) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-∑ i, x i)) := by
    fun_prop
  intro x r hr
  by_cases hx : ∀ i, 0 ≤ x i
  · have hr' : Real.exp (-∑ i, x i) < r := by
      simpa only [productExpDensity_eq, if_pos hx] using hr
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hr')] with y hy
    by_cases hy0 : ∀ i, 0 ≤ y i
    · simpa only [productExpDensity_eq, if_pos hy0] using hy
    · have hr0 : 0 < r := (productExpDensity_nonneg x).trans_lt hr
      simpa only [productExpDensity_eq, if_neg hy0] using hr0
  · have hr0 : 0 < r := by simpa only [productExpDensity_eq, if_neg hx] using hr
    filter_upwards [(orthant_isClosed n).isOpen_compl.mem_nhds hx] with y hy
    change ¬ (∀ i, 0 ≤ y i) at hy
    simpa only [productExpDensity_eq, if_neg hy] using hr0

/-- The logarithm of the exponential density is affine on its positive support. -/
theorem log_concave_productExpDensity (n : ℕ) :
    ConcaveOn ℝ {x : EuclideanSpace ℝ (Fin n) | 0 < productExpDensity x}
      (fun x => Real.log (productExpDensity x)) := by
  have hs : {x : EuclideanSpace ℝ (Fin n) | 0 < productExpDensity x} =
      {x | ∀ i, 0 ≤ x i} := by
    ext x
    by_cases hx : ∀ i, 0 ≤ x i <;> simp [productExpDensity_eq, hx, Real.exp_pos]
  rw [hs]
  refine ⟨orthant_convex n, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := orthant_convex n hx hy ha hb hab
  change ∀ i, 0 ≤ x i at hx
  change ∀ i, 0 ≤ y i at hy
  change ∀ i, 0 ≤ (a • x + b • y) i at hxy
  simp only [productExpDensity_eq, if_pos hx, if_pos hy, if_pos hxy, Real.log_exp]
  change a * (-∑ i, x i) + b * (-∑ i, y i) ≤ -(∑ i, (a * x i + b * y i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring_nf
  exact le_rfl

/-- All hypotheses of the entropy inequality hold for affine exponential products. -/
theorem affine_product_regular {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) :
    (∀ x, 0 ≤ affineDensity e b productExpDensity x) ∧
    UpperSemicontinuous (affineDensity e b productExpDensity) ∧
    ConcaveOn ℝ {x | 0 < affineDensity e b productExpDensity x}
      (fun x => Real.log (affineDensity e b productExpDensity x)) ∧
    Integrable (affineDensity e b productExpDensity) ∧
    (∫ x, affineDensity e b productExpDensity x) = 1 ∧
    Integrable (fun x => affineDensity e b productExpDensity x * ‖x‖ ^ 2) ∧
    Integrable (fun x => affineDensity e b productExpDensity x *
      Real.log (affineDensity e b productExpDensity x)) := by
  refine ⟨affineDensity_nonneg e b productExpDensity_nonneg,
    upperSemicontinuous_affineDensity e b (upperSemicontinuous_productExpDensity n),
    log_concave_affineDensity e b (log_concave_productExpDensity n),
    integrable_affineDensity e b (integrable_productExpDensity n), ?_,
    integrable_second_affineDensity e b productExpDensity_nonneg (integrable_productExpDensity n)
      (integrable_second_productExpDensity n),
    integrable_entropy_affineDensity e b (integrable_productExpDensity n)
      (integrable_entropy_productExpDensity n)⟩
  rw [integral_affineDensity, integral_productExpDensity]

end Submission.Obl.Root.DensityAffine
