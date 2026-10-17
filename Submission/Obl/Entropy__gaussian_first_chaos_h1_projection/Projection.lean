import Submission.Obl.Entropy__gaussian_first_chaos_h1_projection.Analytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_first_chaos_h1_projection

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian E

noncomputable def linearPart (c : Fin m → ℝ) : E →L[ℝ] ℝ :=
  ∑ r, c r • EuclideanSpace.proj r

lemma linearPart_apply (c : Fin m → ℝ) (x : E) :
    linearPart c x = ∑ r, x r * c r := by
  simp [linearPart, mul_comm]

lemma linearPart_single (c : Fin m → ℝ) (r : Fin m) :
    linearPart c (PiLp.single 2 r (1 : ℝ)) = c r := by
  simp [linearPart_apply, PiLp.single_apply]

lemma linearPart_memLp (c : Fin m → ℝ) : MemLp (linearPart c) 2 γ :=
  IsGaussian.memLp_dual γ (linearPart c) 2 (by norm_num)

lemma integral_linearPart_mul (c : Fin m → ℝ) {f : E → ℝ} (hf : MemLp f 2 γ) :
    (∫ x, linearPart c x * f x ∂γ) = ∑ r, c r * ∫ x, x r * f x ∂γ := by
  simp_rw [linearPart_apply, Finset.sum_mul,
    show ∀ r (x : E), x r * c r * f x = c r * (x r * f x) from fun r x => by ring]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro r _
    exact ((coord_memLp r).integrable_mul hf).const_mul (c r)

lemma integral_coord_linearPart (c : Fin m → ℝ) (r : Fin m) :
    (∫ x : E, x r * linearPart c x ∂γ) = c r := by
  simp_rw [mul_comm _ (linearPart c _)]
  rw [integral_linearPart_mul c (coord_memLp r)]
  simp [integral_coord_mul]

lemma integral_linearPart_sq (c : Fin m → ℝ) :
    (∫ x, (linearPart c x)^2 ∂γ) = ∑ r, (c r)^2 := by
  simp_rw [pow_two]
  rw [integral_linearPart_mul c (linearPart_memLp c)]
  simp_rw [integral_coord_linearPart]

noncomputable def firstCoeff (f : E → ℝ) (r : Fin m) : ℝ :=
  ∫ x, x r * f x ∂γ

noncomputable def scalarRemainder (f : E → ℝ) (x : E) : ℝ :=
  f x - linearPart (firstCoeff f) x

lemma remainder_contDiff {f : E → ℝ} {n : WithTop ENat} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (scalarRemainder f) :=
  hf.sub (linearPart (firstCoeff f)).contDiff

lemma remainder_memLp {f : E → ℝ} (hf : MemLp f 2 γ) :
    MemLp (scalarRemainder f) 2 γ :=
  hf.sub (linearPart_memLp (firstCoeff f))

lemma fderiv_remainder {f : E → ℝ} (hf : Differentiable ℝ f) (x : E) (r : Fin m) :
    fderiv ℝ (scalarRemainder f) x (PiLp.single 2 r (1 : ℝ)) =
      fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) - firstCoeff f r := by
  change fderiv ℝ (f - ⇑(linearPart (firstCoeff f))) x (PiLp.single 2 r (1 : ℝ)) = _
  rw [fderiv_sub (hf x) (linearPart (firstCoeff f)).differentiableAt,
    ContinuousLinearMap.fderiv]
  simp [linearPart_single]

lemma integral_remainder {f : E → ℝ} (hf : MemLp f 2 γ) (hmean : (∫ x, f x ∂γ) = 0) :
    (∫ x, scalarRemainder f x ∂γ) = 0 := by
  simp only [scalarRemainder]
  rw [integral_sub (hf.integrable (by norm_num))
    ((linearPart_memLp (firstCoeff f)).integrable (by norm_num)), hmean,
    integral_strongDual_stdGaussian, sub_zero]

lemma integral_coord_remainder {f : E → ℝ} (hf : MemLp f 2 γ) (r : Fin m) :
    (∫ x : E, x r * scalarRemainder f x ∂γ) = 0 := by
  simp_rw [scalarRemainder, mul_sub]
  rw [integral_sub, integral_coord_linearPart]
  · exact sub_self _
  · exact (coord_memLp r).integrable_mul hf
  · exact (coord_memLp r).integrable_mul (linearPart_memLp (firstCoeff f))

lemma integral_sub_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x - g x)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ) - 2 * (∫ x, f x * g x ∂μ) + ∫ x, (g x)^2 ∂μ := by
  simp_rw [sub_sq, mul_assoc]
  rw [integral_add, integral_sub, integral_const_mul]
  · exact hf.integrable_sq
  · exact (hf.integrable_mul hg).const_mul 2
  · exact hf.integrable_sq.sub ((hf.integrable_mul hg).const_mul 2)
  · exact hg.integrable_sq

lemma integral_remainder_sq {f : E → ℝ} (hf : MemLp f 2 γ) :
    (∫ x, (scalarRemainder f x)^2 ∂γ) = (∫ x, (f x)^2 ∂γ) - ∑ r, (firstCoeff f r)^2 := by
  simp only [scalarRemainder]
  rw [integral_sub_sq hf (linearPart_memLp (firstCoeff f)),
    integral_linearPart_sq]
  have h : (∫ x, f x * linearPart (firstCoeff f) x ∂γ) = ∑ r, (firstCoeff f r)^2 := by
    simp_rw [mul_comm _ (linearPart (firstCoeff f) _)]
    rw [integral_linearPart_mul (firstCoeff f) hf]
    simp only [firstCoeff, pow_two]
  rw [h]
  ring

lemma integral_centered_sq {f : E → ℝ} (hf : MemLp f 2 γ) (c : ℝ)
    (hc : (∫ x, f x ∂γ) = c) :
    (∫ x, (f x - c)^2 ∂γ) = (∫ x, (f x)^2 ∂γ) - c^2 := by
  rw [integral_sub_sq hf (memLp_const c), integral_mul_const, hc]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma remainder_energy {f : E → ℝ} (hf : Differentiable ℝ f) (hL2 : MemLp f 2 γ)
    (hd : ∀ r : Fin m, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2 γ) :
    (∫ x, (f x)^2 ∂γ) - ∑ r, ∫ x, (fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))^2 ∂γ =
    (∫ x, (scalarRemainder f x)^2 ∂γ) -
      ∑ r, ∫ x, (fderiv ℝ (scalarRemainder f) x (PiLp.single 2 r (1 : ℝ)))^2 ∂γ := by
  simp_rw [fderiv_remainder hf]
  have hmean (r : Fin m) :
      (∫ x, fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)) ∂γ) = firstCoeff f r :=
    gaussian_integral_fderiv_of_memLp hf hL2 r (hd r)
  simp_rw [integral_centered_sq (hd _) _ (hmean _)]
  rw [integral_remainder_sq hL2, Finset.sum_sub_distrib]
  ring

end Submission.Obl.Entropy__gaussian_first_chaos_h1_projection
