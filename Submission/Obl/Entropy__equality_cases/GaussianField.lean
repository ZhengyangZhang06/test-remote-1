import Submission.Obl.Entropy__equality_cases.Rigidity

namespace Submission.Obl.Entropy__equality_cases

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Gaussian orthogonality expressed for a scalar linear form. -/
theorem gaussian_linear_form_square (a : ι → ℝ) :
    (∫ x : EuclideanSpace ℝ ι, (∑ i, x i * a i) ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ∑ i, (a i) ^ 2 := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  let L := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) v
  have hL : ∀ x, L x = ∑ i, x i * a i := by
    intro x
    simp [L, v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.aemeasurable, integral_strongDual_stdGaussian,
    show ‖L‖ = ‖v‖ from (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).norm_map v,
    EuclideanSpace.real_norm_sq_eq] at h
  simpa only [hL, sub_zero] using h

/-- Every scalar entry of a linear matrix field is square integrable for Gaussian measure. -/
theorem gaussian_linear_form_square_integrable (a : ι → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => (∑ i, x i * a i) ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  let L := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) v
  simpa [L, v, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using
    (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ ι)) L 2 (by norm_num)).integrable_sq

/-- Gaussian orthogonality identifies the L2 size of a linear matrix field with its coefficients. -/
theorem gaussian_linear_field_square (X : ι → Matrix ι ι ℝ) :
    (∫ x : EuclideanSpace ℝ ι, (∑ i, ∑ j, (linearField X x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∑ i, ∑ j, ∑ r, (X r i j) ^ 2 := by
  simp only [linearField, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => gaussian_linear_form_square_integrable (fun r => X r i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => gaussian_linear_form_square_integrable (fun r => X r i j))]
  simp_rw [gaussian_linear_form_square]

/-- The same identity for differences of linear fields. -/
theorem gaussian_linear_field_sub_square (X Y : ι → Matrix ι ι ℝ) :
    (∫ x : EuclideanSpace ℝ ι,
      (∑ i, ∑ j, (linearField X x i j - linearField Y x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∑ i, ∑ j, ∑ r, (X r i j - Y r i j) ^ 2 := by
  simpa only [linearField, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib] using
    gaussian_linear_field_square (fun r => X r - Y r)

/-- Coefficient convergence gives Gaussian L2 convergence of the linear matrix fields. -/
theorem gaussian_linear_field_L2_tendsto {α : Type*} {l : Filter α}
    (X : α → ι → Matrix ι ι ℝ) (Y : ι → Matrix ι ι ℝ)
    (hX : ∀ r i j, Filter.Tendsto (fun n => X n r i j) l (nhds (Y r i j))) :
    Filter.Tendsto (fun n => ∫ x : EuclideanSpace ℝ ι,
      (∑ i, ∑ j, (linearField (X n) x i j - linearField Y x i j) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) l (nhds 0) := by
  simp_rw [gaussian_linear_field_sub_square]
  have h (r i j : ι) : Filter.Tendsto (fun n => (X n r i j - Y r i j) ^ 2) l (nhds 0) := by
    simpa using ((hX r i j).sub_const (Y r i j)).pow 2
  simpa using tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      tendsto_finsetSum Finset.univ (fun r _ => h r i j)))

end Submission.Obl.Entropy__equality_cases
