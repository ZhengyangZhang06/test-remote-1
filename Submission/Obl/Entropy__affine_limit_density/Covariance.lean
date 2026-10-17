import Submission.Lib.EntropyTools.DensityMoments

open MeasureTheory Filter
open scoped Topology Matrix

namespace Submission.Obl.Entropy__affine_limit_density

open Submission.Lib.EntropyTools

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

noncomputable def linMatrix {m : ℕ} (P : E m →ₗ[ℝ] E m) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.toEuclideanLin.symm P

theorem linMatrix_apply {m : ℕ} (P : E m →ₗ[ℝ] E m) (x : E m) (i : Fin m) :
    P x i = ∑ j, linMatrix P i j * x j := by
  have h := LinearMap.congr_fun (Matrix.toEuclideanLin.apply_symm_apply P) x
  exact (congrArg (fun y : E m => y i) h).symm

/-- Density measures have the expected real-valued weighted integral. -/
theorem integral_density {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume) (g : E m → ℝ) :
    ∫ x, g x ∂(volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, f x * g x := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

/-- A finite-dimensional affine map transforms the full second-moment matrix by congruence. -/
theorem integral_density_linear_mul {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : E m) (P : E m →ₗ[ℝ] E m) (i j : Fin m) :
    (∫ x, f x * (P (x - b) i * P (x - b) j)) =
      (linMatrix P * densityCovariance f b * (linMatrix P).transpose) i j := by
  let A := linMatrix P
  have hexp (x : E m) : f x * (P (x - b) i * P (x - b) j) =
      ∑ k, ∑ l, (A i k * A j l) * (f x * (x k - b k) * (x l - b l)) := by
    simp only [linMatrix_apply, PiLp.sub_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp [A]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    (integrable_density_centered_mul hf0 hf hf2 b k l).const_mul (A i k * A j l)))]
  simp_rw [integral_finsetSum _ (fun l _ =>
    (integrable_density_centered_mul hf0 hf hf2 b _ l).const_mul (_ * A j l)),
    integral_const_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, densityCovariance]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  dsimp [A]
  ring

/-- Equality of transported laws identifies all second moments. -/
theorem covariance_of_map_eq {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (b : E m) (P : E m →ₗ[ℝ] E m) {μ : Measure (E m)} {F : E m → E m}
    (hF : AEMeasurable F μ)
    (hlaw : Measure.map F μ = Measure.map (fun x => P (x - b))
      (volume.withDensity (fun x => ENNReal.ofReal (f x)))) (i j : Fin m) :
    (∫ x, F x i * F x j ∂μ) =
      (linMatrix P * densityCovariance f b * (linMatrix P).transpose) i j := by
  have hg : Continuous (fun y : E m => y i * y j) := by fun_prop
  have hP : Continuous (fun x : E m => P (x - b)) :=
    P.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  rw [← integral_map hF hg.aestronglyMeasurable, hlaw,
    integral_map hP.aemeasurable hg.aestronglyMeasurable,
    integral_density hf0 hf]
  exact integral_density_linear_mul hf0 hf hf2 b P i j

end Submission.Obl.Entropy__affine_limit_density
