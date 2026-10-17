import Submission.Obl.Entropy__affine_exponential_moments.Exponential

namespace Submission.Entropy

theorem affine_exponential_moments :
∀ m : ℕ, ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, ∀ L : (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin m)), ∀ a : (EuclideanSpace ℝ (Fin m)), (∀ᵐ x ∂MeasureTheory.volume, f x = |LinearMap.det L.toLinearMap|⁻¹ * (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i)) else 0)) → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x • x) → ∀ C : (Matrix (Fin m) (Fin m) ℝ), C = (fun i j => MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x * (x i - b i) * (x j - b j))) → ∀ H : ℝ, H = -MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) (fun x => f x * Real.log (f x)) → H = (m : ℝ) + Real.log |LinearMap.det L.toLinearMap| ∧ C.det = (LinearMap.det L.toLinearMap) ^ 2 := by
  intro m f L a h b hb C hC H hH
  subst H C b
  exact Submission.Obl.Entropy__affine_exponential_moments.moments_of_ae_affine_product L a h

end Submission.Entropy
