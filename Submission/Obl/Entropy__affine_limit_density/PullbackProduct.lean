import Submission.Obl.Entropy__affine_limit_density.Pullback

open MeasureTheory

namespace Submission.Obl.Entropy__affine_limit_density

open Submission.Obl.Entropy__affine_exponential_moments

/-- Composition of affine densities, including their absolute Jacobians. -/
theorem affineDensity_comp {m : ℕ} (P L0 : E m ≃L[ℝ] E m)
    (b a0 : E m) (g : E m → ℝ) :
    affineDensity P.symm b (affineDensity L0 a0 g) =
      affineDensity (L0.trans P.symm) (b + P.symm a0) g := by
  ext x
  have hd : (L0.trans P.symm).toLinearMap = P.symm.toLinearMap.comp L0.toLinearMap := rfl
  simp only [affineDensity, hd, LinearMap.det_comp, abs_mul, mul_inv_rev]
  have ha : (L0.trans P.symm).symm (x - (b + P.symm a0)) =
      L0.symm (P (x - b) - a0) := by
    simp [sub_add_eq_sub_sub, map_sub]
  rw [ha]
  simp only [ContinuousLinearEquiv.symm_symm]
  ring

/-- Pull an affine exponential law back through an arbitrary invertible normalization. -/
theorem exists_affine_exponential_of_map_eq {m : ℕ} {f : E m → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (P : E m ≃ₗ[ℝ] E m) (b : E m) (L0 : E m ≃ₗ[ℝ] E m) (a0 : E m)
    (hlaw : Measure.map (fun x => P (x - b))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal
        (|LinearMap.det L0.toLinearMap|⁻¹ *
          (if ∀ i : Fin m, 0 ≤ L0.symm (x - a0) i then
            Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L0.symm (x - a0) i))
          else 0)))) :
    ∃ L : E m ≃ₗ[ℝ] E m, ∃ a : E m,
      ∀ᵐ x ∂volume, f x = |LinearMap.det L.toLinearMap|⁻¹ *
        (if ∀ i : Fin m, 0 ≤ L.symm (x - a) i then
          Real.exp (-Finset.sum Finset.univ (fun i : Fin m => L.symm (x - a) i))
        else 0) := by
  let e := P.toContinuousLinearEquiv
  let e0 := L0.toContinuousLinearEquiv
  have hlaw' : Measure.map (fun x => e (x - b))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal (affineDensity e0 a0 productExpDensity x)) := by
    simpa [affineDensity, productExpDensity_eq, e, e0] using hlaw
  have h := ae_eq_affineDensity_of_map_eq hf0 hf
    (affineDensity_nonneg e0 a0 productExpDensity_nonneg)
    (integrable_affineDensity e0 a0 (integrable_productExpDensity m)) e b hlaw'
  rw [affineDensity_comp] at h
  refine ⟨L0.trans P.symm, b + P.symm a0, ?_⟩
  filter_upwards [h] with x hx
  simpa [affineDensity, productExpDensity_eq, e, e0] using hx

end Submission.Obl.Entropy__affine_limit_density
