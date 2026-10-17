import Submission.Obl.Entropy__equality_cases.GaussianPoincare

set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.Entropy__equality_cases

open MeasureTheory ProbabilityTheory
open scoped Topology

/-- The squared operator norm is bounded by the sum of squared coordinate entries. -/
theorem euclidean_clm_norm_sq_le_entries {m n : ℕ}
    (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖D‖ ^ 2 ≤ ∑ i, ∑ j, (D (PiLp.single 2 j (1 : ℝ)) i) ^ 2 := by
  let S : ℝ := ∑ i, ∑ j, (D (PiLp.single 2 j (1 : ℝ)) i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have happ (v : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
      D v i = ∑ j, (D (PiLp.single 2 j (1 : ℝ)) i) * v j := by
    have hv : ∑ j : Fin m, v j • PiLp.single 2 j (1 : ℝ) = v := by
      ext j
      simp [Pi.single_apply]
    calc
      _ = (D (∑ j : Fin m, v j • PiLp.single 2 j (1 : ℝ))) i := by rw [hv]
      _ = _ := by simp [map_sum, mul_comm]
  have hs (v : EuclideanSpace ℝ (Fin m)) : ‖D v‖ ^ 2 ≤ S * ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, happ v]
    calc
      _ ≤ ∑ i : Fin n, (∑ j : Fin m, (D (PiLp.single 2 j (1 : ℝ)) i) ^ 2) *
          (∑ j : Fin m, (v j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [← Finset.sum_mul]
  have hnorm : ‖D‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hv := hs v
    have hpow : ‖D v‖ ^ 2 ≤ (Real.sqrt S * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS]
      exact hv
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hpow
  have := pow_le_pow_left₀ (norm_nonneg D) hnorm 2
  simpa only [Real.sq_sqrt hS] using this

/-- Coordinate form of the finite-constant Gaussian Poincare estimate. -/
theorem gaussian_poincare_matrix {m n : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ 1 f) (hmem : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hm : ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) = 0)
    (D : EuclideanSpace ℝ (Fin m) → Matrix (Fin n) (Fin m) ℝ)
    (hD : ∀ i j, MemLp (fun x => D x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hJac : ∀ x v i, (fderiv ℝ f x v) i = ∑ j, D x i j * v j) :
    (∫ x, ‖f x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
      ((Real.pi / 2) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) *
      ∫ x, ∑ i, ∑ j, (D x i j) ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hentry (x : EuclideanSpace ℝ (Fin m)) (i : Fin n) (j : Fin m) :
      (fderiv ℝ f x) (PiLp.single 2 j (1 : ℝ)) i = D x i j := by
    rw [hJac]
    simp
  have hbound (x : EuclideanSpace ℝ (Fin m)) :
      ‖fderiv ℝ f x‖ ^ 2 ≤ ∑ i, ∑ j, (D x i j) ^ 2 := by
    simpa only [hentry] using euclidean_clm_norm_sq_le_entries (fderiv ℝ f x)
  have henergy : Integrable (fun x => ∑ i, ∑ j, (D x i j) ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hD i j).integrable_sq))
  have hDi : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ := by
    apply henergy.mono' (((hf.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => by simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hbound x)
  have hp := gaussian_poincare_finite hf integral_id_stdGaussian hmem hm hDi
  apply hp.trans
  apply mul_le_mul_of_nonneg_left (integral_mono hDi henergy hbound)
  exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _))

/-- A single positive constant works for all centered maps in a fixed dimension. -/
theorem exists_gaussian_poincare_constant (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∀ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 f → MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) →
      (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0 →
      ∀ D : EuclideanSpace ℝ (Fin m) → Matrix (Fin n) (Fin m) ℝ,
      (∀ i j, MemLp (fun x => D x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) →
      (∀ x v i, (fderiv ℝ f x v) i = ∑ j, D x i j * v j) →
      (∫ x, ‖f x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
        K * ∫ x, ∑ i, ∑ j, (D x i j) ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let K := (Real.pi / 2) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ^ 2
    ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _))
  refine ⟨K + 1, by positivity, ?_⟩
  intro n f hf hmem hm D hD hJac
  apply (gaussian_poincare_matrix hf hmem hm D hD hJac).trans
  exact mul_le_mul_of_nonneg_right (show K ≤ K + 1 by linarith)
    (integral_nonneg (fun x => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg _))))

end Submission.Obl.Entropy__equality_cases
