import Submission.Obl.Entropy__gaussian_covariance_variational.Density
import Submission.Obl.Entropy__gaussian_covariance_variational.Matrix

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix

namespace Submission.Obl.Entropy__gaussian_covariance_variational

/-- The scalar analytic estimate used in the matrix covariance theorem. -/
def ScalarCovarianceBound (m : ℕ) : Prop :=
  let E := EuclideanSpace ℝ (Fin m)
  let γ := stdGaussian E
  ∀ F : E → ℝ, Differentiable ℝ F → MemLp F 2 γ →
    (∀ j, MemLp (fun x => fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) 2 γ) →
    ∀ a : Fin m → E → ℝ, ∀ b : Fin m → Fin m → E → ℝ,
    (∀ j, MemLp (a j) 2 γ) → (∀ r j, MemLp (b r j) 2 γ) →
    (∀ j z, ContDiff ℝ (⊤ : WithTop ENat) z → HasCompactSupport z →
      (∫ x, (a j x - fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) * z x ∂γ) =
        ∑ r, ∫ x, b r j x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)) ∂γ) →
    (∫ x, (F x - ∫ y, F y ∂γ)^2 ∂γ) ≤
      (∑ j, ∫ x, (a j x)^2 ∂γ) + ∑ r, ∑ j, ∫ x, (b r j x)^2 ∂γ

variable {m : ℕ}

/-- Constant row combinations preserve compact-test weak divergence identities. -/
lemma weak_row
    (J a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (b : Fin m → EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ i j, MemLp (fun x => J x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (ha : ∀ i j, MemLp (fun x => a x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hb : ∀ r i j, MemLp (fun x => b r x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hw : ∀ i j z, ContDiff ℝ (⊤ : WithTop ENat) z → HasCompactSupport z →
      (∫ x, (a x i j - J x i j) * z x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
        ∑ r, ∫ x, b r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)))
    (u : Fin m → ℝ) (j : Fin m) (z : EuclideanSpace ℝ (Fin m) → ℝ)
    (hz : ContDiff ℝ (⊤ : WithTop ENat) z) (hzs : HasCompactSupport z) :
    (∫ x, ((∑ i, u i * a x i j) - ∑ i, u i * J x i j) * z x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∑ r, ∫ x, (∑ i, u i * b r x i j) * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hzL : MemLp z 2 γ := hz.continuous.memLp_of_hasCompactSupport hzs
  have hdL (r : Fin m) : MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 γ :=
    ((hz.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hzs.fderiv_apply ℝ _)
  have he (x : EuclideanSpace ℝ (Fin m)) :
      ((∑ i, u i * a x i j) - ∑ i, u i * J x i j) * z x =
        ∑ i, u i * ((a x i j - J x i j) * z x) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
  simp_rw [he]
  erw [integral_finsetSum _ (fun i _ => (((ha i j).sub (hJ i j)).integrable_mul hzL).const_mul (u i))]
  simp only [Pi.sub_apply, Pi.mul_apply, integral_const_mul]
  simp_rw [hw _ _ z hz hzs, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [Finset.sum_mul, mul_assoc]
  erw [integral_finsetSum _ (fun i _ => ((hb r i j).integrable_mul (hdL r)).const_mul (u i))]
  simp only [integral_const_mul, Pi.mul_apply]

/-- Reduction of the density and matrix formulation to the scalar analytic bound. -/
theorem covariance_of_scalar (hs : ScalarCovarianceBound m)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hf2 : Integrable (fun x => f x * ‖x‖^2) volume)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hF : ContDiff ℝ 1 F)
    (hlaw : Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (J a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (b : Fin m → EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hJ : ∀ i j, MemLp (fun x => J x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hJF : ∀ x i j, J x i j = (fderiv ℝ F x (PiLp.single 2 j (1 : ℝ))) i)
    (ha : ∀ i j, MemLp (fun x => a x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hb : ∀ r i j, MemLp (fun x => b r x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hw : ∀ i j z, ContDiff ℝ (⊤ : WithTop ENat) z → HasCompactSupport z →
      (∫ x, (a x i j - J x i j) * z x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
        ∑ r, ∫ x, b r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)))
    (P : Matrix (Fin m) (Fin m) ℝ) (hP : P.PosDef) :
    (P * Submission.Lib.EntropyTools.densityCovariance f (∫ x, f x • x)).trace ≤
      (∫ x, ((a x).transpose * P * a x).trace ∂stdGaussian (EuclideanSpace ℝ (Fin m))) +
      ∑ r, ∫ x, ((b r x).transpose * P * b r x).trace
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hFlp := transport_memLp hf0 hf hf2 hF.continuous hlaw
  apply weighted_bound_of_quadratic_bound _ a b ha hb _ P hP
  intro u
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := ∑ i, u i • EuclideanSpace.proj i
  have hL (x : EuclideanSpace ℝ (Fin m)) : L x = ∑ i, u i * x i := by
    simp [L, EuclideanSpace.proj]
  have hd (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fun y => L (F y)) x (PiLp.single 2 j (1 : ℝ)) =
        ∑ i, u i * J x i j := by
    erw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.comp_apply, hL, hJF]
  have h := hs (fun x => L (F x)) (L.differentiable.comp (hF.differentiable (by simp)))
    (hFlp.continuousLinearMap_comp L)
    (fun j => by simpa only [hd] using memLp_row J hJ u j)
    (fun j x => ∑ i, u i * a x i j) (fun r j x => ∑ i, u i * b r x i j)
    (fun j => memLp_row a ha u j) (fun r j => memLp_row (b r) (hb r) u j)
    (fun j z hz hzs => by simpa only [hd] using weak_row J a b hJ ha hb hw u j z hz hzs)
  rw [Submission.Lib.EntropyTools.densityCovariance_quadratic hf0 hf hf2]
  convert h using 1
  rw [L.integral_comp_comm (hFlp.integrable (by norm_num)), transport_mean hf0 hf hF.continuous hlaw]
  simpa only [map_sub, hL, PiLp.sub_apply, Finset.sum_sub_distrib, mul_sub] using
    (transport_integral hf0 hf hF.continuous hlaw
      (g := fun x => (L (x - ∫ y, f y • y))^2) (by fun_prop)).symm


end Submission.Obl.Entropy__gaussian_covariance_variational
