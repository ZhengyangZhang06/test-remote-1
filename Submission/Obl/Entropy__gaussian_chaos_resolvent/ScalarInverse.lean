import Submission.Obl.Entropy__gaussian_chaos_resolvent.Resolvent

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

@[simp] theorem hermiteFunction_zero (x : ℝ) : hermiteFunction 0 x = 1 := by
  simp [hermiteFunction]

@[simp] theorem hermiteFunction_one (x : ℝ) : hermiteFunction 1 x = x := by
  simp [hermiteFunction]

@[simp] theorem hermiteEuclidean_zero {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    hermiteEuclidean 0 x = 1 := by
  simp [hermiteEuclidean, hermiteTensor]

@[simp] theorem hermiteEuclidean_raise_zero {m : ℕ} (r : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) : hermiteEuclidean (raiseIndex 0 r) x = x r := by
  classical
  unfold hermiteEuclidean hermiteTensor
  rw [Finset.prod_eq_single r]
  · simp
  · intro j _ hj
    simp [raiseIndex, Function.update_of_ne hj]
  · simp

theorem inner_Lp_toLp_real {m : ℕ} (f : GaussianL2 m)
    {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) :
    inner ℝ f (hg.toLp g) = ∫ x, f x * g x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [hx, mul_comm]

theorem norm_Lp_sq {m : ℕ} (f : GaussianL2 m) :
    ‖f‖^2 = ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

/-- The Hermite inverse has weak divergence `f`, with the sharp second-chaos bounds. -/
theorem scalar_inverse_estimates {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Differentiable ℝ f)
    (hf2 : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hdf2 : ∀ r : Fin m, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hmean : (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0)
    (hfirst : ∀ r : Fin m, (∫ x, x r * f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0) :
    ∃ v : Fin m → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ r, MemLp (v r) 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      (∀ z : EuclideanSpace ℝ (Fin m) → ℝ, Differentiable ℝ z →
        MemLp z 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) →
        (∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2
          (stdGaussian (EuclideanSpace ℝ (Fin m)))) →
        (∫ x, f x * z x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
          ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))
            ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
      (∑ r, ∫ x, v r x * fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
          ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ∧
      (∑ r, ∫ x, (v r x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
        (∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) / 2 ∧
      2 * (∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
        ∑ r, ∫ x, (fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))^2
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  let F : GaussianL2 m := hf2.toLp f
  let D : Fin m → GaussianL2 m := fun r => (hdf2 r).toLp _
  let V : Fin m → GaussianL2 m := fun r => resolventComponent (D r)
  have hF0 : gaussianCoeff F 0 = 0 := by
    simpa [F, gaussianCoeff_toLp] using hmean
  have hD (r a) : gaussianCoeff (D r) a =
      Real.sqrt (a r + 1 : ℝ) * gaussianCoeff F (raiseIndex a r) :=
    gaussianCoeff_deriv r hf hf2 (hdf2 r) a
  have hD0 (r) : gaussianCoeff (D r) 0 = 0 := by
    rw [hD]
    simp only [Pi.zero_apply, Nat.cast_zero, zero_add, Real.sqrt_one, one_mul]
    simpa [F, gaussianCoeff_toLp, mul_comm] using hfirst r
  have hcross : (∑ r, inner ℝ (V r) (D r)) = ‖F‖^2 := by
    rw [sum_resolvent_inner_eq F F D D hF0 hD hD, real_inner_self_eq_norm_sq]
  have hnorm : (∑ r, ‖V r‖^2) ≤ (1/2 : ℝ)*‖F‖^2 := by
    calc
      _ ≤ ∑ r, (1/2 : ℝ)*inner ℝ (V r) (D r) :=
        Finset.sum_le_sum (fun r _ => resolvent_norm_sq_le (D r) (hD0 r))
      _ = _ := by rw [← Finset.mul_sum, hcross]
  have hgap : 2*‖F‖^2 ≤ ∑ r, ‖D r‖^2 := by
    have hh := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => resolvent_inner_le (D r) (hD0 r))
    rw [hcross, ← Finset.mul_sum] at hh
    linarith
  refine ⟨fun r x => V r x, fun r => Lp.memLp (V r), ?_, ?_, ?_, ?_⟩
  · intro z hz hz2 hdz2
    let E : Fin m → GaussianL2 m := fun r => (hdz2 r).toLp _
    have hh := sum_resolvent_inner_eq F (hz2.toLp z) D E hF0 hD
      (fun r a => gaussianCoeff_deriv r hz hz2 (hdz2 r) a)
    rw [show inner ℝ F (hz2.toLp z) = ∫ x, f x*z x
      ∂stdGaussian (EuclideanSpace ℝ (Fin m)) from inner_toLp_real hf2 hz2] at hh
    simp only [E, inner_Lp_toLp_real] at hh
    exact hh.symm
  · simpa only [D, inner_Lp_toLp_real, F, norm_toLp_sq] using hcross
  · rw [show ‖F‖^2 = ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))
      from norm_toLp_sq hf2] at hnorm
    simpa only [norm_Lp_sq, one_div_mul_eq_div] using hnorm
  · simpa only [F, D, norm_toLp_sq] using hgap

theorem memLp_compact_coord_deriv {m : ℕ} {z : EuclideanSpace ℝ (Fin m) → ℝ}
    (hz : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z) (hzc : HasCompactSupport z)
    (r : Fin m) : MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact (hz.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact (hzc.fderiv ℝ).comp_left (g := fun L => L (PiLp.single 2 r (1 : ℝ))) rfl

theorem second_chaos_inverse (m : ℕ) (_hm : 1 ≤ m) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hf2 : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hdf2 : ∀ r : Fin m, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hmean : (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0)
    (hfirst : ∀ r : Fin m, (∫ x, x r * f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0) :
    ∃ v : Fin m → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ r, MemLp (v r) 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      (∀ z : EuclideanSpace ℝ (Fin m) → ℝ,
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
        (∫ x, f x * z x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
          ∑ r, ∫ x, v r x * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))
            ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
      (∑ r, ∫ x, v r x * fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))
        ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
          ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m)) ∧
      (∑ r, ∫ x, (v r x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
        (∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) / 2 := by
  obtain ⟨v, hv, hdiv, hcross, hnorm, _⟩ :=
    scalar_inverse_estimates (hf.differentiable (by norm_num)) hf2 hdf2 hmean hfirst
  refine ⟨v, hv, ?_, hcross, hnorm⟩
  intro z hz hzc
  exact hdiv z (hz.differentiable (by norm_num))
    (hz.continuous.memLp_of_hasCompactSupport hzc) (memLp_compact_coord_deriv hz hzc)

theorem second_chaos_gap (m : ℕ) (_hm : 1 ≤ m) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hf2 : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hdf2 : ∀ r : Fin m, MemLp (fun x => fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hmean : (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0)
    (hfirst : ∀ r : Fin m, (∫ x, x r * f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0) :
    2 * (∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤
      ∑ r, ∫ x, (fderiv ℝ f x (PiLp.single 2 r (1 : ℝ)))^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  obtain ⟨_, _, _, _, _, hgap⟩ :=
    scalar_inverse_estimates (hf.differentiable (by norm_num)) hf2 hdf2 hmean hfirst
  exact hgap

end Submission.Obl.Entropy__gaussian_chaos_resolvent
