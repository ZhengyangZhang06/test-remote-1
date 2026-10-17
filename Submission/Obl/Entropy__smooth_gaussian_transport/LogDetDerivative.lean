import Submission.Obl.Entropy__smooth_gaussian_transport.SmoothLogDet

open Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem eventually_positive_symmetric_line {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : B.toLinearMap.IsSymmetric) :
    ∀ᶠ t : ℝ in 𝓝 0, (operatorMatrix (A + t • B)).PosDef := by
  have hAp : A.toLinearMap.IsPositive :=
    (LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp hA.posSemidef
  have hd : 0 < A.det := by simpa only [operatorMatrix_det] using hA.det_pos
  obtain ⟨δ, hδ, hb⟩ := uniform_positive_lower_bound (L := ‖A‖) hd
  have hbase := hb A le_rfl hAp.1 hAp.2 le_rfl
  have hc : Continuous (fun t : ℝ => (A + t • B).det) :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hzB : (0 : ℝ) • B = 0 := by ext v; simp
  have hz : A + (0 : ℝ) • B = A := by rw [hzB, add_zero]
  have hne : ∀ᶠ t : ℝ in 𝓝 0, (A + t • B).det ≠ 0 := by
    have hn : (A + (0 : ℝ) • B).det ≠ 0 := by rw [hz]; exact hd.ne'
    exact hc.continuousAt.eventually_ne hn
  have hnorm : ∀ᶠ t : ℝ in 𝓝 0, ‖t • B‖ < δ := by
    have ht : Tendsto (fun t : ℝ => ‖t • B‖) (𝓝 0) (𝓝 0) := by
      have hn : Continuous (fun t : ℝ => ‖t • B‖) := by fun_prop
      simpa only [hzB, norm_zero] using (hn.tendsto (0 : ℝ))
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hne, hnorm] with t htd htn
  apply operatorMatrix_posDef
  · exact hAp.1.add (hB.smul (by simp))
  · intro v
    have hnormv : |inner ℝ ((t • B) v) v| ≤ ‖t • B‖ * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖(t • B) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖t • B‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((t • B).le_opNorm v) (norm_nonneg v)
        _ = _ := by ring
    have hlo := (neg_abs_le (inner ℝ ((t • B) v) v)).trans'
      (neg_le_neg hnormv)
    change 0 ≤ inner ℝ (A v + (t • B) v) v
    rw [inner_add_left]
    nlinarith [hbase v, sq_nonneg ‖v‖, mul_le_mul_of_nonneg_right htn.le (sq_nonneg ‖v‖)]
  · exact htd

/-- Jacobi's formula on symmetric directions, obtained from the supporting
planes of log det and differentiability of the determinant polynomial. -/
theorem hasDerivAt_log_det_line_zero {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : B.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ => Real.log (A + t • B).det) (linearizedTrace A B) 0 := by
  let f : ℝ → ℝ := fun t => Real.log (A + t • B).det
  have hdA : A.det ≠ 0 := by simpa only [operatorMatrix_det] using hA.det_pos.ne'
  have hz : A + (0 : ℝ) • B = A := by ext v; simp
  have hdiff : DifferentiableAt ℝ f 0 := by
    apply (ContDiffAt.differentiableAt (n := 1) ?_ one_ne_zero)
    have hc : ContDiffAt ℝ 1 (fun t : ℝ => A + t • B) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    apply (log_det_contDiffAt (n := 1) (by rw [hz]; exact hdA)).comp 0 hc
  have hmax : IsLocalMax (fun t => f t - t * linearizedTrace A B) 0 := by
    filter_upwards [eventually_positive_symmetric_line hA hB] with t ht
    have hle := log_det_sub_le_linearizedTrace hA ht
    have he : A + t • B - A = t • B := by abel
    rw [he, linearizedTrace_smul] at hle
    simp only [f, hz, zero_mul, sub_zero]
    linarith
  have hd : HasDerivAt (fun t => f t - t * linearizedTrace A B)
      (deriv f 0 - linearizedTrace A B) 0 := by
    convert! hdiff.hasDerivAt.sub ((hasDerivAt_id (0 : ℝ)).mul_const (linearizedTrace A B)) using 1 <;> simp
  have he : deriv f 0 = linearizedTrace A B := sub_eq_zero.mp (hmax.hasDerivAt_eq_zero hd)
  simpa only [he] using hdiff.hasDerivAt

theorem hasDerivAt_log_det_line {m : ℕ} {A B : E m →L[ℝ] E m} {t : ℝ}
    (hA : (operatorMatrix (A + t • B)).PosDef) (hB : B.toLinearMap.IsSymmetric) :
    HasDerivAt (fun s : ℝ => Real.log (A + s • B).det)
      (linearizedTrace (A + t • B) B) t := by
  have hd := hasDerivAt_log_det_line_zero hA hB
  have hd' : HasDerivAt (fun r : ℝ => Real.log (A + t • B + r • B).det)
      (linearizedTrace (A + t • B) B) (t - t) := by simpa only [sub_self] using hd
  have hcomp := hd'.comp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
  convert! hcomp using 1
  · ext s
    congr 2
    module
  · simp

end Submission.Obl.Entropy__smooth_gaussian_transport
