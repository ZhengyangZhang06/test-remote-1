import Submission.Obl.Entropy__smooth_gaussian_transport.LinearizedDeterminant
import Submission.Obl.Entropy__smooth_gaussian_transport.UniformEllipticity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem operatorMatrix_continuous {m : ℕ} :
    Continuous (operatorMatrix : (E m →L[ℝ] E m) → Matrix (Fin m) (Fin m) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [operatorMatrix, LinearMap.toMatrix_apply]
  change Continuous (fun A : E m →L[ℝ] E m =>
    (A ((EuclideanSpace.basisFun (Fin m) ℝ) j)) i)
  fun_prop

theorem operatorMatrix_injective {m : ℕ} :
    Function.Injective (operatorMatrix : (E m →L[ℝ] E m) → Matrix (Fin m) (Fin m) ℝ) := by
  intro A B h
  have he : A.toLinearMap = B.toLinearMap := (LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis).injective h
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun he v

theorem linearizedTrace_zero {m : ℕ} (A : E m →L[ℝ] E m) : linearizedTrace A 0 = 0 := by
  simp only [linearizedTrace, operatorMatrix, ContinuousLinearMap.toLinearMap_zero,
    map_zero, Matrix.mul_zero, Matrix.trace_zero]

theorem linearizedTrace_pos {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : (operatorMatrix A).PosDef) (hB : (operatorMatrix B).PosSemidef) (hB0 : B ≠ 0) :
    0 < linearizedTrace A B := by
  let S := (operatorMatrix A)⁻¹
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hA.inv.posSemidef.nonneg
  have hu : IsUnit R := (CFC.isUnit_sqrt_iff S hA.inv.posSemidef.nonneg).mpr hA.inv.isUnit
  have hRd : IsUnit R.det := hu.map (Matrix.detMonoidHom)
  have hpos : (R * operatorMatrix B * R).PosSemidef := by
    simpa only [hR.eq] using hB.conjTranspose_mul_mul_same R
  have htrace : Matrix.trace (R * operatorMatrix B * R) = linearizedTrace A B := by
    rw [Matrix.trace_mul_cycle, hRR]
    rfl
  have hne : R * operatorMatrix B * R ≠ 0 := by
    intro hz
    apply hB0
    apply operatorMatrix_injective
    have he : operatorMatrix B = 0 := by
      calc
        operatorMatrix B = R⁻¹ * (R * operatorMatrix B * R) * R⁻¹ := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRd, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRd, Matrix.mul_one]
        _ = 0 := by rw [hz]; simp
    simpa only [operatorMatrix, ContinuousLinearMap.toLinearMap_zero, map_zero] using he
  rw [← htrace]
  exact lt_of_le_of_ne hpos.trace_nonneg (Ne.symm (hpos.trace_eq_zero_iff.not.mpr hne))

theorem linearizedTrace_continuousAt {m : ℕ} {A B : E m →L[ℝ] E m}
    (hA : A.det ≠ 0) :
    ContinuousAt (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      linearizedTrace z.1 z.2) (A, B) := by
  have hl : Continuous (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) => operatorMatrix z.1) :=
    operatorMatrix_continuous.comp continuous_fst
  have hr : Continuous (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) => operatorMatrix z.2) :=
    operatorMatrix_continuous.comp continuous_snd
  have hnum : Continuous (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      Matrix.trace ((operatorMatrix z.1).adjugate * operatorMatrix z.2)) :=
    (hl.matrix_adjugate.matrix_mul hr).matrix_trace
  have hden : ContinuousAt (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) =>
      z.1.det⁻¹) (A, B) :=
    (ContinuousLinearMap.continuous_det.comp continuous_fst).continuousAt.inv₀ hA
  have he : (fun z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) => linearizedTrace z.1 z.2) =
      fun z => z.1.det⁻¹ * Matrix.trace ((operatorMatrix z.1).adjugate * operatorMatrix z.2) := by
    funext z
    simp only [linearizedTrace, Matrix.inv_def, Ring.inverse_eq_inv, operatorMatrix_det,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [he]
  exact hden.mul hnum.continuousAt

theorem isClosed_nonnegative_operators {m : ℕ} :
    IsClosed {B : E m →L[ℝ] E m | (operatorMatrix B).PosSemidef} := by
  simpa only [Matrix.nonneg_iff_posSemidef] using
    isClosed_le (continuous_const : Continuous (fun _ : E m →L[ℝ] E m =>
      (0 : Matrix (Fin m) (Fin m) ℝ))) operatorMatrix_continuous

/-- On a compact family of positive definite base Hessians, the linearized
trace is uniformly comparable to the norm of a nonnegative increment. -/
theorem uniform_linearizedTrace_bounds {m : ℕ} {S : Set (E m →L[ℝ] E m)}
    (hS : IsCompact S) (hpos : ∀ A ∈ S, (operatorMatrix A).PosDef) :
    ∃ δ Λ : ℝ, 0 < δ ∧ 0 < Λ ∧ ∀ A ∈ S, ∀ B : E m →L[ℝ] E m,
      (operatorMatrix B).PosSemidef →
      δ * ‖B‖ ≤ linearizedTrace A B ∧ linearizedTrace A B ≤ Λ * ‖B‖ := by
  let T : Set (E m →L[ℝ] E m) := {B | ‖B‖ = 1 ∧ (operatorMatrix B).PosSemidef}
  have hT : IsCompact T := by
    convert! (isCompact_sphere (0 : E m →L[ℝ] E m) 1).inter_right
      isClosed_nonnegative_operators using 1
    ext B
    simp only [T, Metric.mem_sphere, dist_zero_right, mem_inter_iff, mem_ofPred_eq]
  let Q : (E m →L[ℝ] E m) × (E m →L[ℝ] E m) → ℝ :=
    fun z => linearizedTrace z.1 z.2
  have hQc : ContinuousOn Q (S ×ˢ T) := fun z hz =>
    (linearizedTrace_continuousAt (by
      simpa only [operatorMatrix_det] using (hpos z.1 hz.1).det_pos.ne')).continuousWithinAt
  have hQpos (z : (E m →L[ℝ] E m) × (E m →L[ℝ] E m)) (hz : z ∈ S ×ˢ T) : 0 < Q z := by
    apply linearizedTrace_pos (hpos z.1 hz.1) hz.2.2
    intro he
    have hh := hz.2.1
    rw [he, norm_zero] at hh
    norm_num at hh
  obtain ⟨δ, Λ, hδ, hΛ, hbounds⟩ : ∃ δ Λ : ℝ, 0 < δ ∧ 0 < Λ ∧
      ∀ z ∈ S ×ˢ T, δ ≤ Q z ∧ Q z ≤ Λ := by
    by_cases hne : (S ×ˢ T).Nonempty
    · obtain ⟨z, hz, hzmin⟩ := (hS.prod hT).exists_isMinOn hne hQc
      obtain ⟨w, hw, hwmax⟩ := (hS.prod hT).exists_isMaxOn hne hQc
      refine ⟨Q z, max 1 (Q w), hQpos z hz, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
      exact fun y hy => ⟨hzmin hy, (hwmax hy).trans (le_max_right _ _)⟩
    · exact ⟨1, 1, zero_lt_one, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  refine ⟨δ, Λ, hδ, hΛ, ?_⟩
  intro A hA B hB
  by_cases hB0 : B = 0
  · simp only [hB0, norm_zero, mul_zero, linearizedTrace_zero, le_refl, and_self]
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hu : ‖‖B‖⁻¹ • B‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hp : (operatorMatrix (‖B‖⁻¹ • B)).PosSemidef := by
    simpa only [operatorMatrix, ContinuousLinearMap.toLinearMap_smul, map_smul] using
      hB.smul (inv_nonneg.mpr hn.le)
  have hh := hbounds (A, ‖B‖⁻¹ • B) ⟨hA, hu, hp⟩
  change δ ≤ linearizedTrace A (‖B‖⁻¹ • B) ∧
    linearizedTrace A (‖B‖⁻¹ • B) ≤ Λ at hh
  rw [linearizedTrace_smul] at hh
  have hlo := mul_le_mul_of_nonneg_left hh.1 hn.le
  have hhi := mul_le_mul_of_nonneg_left hh.2 hn.le
  have hcancel : ‖B‖ * (‖B‖⁻¹ * linearizedTrace A B) = linearizedTrace A B := by
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  rw [hcancel] at hlo hhi
  exact ⟨by simpa only [mul_comm] using hlo, by simpa only [mul_comm] using hhi⟩

/-- The linearized transport equation has locally uniform ellipticity and
bounded drift, although its Hessian coefficients are only measurable. -/
theorem brenier_ae_linearized_bounds {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ δ Λ M : ℝ, 0 < δ ∧ 0 < Λ ∧ 0 < M ∧ ∀ᵐ x ∂volume, x ∈ K →
      ‖gradient V (gradient φ x)‖ ≤ M ∧
      ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (fderiv ℝ (gradient φ) x) B ∧
        linearizedTrace (fderiv ℝ (gradient φ) x) B ≤ Λ * ‖B‖ := by
  let L := 10 * (1 / Real.sqrt a)
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hnorm (x : E m) : ‖fderiv ℝ (gradient φ) x‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨l, U, hl, _, hb⟩ := density_bounds_on_compact
    (brenier_alexandrov_continuous_density hm hV.continuous hφ hlaw)
    (fun x => mul_pos (Submission.Lib.EntropyRemainder.gaussianDensity_pos x) (Real.exp_pos _)) hK
  let S : Set (E m →L[ℝ] E m) := {A | ‖A‖ ≤ L ∧ (operatorMatrix A).PosSemidef ∧ l ≤ A.det}
  have hS : IsCompact S := by
    convert! (isCompact_closedBall (0 : E m →L[ℝ] E m) L).inter_right
      (isClosed_nonnegative_operators.inter
        (isClosed_le (continuous_const (y := l)) ContinuousLinearMap.continuous_det)) using 1
    ext A
    simp only [S, Metric.mem_closedBall, dist_zero_right, mem_inter_iff, mem_ofPred_eq]
  have hSpos (A : E m →L[ℝ] E m) (hA : A ∈ S) : (operatorMatrix A).PosDef := by
    apply hA.2.1.posDef_iff_det_ne_zero.mpr
    rw [operatorMatrix_det]
    exact (hl.trans_le hA.2.2).ne'
  obtain ⟨δ, Λ, hδ, hΛ, hbounds⟩ := uniform_linearizedTrace_bounds hS hSpos
  have hgradV : Continuous (gradient V) :=
    continuous_gradient_of_contDiff_one (hV.of_le (by norm_num))
  obtain ⟨M, hM, hMb⟩ := (hK.image (hgradV.comp hLip.continuous)).isBounded.exists_pos_norm_le
  refine ⟨δ, Λ, M, hδ, hΛ, hM, ?_⟩
  filter_upwards [brenier_ae_positive_hessian hm hV.continuous hφ hlaw] with x hx
  intro hxK
  refine ⟨hMb _ (mem_image_of_mem _ hxK), ?_⟩
  apply hbounds
  refine ⟨hnorm x, hx.2.1.posSemidef, ?_⟩
  rw [hx.2.2]
  exact (hb x hxK).1

end Submission.Obl.Entropy__smooth_gaussian_transport
