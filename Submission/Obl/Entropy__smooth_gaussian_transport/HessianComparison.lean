import Submission.Obl.Entropy__smooth_gaussian_transport.FiniteDirections

open Set Filter
open scoped Topology RealInnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The finite-direction control remains valid when the trace has a small
negative error. A positive multiple of the base Hessian absorbs that error. -/
theorem finite_directions_trace_control_error {m : ℕ} (hm : 1 ≤ m)
    {S : Set (E m →L[ℝ] E m)} (hS : IsCompact S)
    (hpos : ∀ A ∈ S, (operatorMatrix A).PosDef) :
    ∃ F : Finset (E m), (∀ v ∈ F, ‖v‖ = 1) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ A ∈ S, ∀ (B : E m →L[ℝ] E m) (ε : ℝ), B.toLinearMap.IsSymmetric →
        0 ≤ ε → -ε ≤ linearizedTrace A B →
        ‖B‖ ≤ C * ((∑ v ∈ F, max 0 (inner ℝ (B v) v)) + ε) := by
  classical
  obtain ⟨F, hF, C₀, hC₀, hcontrol⟩ := finite_directions_trace_control hS hpos
  obtain ⟨L, hL, hnorm⟩ := hS.isBounded.exists_pos_norm_le
  let D : ℝ := (C₀ * F.card + 1) * L
  let C : ℝ := C₀ + D + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  refine ⟨F, hF, C, hC, ?_⟩
  intro A hA B ε hB hε htr
  have hAs : A.toLinearMap.IsSymmetric :=
    ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp
      (hpos A hA).posSemidef).1
  let B' : E m →L[ℝ] E m := B + ε • A
  have hBs : B'.toLinearMap.IsSymmetric :=
    hB.add (LinearMap.IsSymmetric.smul (by rfl) hAs)
  have htr' : 0 ≤ linearizedTrace A B' := by
    dsimp only [B']
    rw [linearizedTrace_add, linearizedTrace_smul, linearizedTrace_self (hpos A hA)]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hmR)]
  have hb := hcontrol A hA B' hBs htr'
  have hsum : (∑ v ∈ F, max 0 (inner ℝ (B' v) v)) ≤
      (∑ v ∈ F, max 0 (inner ℝ (B v) v)) + (F.card : ℝ) * (ε * L) := by
    calc
      _ ≤ ∑ v ∈ F, (max 0 (inner ℝ (B v) v) + ε * L) := by
        apply Finset.sum_le_sum
        intro v hv
        have hav : inner ℝ (A v) v ≤ L := by
          calc
            _ ≤ ‖A v‖ * ‖v‖ := real_inner_le_norm _ _
            _ ≤ (‖A‖ * ‖v‖) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg v)
            _ = ‖A‖ := by rw [hF v hv]; ring
            _ ≤ L := hnorm A hA
        apply max_le (by positivity)
        simp only [B', add_apply, smul_apply, inner_add_left, real_inner_smul_left]
        exact add_le_add (le_max_right _ _) (mul_le_mul_of_nonneg_left hav hε)
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, nsmul_eq_mul]
  have hnormB : ‖B‖ ≤ ‖B'‖ + ε * L := by
    have he : B = B' - ε • A := by dsimp [B']; module
    calc
      ‖B‖ = ‖B' - ε • A‖ := congrArg norm he
      _ ≤ ‖B'‖ + ‖ε • A‖ := norm_sub_le _ _
      _ = ‖B'‖ + ε * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
      _ ≤ ‖B'‖ + ε * L := by gcongr; exact hnorm A hA
  have hsum0 : 0 ≤ ∑ v ∈ F, max 0 (inner ℝ (B v) v) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  calc
    ‖B‖ ≤ C₀ * (∑ v ∈ F, max 0 (inner ℝ (B' v) v)) + ε * L :=
      hnormB.trans (add_le_add hb le_rfl)
    _ ≤ C₀ * ((∑ v ∈ F, max 0 (inner ℝ (B v) v)) + (F.card : ℝ) * (ε * L)) + ε * L := by
      gcongr
    _ = C₀ * (∑ v ∈ F, max 0 (inner ℝ (B v) v)) + D * ε := by dsimp [D]; ring
    _ ≤ C * (∑ v ∈ F, max 0 (inner ℝ (B v) v)) + C * ε :=
      add_le_add (mul_le_mul_of_nonneg_right hC₀C hsum0) (mul_le_mul_of_nonneg_right hDC hε)
    _ = _ := by ring

/-- Concavity of log determinant converts the previous trace estimate into
an estimate for differences of positive definite Hessians. -/
theorem finite_directions_hessian_comparison {m : ℕ} (hm : 1 ≤ m)
    {S : Set (E m →L[ℝ] E m)} (hS : IsCompact S)
    (hpos : ∀ A ∈ S, (operatorMatrix A).PosDef) :
    ∃ F : Finset (E m), (∀ v ∈ F, ‖v‖ = 1) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ A ∈ S, ∀ B ∈ S,
        ‖B - A‖ ≤ C * ((∑ v ∈ F, max 0 (inner ℝ (B v) v - inner ℝ (A v) v)) +
          |Real.log B.det - Real.log A.det|) := by
  obtain ⟨F, hF, C, hC, hcontrol⟩ := finite_directions_trace_control_error hm hS hpos
  refine ⟨F, hF, C, hC, ?_⟩
  intro A hA B hB
  have hAs : A.toLinearMap.IsSymmetric :=
    ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp
      (hpos A hA).posSemidef).1
  have hBs : B.toLinearMap.IsSymmetric :=
    ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp
      (hpos B hB).posSemidef).1
  have hh := hcontrol A hA (B - A) |Real.log B.det - Real.log A.det|
    (hBs.sub hAs) (abs_nonneg _)
    ((neg_abs_le _).trans (log_det_sub_le_linearizedTrace (hpos A hA) (hpos B hB)))
  simpa only [sub_apply, inner_sub_left] using hh

end Submission.Obl.Entropy__smooth_gaussian_transport
