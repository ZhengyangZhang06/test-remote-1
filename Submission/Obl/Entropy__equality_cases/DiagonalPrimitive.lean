import Mathlib

namespace Submission.Obl.Entropy__equality_cases

/-- A diagonal Jacobian integrates to the coordinate primitives, up to translation.
This is the last differential step of the linear-field rigidity lemma. -/
theorem diagonal_jacobian_primitive {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (t q : ℝ → ℝ) (ht : ∀ s, HasDerivAt t (q s) s)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ^ 2 = 1)
    (hF : ∀ x, HasFDerivAt F
      ((Matrix.diagonal (fun i => q (σ i * x i))).toEuclideanLin.toContinuousLinearMap) x) :
    ∃ w : EuclideanSpace ℝ (Fin m), ∀ x i, F x i = σ i * t (σ i * x i) + w i := by
  let w : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (fun i => F 0 i - σ i * t 0)
  refine ⟨w, ?_⟩
  intro x i
  let p : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := EuclideanSpace.proj i
  have hcoord (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => F z i) (q (σ i * y i) • p) y := by
    convert! p.hasFDerivAt.comp y (hF y) using 1
    ext v
    simp [p, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  have hmodel (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => σ i * t (σ i * z i)) (q (σ i * y i) • p) y := by
    have h := ((ht (σ i * y i)).comp_hasFDerivAt y
      (p.hasFDerivAt.const_mul (σ i))).const_mul (σ i)
    convert! h using 1
    ext v
    simp only [smul_apply, smul_eq_mul]
    calc
      _ = σ i ^ 2 * (q (σ i * y i) * p v) := by rw [hσ i, one_mul]
      _ = _ := by ring
  have hz (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z => F z i - σ i * t (σ i * z i))
        (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) y := by
    simpa only [sub_self, Pi.sub_apply] using! (hcoord y).sub (hmodel y)
  have hconst := is_const_of_fderiv_eq_zero
    (fun y => (hz y).differentiableAt) (fun y => (hz y).fderiv) x 0
  change F x i = σ i * t (σ i * x i) + (F 0 i - σ i * t 0)
  simp only [PiLp.zero_apply, mul_zero] at hconst
  linarith

end Submission.Obl.Entropy__equality_cases
