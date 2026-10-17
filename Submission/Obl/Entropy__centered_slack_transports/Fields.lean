import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__centered_slack_transports

variable {m : ℕ}

/-- A continuous bounded matrix field has Gaussian square-integrable entries. -/
theorem field_memLp {A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hc : ∀ i j, Continuous (fun x => A x i j))
    (hb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) (i j : Fin m) :
    MemLp (fun x => A x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨R, _, hR⟩ := hb
  exact MemLp.of_bound (hc i j).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hR x i j)

/-- Taking scalar Gaussian first moments preserves symmetry. -/
theorem coefficient_isHermitian
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).IsHermitian) (r : Fin m) :
    (Matrix.of fun i j => ∫ x, x r * A x i j
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
  congr 1
  funext x
  have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M i j) (hA x)
  simpa only [Matrix.conjTranspose_apply, star_trivial] using congrArg (x r * ·) h

/-- Values on the coordinate basis determine a linear derivative in every direction. -/
theorem derivative_from_basis
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (D : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hD : ∀ x i j, D x i j = (fderiv ℝ G x (PiLp.single 2 j (1 : ℝ))) i)
    (x v : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (fderiv ℝ G x v) i = ∑ j, D x i j * v j := by
  have hv : v = ∑ j : Fin m, v j • PiLp.single 2 j (1 : ℝ) := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v).symm
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hD x i j, mul_comm]

end Submission.Obl.Entropy__centered_slack_transports
