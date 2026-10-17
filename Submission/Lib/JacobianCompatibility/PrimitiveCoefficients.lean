import Submission.Lib.JacobianCompatibility.UniformJacobian
import Submission.Lib.JacobianCompatibility.MatrixLimits
import Submission.Lib.JacobianCompatibility.ScalarLimits

/-!
The first two homogeneous coefficients of a nonlinear matrix Jacobian are
Jacobians. Central differences avoid assuming differentiability of matrix CFC.
-/

namespace Submission.Lib.JacobianCompatibility

open Filter Set Asymptotics
open scoped Topology Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cfc_rescale_arg (q : ℝ → ℝ) (t : ℝ) (B : Matrix n n ℝ)
    (hB : B.IsHermitian) : cfc (fun z ↦ q (t * z)) B = cfc q (t • B) :=
  cfc_comp_const_mul t q B ((B.finite_real_spectrum.image _).continuousOn q) hB

/-- Scalars act linearly on the class of matrix functions which are Jacobians. -/
lemma hasPrimitive_cfc_smul
    (A : EuclideanSpace ℝ n → Matrix n n ℝ) {q : ℝ → ℝ}
    (h : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)))) (c : ℝ) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ c * q z) (A x))) := by
  have heq : (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ c * q z) (A x))) =
      (fun x ↦ c • Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x))) := by
    funext x
    rw [cfc_const_mul c q (A x) (continuousOn_matrix_spectrum _ _), map_smul]
  rw [heq]
  exact h.smul c

lemma hasPrimitive_cfc_sub
    (A : EuclideanSpace ℝ n → Matrix n n ℝ) {q r : ℝ → ℝ}
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x))))
    (hr : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc r (A x)))) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ q z - r z) (A x))) := by
  have heq : (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ q z - r z) (A x))) =
      (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc r (A x))) := by
    funext x
    rw [cfc_sub q r (A x) (continuousOn_matrix_spectrum _ _)
      (continuousOn_matrix_spectrum _ _), map_sub]
  rw [heq]
  exact hq.sub hr

lemma hasPrimitive_cfc_add
    (A : EuclideanSpace ℝ n → Matrix n n ℝ) {q r : ℝ → ℝ}
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x))))
    (hr : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc r (A x)))) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ q z + r z) (A x))) := by
  have heq : (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ q z + r z) (A x))) =
      (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc r (A x))) := by
    funext x
    rw [cfc_add (A x) q r (continuousOn_matrix_spectrum _ _)
      (continuousOn_matrix_spectrum _ _), map_add]
  rw [heq]
  exact hq.add hr

lemma hasPrimitive_cfc_const
    (A : EuclideanSpace ℝ n → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian) (c : ℝ) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc (fun _ ↦ c) (A x))) := by
  have heq : (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc (fun _ : ℝ ↦ c) (A x))) =
      (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (algebraMap ℝ (Matrix n n ℝ) c)) := by
    funext x
    rw [cfc_const (p := IsSelfAdjoint) c (A x) (hA x)]
  rw [heq]
  exact HasPrimitive.const _

lemma hasPrimitive_cfc_precomp_smul
    (A : EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    {q : ℝ → ℝ}
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)))) (t : ℝ) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ q (t * z)) (A x))) := by
  simpa only [map_smul, cfc_rescale_arg q t _ (hA _)] using hq.precomp_smul t

/-- Uniform limits of scalar functions preserve the Jacobian property for a
fixed Hermitian linear matrix field. -/
theorem hasPrimitive_cfc_of_uniformLimit
    (A : EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    {ι : Type*} {l : Filter ι} [NeBot l] {qseq : ι → ℝ → ℝ} {q : ℝ → ℝ}
    (hseq : ∀ i, HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc (qseq i) (A x))))
    (hlim : ∀ R, 0 ≤ R → TendstoUniformlyOn qseq q l (Metric.closedBall 0 R)) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x))) := by
  apply HasPrimitive.of_tendstoUniformlyOn_ball (l := l) _ hseq
  intro r
  apply tendstoUniformlyOn_cfc_clm_of_bound A (fun x _ ↦ hA x)
      (R := ‖A‖ * max r 0)
  · intro x hx
    apply (A.le_opNorm x).trans
    gcongr
    exact (by simpa using hx : ‖x‖ < r).le.trans (le_max_left _ _)
  · exact hlim _ (by positivity)

/-- The linear coefficient in the Taylor expansion of a matrix Jacobian is a Jacobian. -/
theorem hasPrimitive_cfc_linear_coefficient
    (A : EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    {q : ℝ → ℝ} {c : ℝ} (hqc : HasDerivAt q c 0)
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)))) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) ((2 * c) • A x)) := by
  have hp : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ (2 * c) * z ^ 1) (A x))) := by
    apply hasPrimitive_cfc_of_uniformLimit A hA
      (qseq := fun t z ↦ (t ^ 1)⁻¹ * (q (t * z) - q (-(t * z))))
      (l := 𝓝[≠] (0 : ℝ))
    · intro t
      apply hasPrimitive_cfc_smul
      have ht := hasPrimitive_cfc_precomp_smul A hA hq t
      have hnt := hasPrimitive_cfc_precomp_smul A hA hq (-t)
      simpa only [neg_mul] using hasPrimitive_cfc_sub A ht hnt
    · intro R hR
      exact tendstoUniformlyOn_div_pow_of_taylor (odd_difference_isLittleO hqc) hR
  have heq : ∀ x, cfc (fun z : ℝ ↦ (2 * c) * z ^ 1) (A x) = (2 * c) • A x := by
    intro x
    simpa only [pow_one] using cfc_const_mul_id (p := IsSelfAdjoint) (2 * c) (A x) (hA x)
  simpa only [heq] using hp

/-- The quadratic coefficient in the Taylor expansion of a matrix Jacobian is a Jacobian. -/
theorem hasPrimitive_cfc_quadratic_coefficient
    (A : EuclideanSpace ℝ n →L[ℝ] Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    {q : ℝ → ℝ} (hqc : ContDiff ℝ 2 q)
    (hq : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc q (A x)))) :
    HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (deriv (deriv q) 0 • (A x) ^ 2)) := by
  have hp : HasPrimitive (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cfc (fun z ↦ deriv (deriv q) 0 * z ^ 2) (A x))) := by
    apply hasPrimitive_cfc_of_uniformLimit A hA
      (qseq := fun t z ↦ (t ^ 2)⁻¹ * (q (t * z) + q (-(t * z)) - 2 * q 0))
      (l := 𝓝[≠] (0 : ℝ))
    · intro t
      apply hasPrimitive_cfc_smul
      have ht := hasPrimitive_cfc_precomp_smul A hA hq t
      have hnt := hasPrimitive_cfc_precomp_smul A hA hq (-t)
      have hc := hasPrimitive_cfc_const A hA (2 * q 0)
      simpa only [neg_mul] using
        hasPrimitive_cfc_sub A (hasPrimitive_cfc_add A ht hnt) hc
    · intro R hR
      exact tendstoUniformlyOn_div_pow_of_taylor (even_difference_isLittleO hqc) hR
  have heq : ∀ x, cfc (fun z ↦ deriv (deriv q) 0 * z ^ 2) (A x) =
      deriv (deriv q) 0 • (A x) ^ 2 := by
    intro x
    rw [cfc_const_mul _ _ _ (continuousOn_matrix_spectrum _ _), cfc_pow_id (p := IsSelfAdjoint) (R := ℝ) (A x) 2 (hA x)]
  simpa only [heq] using hp

end Submission.Lib.JacobianCompatibility
