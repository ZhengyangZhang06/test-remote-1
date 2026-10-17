import Mathlib

/-! Uniform scalar convergence passes to functional calculus on bounded Hermitian fields. -/

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma continuousOn_matrix_spectrum (f : ℝ → ℝ) (A : Matrix n n ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

/-- Uniform scalar convergence on a spectral bound gives uniform matrix convergence. -/
theorem tendstoUniformlyOn_cfc_of_bound
    {ι α : Type*} {l : Filter ι} {s : Set α}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} (A : α → Matrix n n ℝ)
    {R : ℝ} (hA : ∀ x ∈ s, (A x).IsHermitian)
    (hbound : ∀ x ∈ s, ‖A x‖ ≤ R)
    (hlim : TendstoUniformlyOn f g l (Metric.closedBall 0 R)) :
    TendstoUniformlyOn (fun i x ↦ cfc (f i) (A x)) (fun x ↦ cfc g (A x)) l s := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim (ε / 2) (by positivity)] with i hi x hx
  rw [dist_eq_norm, ← cfc_sub g (f i) (A x)
    (continuousOn_matrix_spectrum _ _) (continuousOn_matrix_spectrum _ _)]
  apply lt_of_le_of_lt (norm_cfc_le (by positivity : 0 ≤ ε / 2) ?_) (by linarith)
  intro t ht
  have htR : t ∈ Metric.closedBall (0 : ℝ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (IsometricContinuousFunctionalCalculus.norm_spectrum_le (A x) ht (hA x hx)).trans (hbound x hx)
  have hb := hi t htR
  rw [dist_eq_norm] at hb
  exact hb.le

/-- The same convergence, expressed as Jacobians on Euclidean space. -/
theorem tendstoUniformlyOn_cfc_clm_of_bound
    {ι α : Type*} {l : Filter ι} {s : Set α}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} (A : α → Matrix n n ℝ)
    {R : ℝ} (hA : ∀ x ∈ s, (A x).IsHermitian)
    (hbound : ∀ x ∈ s, ‖A x‖ ≤ R)
    (hlim : TendstoUniformlyOn f g l (Metric.closedBall 0 R)) :
    TendstoUniformlyOn
      (fun i x ↦ Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (cfc (f i) (A x)))
      (fun x ↦ Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (cfc g (A x))) l s := by
  have hu : UniformContinuous (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) := by
    apply Isometry.uniformContinuous
    intro A B
    simp only [edist_dist, dist_eq_norm, ← map_sub, Matrix.l2_opNorm_toEuclideanCLM]
  exact hu.comp_tendstoUniformlyOn (tendstoUniformlyOn_cfc_of_bound A hA hbound hlim)

end Submission.Obl.Entropy__linear_jacobian_rigidity
