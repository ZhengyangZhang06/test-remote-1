import Mathlib

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tensor symmetry behind the cofactor divergence identity. -/
lemma inverse_derivative_contraction (A : Matrix ι ι ℝ) (B : ι → Matrix ι ι ℝ)
    (hB : ∀ s a b, B s a b = B b a s) (r : ι) :
    (∑ s, (A * B s * A) s r) = ∑ b, (A * B b).trace * A b r := by
  simp only [Matrix.mul_apply, Matrix.trace, Matrix.diag, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  rw [hB s a b]

/-- Multiplying the first log-Jacobian equation by the inverse cancels the drift. -/
lemma first_equation_contraction (J A : Matrix ι ι ℝ) (hJA : J * A = 1)
    (g x t : ι → ℝ) (ht : ∀ b, t b = ∑ u, g u * J u b - x b) (r : ι) :
    (∑ b, t b * A b r) + (∑ b, x b * A b r) = g r := by
  simp_rw [ht, sub_mul, Finset.sum_sub_distrib]
  rw [sub_add_cancel]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (∑ u, g u * (J * A) u r) = _
  rw [hJA]
  change (∑ u, g u * (if u = r then 1 else 0)) = _
  simp

lemma divergence_sum_algebra (P Q R : ι → ι → ℝ) (x h : ι → ℝ) :
    (∑ s, ∑ r, ((Q s r * h r + P s r * R s r) - x s * P s r * h r)) =
      (∑ s, ∑ r, P s r * R s r) +
      ∑ r, (((∑ s, Q s r) - (∑ s, x s * P s r)) * h r) := by
  simp_rw [sub_mul, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun r s => Q s r * h r),
    Finset.sum_comm (f := fun r s => x s * P s r * h r)]
  ring

end Submission.Obl.Entropy__transport_finite_jacobian_energy
