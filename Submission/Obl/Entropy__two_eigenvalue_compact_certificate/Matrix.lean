import Mathlib

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

theorem quadratic_nonneg (A B C : ℝ) (hA : 0 < A) (hdet : 0 ≤ A*C-B^2)
    (u v : ℝ) : 0 ≤ A*u^2+2*B*u*v+C*v^2 := by
  have hh : 0 ≤ A*(A*u^2+2*B*u*v+C*v^2) := by
    nlinarith only [sq_nonneg (A*u+B*v), mul_nonneg hdet (sq_nonneg v)]
  exact nonneg_of_mul_nonneg_right hh hA

theorem rank_one_bound (p h v o E f D : ℝ) (hp : 0 < p)
    (hlead : 0 < h*p-D*E^2)
    (hdet : 0 ≤ p*(h*v-o^2)-D*(E^2*v-2*E*o*f+h*f*f)) (u w : ℝ) :
    (D/p)*(E*u+f*w)^2 ≤ h*u^2+2*o*u*w+v*w^2 := by
  have hd : 0 ≤ (h*p-D*E^2)*(v*p-D*f^2)-(o*p-D*E*f)^2 := by
    nlinarith only [mul_nonneg hp.le hdet]
  have hh := quadratic_nonneg (h*p-D*E^2) (o*p-D*E*f) (v*p-D*f^2) hlead hd u w
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  nlinarith only [hh]

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
