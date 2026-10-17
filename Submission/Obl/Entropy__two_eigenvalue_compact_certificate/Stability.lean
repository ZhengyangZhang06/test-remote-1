import Mathlib

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- A contracting scalar differential equation accumulates only its forcing error. -/
theorem stable_forward_error {f f' c g : ℝ → ℝ} {a b E F : ℝ}
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hode : ∀ x ∈ Icc a b, f' x = -c x * f x + g x)
    (hc : ∀ x ∈ Icc a b, 0 < c x)
    (hg : ∀ x ∈ Icc a b, |g x| ≤ F)
    (hE : 0 < E) (hF : 0 ≤ F) (ha : |f a| ≤ E)
    {x : ℝ} (hx : x ∈ Icc a b) : |f x| ≤ E + F * (x-a) := by
  have helper (u u' v : ℝ → ℝ)
      (hd : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
      (ho : ∀ x ∈ Icc a b, u' x = -c x * u x + v x)
      (hv : ∀ x ∈ Icc a b, v x ≤ F) (hi : u a ≤ E) :
      u x ≤ E + F * (x-a) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f' := u') (B' := fun _ => F) (a := a) (b := b)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y ⟨hy.1, hy.2.le⟩).hasDerivWithinAt)
      (by simpa using hi)
      (fun y => by simpa using (((hasDerivAt_id y).sub_const a).const_mul F).const_add E)
      (fun y hy he => ?_) hx
    have hy' : y ∈ Icc a b := ⟨hy.1, hy.2.le⟩
    rw [ho y hy', he]
    have hpos : 0 < E + F*(y-a) := by nlinarith [mul_nonneg hF (sub_nonneg.mpr hy.1)]
    nlinarith [hc y hy', hv y hy']
  apply abs_le.mpr
  constructor
  · have hh := helper (fun y => -f y) (fun y => -f' y) (fun y => -g y)
        (fun y hy => (hderiv y hy).neg)
        (fun y hy => by rw [hode y hy]; ring)
        (fun y hy => by linarith [(abs_le.mp (hg y hy)).1]) (by linarith [(abs_le.mp ha).1])
    linarith
  · exact helper f f' g hderiv hode (fun y hy => le_of_abs_le (hg y hy)) (le_of_abs_le ha)

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
