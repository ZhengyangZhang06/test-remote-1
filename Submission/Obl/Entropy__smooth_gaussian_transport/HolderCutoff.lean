import Submission.Obl.Entropy__smooth_gaussian_transport.UniformBoundedHolder

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem bilinear_sub_norm_le {Y Z W : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : Y →L[ℝ] Z →L[ℝ] W) (p r : Y) (q s : Z) :
    ‖B p q - B r s‖ ≤ ‖B‖ * (‖p‖ * ‖q - s‖ + ‖p - r‖ * ‖s‖) := by
  have he : B p q - B r s = B p (q - s) + B (p - r) s := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖B p (q - s)‖ + ‖B (p - r) s‖ := norm_add_le _ _
    _ ≤ ‖B p‖ * ‖q - s‖ + ‖B (p - r)‖ * ‖s‖ := add_le_add ((B p).le_opNorm _) ((B (p - r)).le_opNorm _)
    _ ≤ (‖B‖ * ‖p‖) * ‖q - s‖ + (‖B‖ * ‖p - r‖) * ‖s‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
    _ = _ := by ring

/-- Cut off a uniformly bounded Hölder family on a neighborhood of a fixed
compact support. No regularity away from that neighborhood is needed. -/
theorem uniformBoundedHolder_cutoff_bilinear {ι X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ψ : X → Y} {f : ι → X → Z} {K : Set X} {M C r α : ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hthick : ∀ x ∈ tsupport ψ, ∀ y, ‖x - y‖ < r → y ∈ K)
    (hb : ∀ i x, x ∈ K → ‖f i x‖ ≤ M)
    (hm : ∀ i x, x ∈ K → ∀ y, y ∈ K → ‖f i x - f i y‖ ≤ C * ‖x - y‖ ^ α)
    (B : Y →L[ℝ] Z →L[ℝ] W) :
    UniformBoundedHolder α (fun i x => B (ψ x) (f i x)) := by
  obtain ⟨A, D, hA, hD, hψb, hψm⟩ := compact_c1_bounded_holder hψ hψc hα hα1
  let N : ℝ := ‖B‖ * A * M
  let L : ℝ := ‖B‖ * (A * C + D * M)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hs (i : ι) : Function.support (fun x => B (ψ x) (f i x)) ⊆ tsupport ψ := by
    intro x hx
    apply subset_closure
    intro he
    apply hx
    simp only [he, map_zero, zero_apply]
  have hb' (i : ι) (x : X) : ‖B (ψ x) (f i x)‖ ≤ N := by
    by_cases hx : ψ x = 0
    · simpa only [hx, map_zero, zero_apply, norm_zero] using hN
    · have hxK := hthick x (subset_closure hx) x (by simpa only [sub_self, norm_zero] using hr)
      calc
        _ ≤ ‖B (ψ x)‖ * ‖f i x‖ := (B (ψ x)).le_opNorm _
        _ ≤ (‖B‖ * A) * M := mul_le_mul
          ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hψb x) (norm_nonneg B)))
          (hb i x hxK) (norm_nonneg _) (by positivity)
  have hm' (i : ι) (x : X) (hx : x ∈ tsupport ψ) (y : X) (hxy : ‖x - y‖ < r) :
      ‖B (ψ x) (f i x) - B (ψ y) (f i y)‖ ≤ L * ‖x - y‖ ^ α := by
    have hxK := hthick x hx x (by simpa only [sub_self, norm_zero] using hr)
    have hyK := hthick x hx y hxy
    calc
      _ ≤ ‖B‖ * (‖ψ x‖ * ‖f i x - f i y‖ + ‖ψ x - ψ y‖ * ‖f i y‖) := bilinear_sub_norm_le B _ _ _ _
      _ ≤ ‖B‖ * (A * (C * ‖x - y‖ ^ α) + (D * ‖x - y‖ ^ α) * M) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        exact add_le_add (mul_le_mul (hψb x) (hm i x hxK y hyK) (norm_nonneg _) hA.le)
          (mul_le_mul (hψm x y) (hb i y hyK) (norm_nonneg _) (by positivity))
      _ = _ := by dsimp only [L]; ring
  refine ⟨N, L + 2 * N / r ^ α, hN, by positivity, hb', ?_⟩
  intro i
  exact global_holder_of_near_support hN hL hr hα.le (hb' i) (hs i) (hm' i)

end Submission.Obl.Entropy__smooth_gaussian_transport
