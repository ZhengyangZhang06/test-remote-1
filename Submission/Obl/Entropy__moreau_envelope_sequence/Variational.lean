import Mathlib

noncomputable section
open Set Filter Topology
open scoped InnerProductSpace

namespace Submission.Obl.Entropy__moreau_envelope_sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma minimizer_variational {S : Set E} {V : E → ℝ} (hV : ConvexOn ℝ S V)
    {t : ℝ} (_ht : 0 < t) {x p : E} (hp : p ∈ S)
    (hmin : ∀ y ∈ S, V p + t / 2 * ‖x - p‖ ^ 2 ≤ V y + t / 2 * ‖x - y‖ ^ 2)
    {y : E} (hy : y ∈ S) :
    t * ⟪x - p, y - p⟫_ℝ ≤ V y - V p := by
  have hslope (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
      t * ⟪x - p, y - p⟫_ℝ ≤ V y - V p + t / 2 * s * ‖y - p‖ ^ 2 := by
    have hm := hmin ((1 - s) • p + s • y)
      (hV.1 hp hy (by linarith) hs.le (by ring))
    have hv := hV.2 hp hy (by linarith : 0 ≤ 1 - s) hs.le (by ring : 1 - s + s = 1)
    have he : x - ((1 - s) • p + s • y) = (x - p) - s • (y - p) := by module
    rw [he, norm_sub_sq_real (x - p) (s • (y - p)), real_inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs] at hm
    simp only [smul_eq_mul] at hv
    nlinarith
  have hlim : Tendsto (fun s : ℝ => V y - V p + t / 2 * s * ‖y - p‖ ^ 2)
      (𝓝[>] 0) (𝓝 (V y - V p)) := by
    have h : Continuous (fun s : ℝ => V y - V p + t / 2 * s * ‖y - p‖ ^ 2) := by
      fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with s hs1 hs
  exact hslope s hs hs1

lemma residual_firm {S : Set E} {V : E → ℝ} (hV : ConvexOn ℝ S V)
    {t : ℝ} (ht : 0 < t) {p : E → E} (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S →
      V (p x) + t / 2 * ‖x - p x‖ ^ 2 ≤ V y + t / 2 * ‖x - y‖ ^ 2)
    (x y : E) :
    ‖(x - p x) - (y - p y)‖ ^ 2 ≤ ⟪(x - p x) - (y - p y), x - y⟫_ℝ := by
  have h₁ := minimizer_variational hV ht (hp x) (hmin x) (hp y)
  have h₂ := minimizer_variational hV ht (hp y) (hmin y) (hp x)
  have hin : ⟪(x - p x) - (y - p y), p x - p y⟫_ℝ ≥ 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_sub_right] at h₁ h₂
    nlinarith
  have he : x - y = ((x - p x) - (y - p y)) + (p x - p y) := by abel
  conv_rhs => rw [he, inner_add_right, real_inner_self_eq_norm_sq]
  linarith

lemma residual_lipschitz {S : Set E} {V : E → ℝ} (hV : ConvexOn ℝ S V)
    {t : ℝ} (ht : 0 < t) {p : E → E} (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S →
      V (p x) + t / 2 * ‖x - p x‖ ^ 2 ≤ V y + t / 2 * ‖x - y‖ ^ 2)
    (x y : E) :
    ‖(x - p x) - (y - p y)‖ ≤ ‖x - y‖ := by
  have h := (residual_firm hV ht hp hmin x y).trans (real_inner_le_norm _ _)
  nlinarith [norm_nonneg ((x - p x) - (y - p y)), norm_nonneg (x - y)]

end Submission.Obl.Entropy__moreau_envelope_sequence
