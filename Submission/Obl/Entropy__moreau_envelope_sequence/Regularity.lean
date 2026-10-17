import Submission.Obl.Entropy__moreau_envelope_sequence.Variational

noncomputable section
open Set Filter Topology
open scoped InnerProductSpace

namespace Submission.Obl.Entropy__moreau_envelope_sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def envelope (V : E → ℝ) (t : ℝ) (p : E → E) (x : E) : ℝ :=
  V (p x) + t / 2 * ‖x - p x‖ ^ 2

variable {S : Set E} {V : E → ℝ} {t : ℝ} {p : E → E}

lemma envelope_remainder (hV : ConvexOn ℝ S V) (ht : 0 < t)
    (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S → envelope V t p x ≤ V y + t / 2 * ‖x - y‖ ^ 2)
    (x y : E) :
    0 ≤ envelope V t p y - envelope V t p x - t * ⟪x - p x, y - x⟫_ℝ ∧
    envelope V t p y - envelope V t p x - t * ⟪x - p x, y - x⟫_ℝ
      ≤ t / 2 * ‖y - x‖ ^ 2 := by
  constructor
  · have hv := minimizer_variational hV ht (hp x) (hmin x) (hp y)
    have he : y - p y = (x - p x) + ((y - x) - (p y - p x)) := by abel
    dsimp [envelope]
    rw [he, norm_add_sq_real, inner_sub_right]
    have hn : 0 ≤ t * ‖(y - x) - (p y - p x)‖ ^ 2 := by positivity
    nlinarith
  · have hm := hmin y (p x) (hp x)
    have he : y - p x = (x - p x) + (y - x) := by abel
    rw [he, norm_add_sq_real] at hm
    dsimp [envelope] at *
    linarith

lemma envelope_hasFDerivAt (hV : ConvexOn ℝ S V) (ht : 0 < t)
    (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S → envelope V t p x ≤ V y + t / 2 * ‖x - y‖ ^ 2)
    (x : E) :
    HasFDerivAt (envelope V t p) (t • innerSL ℝ (x - p x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ∀ᶠ h : E in 𝓝 0, ‖h‖ < 2 * c / t := by
    exact (continuous_norm.tendsto 0).eventually
      (Iio_mem_nhds (by simpa using div_pos (by positivity : 0 < 2 * c) ht))
  filter_upwards [hn] with h hh
  have hr := envelope_remainder hV ht hp hmin x (x + h)
  simp only [add_sub_cancel_left] at hr
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
    Real.norm_eq_abs, abs_of_nonneg hr.1]
  apply hr.2.trans
  have hs : t / 2 * ‖h‖ ≤ c := by
    have hh' := (lt_div_iff₀ ht).1 hh
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg h)]

lemma envelope_convex (hV : ConvexOn ℝ S V) (ht : 0 < t)
    (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S → envelope V t p x ≤ V y + t / 2 * ‖x - y‖ ^ 2) :
    ConvexOn ℝ Set.univ (envelope V t p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d hc hd hcd
  let z := c • x + d • y
  have hx := (envelope_remainder hV ht hp hmin z x).1
  have hy := (envelope_remainder hV ht hp hmin z y).1
  have he : c * ⟪z - p z, x - z⟫_ℝ + d * ⟪z - p z, y - z⟫_ℝ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have hz : c • (x - z) + d • (y - z) = 0 := by
      rw [smul_sub, smul_sub]
      have hcz : c • z + d • z = z := by rw [← add_smul, hcd, one_smul]
      calc
        c • x - c • z + (d • y - d • z) = (c • x + d • y) - (c • z + d • z) := by abel
        _ = 0 := by rw [hcz]; exact sub_self z
    rw [hz, inner_zero_right]
  change envelope V t p z ≤ c * envelope V t p x + d * envelope V t p y
  have he' := congrArg (fun r : ℝ => t * r) he
  have hq : (c + d) * envelope V t p z = envelope V t p z := by rw [hcd, one_mul]
  nlinarith only [mul_nonneg hc hx, mul_nonneg hd hy, he', hq]

lemma envelope_regular (hV : ConvexOn ℝ S V) (ht : 0 < t)
    (hp : ∀ x, p x ∈ S)
    (hmin : ∀ x y, y ∈ S → envelope V t p x ≤ V y + t / 2 * ‖x - y‖ ^ 2) :
    ContDiff ℝ 1 (envelope V t p) ∧ ConvexOn ℝ Set.univ (envelope V t p) ∧
    ∀ x y, ‖fderiv ℝ (envelope V t p) x - fderiv ℝ (envelope V t p) y‖
      ≤ t * ‖x - y‖ := by
  have hr : LipschitzWith 1 (fun x => x - p x) := by
    rw [lipschitzWith_iff_norm_sub_le]
    simpa using residual_lipschitz hV ht hp hmin
  have hf := envelope_hasFDerivAt hV ht hp hmin
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => t • innerSL ℝ (x - p x), ?_, hf⟩,
    envelope_convex hV ht hp hmin, ?_⟩
  · exact ((innerSL ℝ).continuous.comp hr.continuous).const_smul t
  · intro x y
    rw [(hf x).fderiv, (hf y).fderiv, ← smul_sub, ← map_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_left (residual_lipschitz hV ht hp hmin x y) ht.le

end Submission.Obl.Entropy__moreau_envelope_sequence
