import Submission.Obl.Entropy__smooth_gaussian_transport.GaussianKernel

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Differentiation in a positive scale parameter with a compact spatial factor. -/
theorem compact_integral_hasDerivAt {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E m → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {g g' : ℝ × E m → F}
    (hg : ContinuousOn g (Ioi 0 ×ˢ univ)) (hg' : ContinuousOn g' (Ioi 0 ×ˢ univ))
    (hd : ∀ s : ℝ, 0 < s → ∀ y : E m, HasDerivAt (fun t => g (t, y)) (g' (s, y)) s)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ∫ y, f y • g (s, y)) (∫ y, f y • g' (r, y)) r := by
  have hgc {s : ℝ} (hs : 0 < s) : Continuous (fun y : E m => g (s, y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hxy : (s, y) ∈ Ioi 0 ×ˢ (univ : Set (E m)) := ⟨hs, mem_univ y⟩
    exact (hg.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hxy)).comp
      (f := fun z : E m => (s, z)) (continuous_const.prodMk continuous_id).continuousAt
  have hg'c {s : ℝ} (hs : 0 < s) : Continuous (fun y : E m => g' (s, y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hxy : (s, y) ∈ Ioi 0 ×ˢ (univ : Set (E m)) := ⟨hs, mem_univ y⟩
    exact (hg'.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hxy)).comp
      (f := fun z : E m => (s, z)) (continuous_const.prodMk continuous_id).continuousAt
  let K : Set (ℝ × E m) := Icc (r / 2) (3 * r / 2) ×ˢ tsupport f
  have hK : IsCompact K := isCompact_Icc.prod hfc
  have hKU : K ⊆ Ioi 0 ×ˢ univ := by
    rintro ⟨s, y⟩ hs
    exact ⟨lt_of_lt_of_le (by linarith) hs.1.1, mem_univ y⟩
  obtain ⟨M, hM, hb⟩ := (hK.image_of_continuousOn (hg'.mono hKU)).isBounded.exists_pos_norm_le
  have hpos {s : ℝ} (hs : s ∈ Ioo (r / 2) (3 * r / 2)) : 0 < s := by
    have := hs.1
    linarith
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => f y • g (s, y)) (F' := fun s y => f y • g' (s, y))
    (μ := volume) (x₀ := r)
    (s := Ioo (r / 2) (3 * r / 2)) (bound := fun y => |f y| * M)
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Ioo_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 3 * r / 2)] with s hs
    exact (hf.smul (hgc (hpos hs))).aestronglyMeasurable
  · exact (hf.smul (hgc hr)).integrable_of_hasCompactSupport hfc.smul_right
  · exact (hf.smul (hg'c hr)).aestronglyMeasurable
  · filter_upwards [] with y
    intro s hs
    by_cases hy : f y = 0
    · simp only [hy, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hb _ ⟨(s, y), ⟨⟨hs.1.le, hs.2.le⟩, subset_closure hy⟩, rfl⟩
  · exact (hf.integrable_of_hasCompactSupport hfc).norm.mul_const M
  · filter_upwards [] with y
    intro s hs
    exact (hd s (hpos hs) y).const_smul (f y)

end Submission.Obl.Entropy__smooth_gaussian_transport
