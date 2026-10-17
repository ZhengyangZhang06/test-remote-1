import Submission.Obl.Entropy__smooth_gaussian_transport.AeDirectionalBounds

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- The mean value inequality for a Lipschitz scalar function with an
almost-everywhere derivative bound on an open convex region. -/
theorem scalar_increment_of_ae_fderiv_bound {m : ℕ} {u : E m → ℝ} {L : NNReal}
    (hL : LipschitzWith L u) {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ u z‖ ≤ M)
    (h : E m) {x : E m} (hx : x ∈ Ω) (hxh : x + h ∈ Ω) :
    u (x + h) - u x ≤ M * ‖h‖ := by
  have hslice := ae_ae_line_translate ((hL.ae_differentiableAt (μ := volume)).and hbound) h
  have hae : ∀ᵐ z ∂volume, z ∈ Ω → z + h ∈ Ω → u (z + h) - u z ≤ M * ‖h‖ := by
    filter_upwards [hslice] with z hz
    intro hzΩ hzh
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z + t • h ∈ Ω := by
      have hh := hc hzΩ hzh (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring : 1 - t + t = 1)
      convert! hh using 1
      module
    let C : ℝ := M * ‖h‖
    let g : ℝ → ℝ := fun t => C * t - u (z + t • h)
    have hline : LipschitzWith ‖ContinuousLinearMap.toSpanSingleton ℝ h‖₊
        (fun t : ℝ => z + t • h) := by
      simpa only [one_mul, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using
        (isometry_add_left z).lipschitz.comp (ContinuousLinearMap.toSpanSingleton ℝ h).lipschitz
    have hlin : LipschitzWith ‖C‖₊ (fun t : ℝ => C * t) := by
      simpa only [smul_eq_mul] using (lipschitzWith_smul C : LipschitzWith ‖C‖₊ (fun t : ℝ => C • t))
    have hg : LipschitzWith (‖C‖₊ + L * ‖ContinuousLinearMap.toSpanSingleton ℝ h‖₊) g :=
      hlin.sub (hL.comp hline)
    have hd : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 1 → 0 ≤ deriv g t := by
      filter_upwards [hz] with t ht
      intro hti
      have hlineD : HasDerivAt (fun s : ℝ => z + s • h) h t := by
        convert! ((hasDerivAt_id t).smul_const h).const_add z using 1
        simp only [one_smul]
      have hdu : HasDerivAt (fun s : ℝ => u (z + s • h)) ((fderiv ℝ u (z + t • h)) h) t := by
        convert! ht.1.hasFDerivAt.comp_hasDerivAt t hlineD using 1
      have hdg : HasDerivAt g (C - (fderiv ℝ u (z + t • h)) h) t := by
        convert! ((hasDerivAt_id t).const_mul C).sub hdu using 1
        simp only [mul_one]
      rw [hdg.deriv]
      have hnorm := ht.2 (hseg t hti)
      have hb : (fderiv ℝ u (z + t • h)) h ≤ M * ‖h‖ := by
        calc
          _ ≤ ‖(fderiv ℝ u (z + t • h)) h‖ := le_abs_self _
          _ ≤ ‖fderiv ℝ u (z + t • h)‖ * ‖h‖ := (fderiv ℝ u (z + t • h)).le_opNorm h
          _ ≤ M * ‖h‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg h)
      exact sub_nonneg.mpr hb
    have hmono := lipschitz_monotoneOn_of_ae_deriv_nonneg hg hd
    have hh := hmono (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
    simp only [g, mul_zero, zero_smul, add_zero, mul_one, one_smul] at hh
    dsimp only [C] at hh
    linarith
  let bad : Set (E m) := {z | z ∈ Ω ∧ z + h ∈ Ω ∧ M * ‖h‖ < u (z + h) - u z}
  have hbopen : IsOpen bad := hΩ.inter ((hΩ.preimage (continuous_id.add continuous_const)).inter
    (isOpen_lt continuous_const ((hL.continuous.comp (continuous_id.add continuous_const)).sub hL.continuous)))
  have hbnull : volume bad = 0 := by
    have hh : ∀ᵐ z ∂volume, z ∉ bad := hae.mono (fun z hz hzb =>
      (hz hzb.1 hzb.2.1).not_gt hzb.2.2)
    convert! ae_iff.mp hh using 1
    congr 1
    ext z
    simp only [mem_ofPred_eq, not_not]
  have hbempty := hbopen.eq_empty_of_measure_zero hbnull
  by_contra hn
  have hh : x ∈ bad := ⟨hx, hxh, lt_of_not_ge hn⟩
  rw [hbempty] at hh
  exact hh

/-- Vector-valued version of the almost-everywhere mean value inequality. -/
theorem norm_sub_of_ae_fderiv_bound {m : ℕ} {f : E m → E m} {L : NNReal}
    (hL : LipschitzWith L f) {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ f z‖ ≤ M)
    {x y : E m} (hx : x ∈ Ω) (hy : y ∈ Ω) : ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  by_cases heq : f y - f x = 0
  · rw [heq, norm_zero]
    exact mul_nonneg hM (norm_nonneg _)
  let v : E m := ‖f y - f x‖⁻¹ • (f y - f x)
  have hn : 0 < ‖f y - f x‖ := norm_pos_iff.mpr heq
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  let u : E m → ℝ := fun z => inner ℝ v (f z)
  have hu : LipschitzWith (‖innerSL ℝ v‖₊ * L) u := (innerSL ℝ v).lipschitz.comp hL
  have hb : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ u z‖ ≤ M := by
    filter_upwards [hL.ae_differentiableAt (μ := volume), hbound] with z hz hzb
    intro hzΩ
    have hd : HasFDerivAt u ((innerSL ℝ v).comp (fderiv ℝ f z)) z :=
      (innerSL ℝ v).hasFDerivAt.comp z hz.hasFDerivAt
    rw [hd.fderiv]
    calc
      _ ≤ ‖innerSL ℝ v‖ * ‖fderiv ℝ f z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ f z‖ := by rw [innerSL_apply_norm, hv, one_mul]
      _ ≤ M := hzb hzΩ
  have hh := scalar_increment_of_ae_fderiv_bound hu hΩ hc hM hb (y - x) hx
    (by simpa only [add_sub_cancel] using hy)
  have he : u (x + (y - x)) - u x = ‖f y - f x‖ := by
    simp only [u, add_sub_cancel, ← inner_sub_right, v, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp
    rw [← inner_sub_right, real_inner_self_eq_norm_sq]
  rwa [he] at hh

/-- Essential closeness of a derivative field to a fixed linear map gives
an everywhere first-order remainder bound on the convex region. -/
theorem linear_remainder_of_ae_fderiv_bound {m : ℕ} {f : E m → E m} {L : NNReal}
    (hL : LipschitzWith L f) {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (A : E m →L[ℝ] E m) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ f z - A‖ ≤ ε)
    {x y : E m} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖f y - f x - A (y - x)‖ ≤ ε * ‖y - x‖ := by
  let g : E m → E m := fun z => f z - A z
  have hg : LipschitzWith (L + ‖A‖₊) g := hL.sub A.lipschitz
  have hb : ∀ᵐ z ∂volume, z ∈ Ω → ‖fderiv ℝ g z‖ ≤ ε := by
    filter_upwards [hL.ae_differentiableAt (μ := volume), hbound] with z hz hzb
    intro hzΩ
    have hd : HasFDerivAt g (fderiv ℝ f z - A) z := hz.hasFDerivAt.sub A.hasFDerivAt
    rw [hd.fderiv]
    exact hzb hzΩ
  have hh := norm_sub_of_ae_fderiv_bound hg hΩ hc hε hb hx hy
  have he : g y - g x = f y - f x - A (y - x) := by dsimp [g]; rw [map_sub]; abel
  rwa [he] at hh

end Submission.Obl.Entropy__smooth_gaussian_transport
