import Submission.Obl.Entropy__smooth_gaussian_transport.NormalizedDifferences

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem ae_ae_line_translate {m : ℕ} {P : E m → Prop}
    (hP : ∀ᵐ x ∂volume, P x) (h : E m) :
    ∀ᵐ x ∂volume, ∀ᵐ t : ℝ ∂volume, P (x + t • h) := by
  obtain ⟨N, hPN, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hgood : ∀ᵐ x : E m ∂volume, x ∉ N := by
    apply ae_iff.mpr
    convert! hN0 using 1
    congr 1
    ext x
    simp only [mem_ofPred_eq, not_not]
  have hmeas : MeasurableSet {z : E m × ℝ | z.1 + z.2 • h ∉ N} := by
    exact (hN.preimage (by fun_prop)).compl
  have hswapped : ∀ᵐ t : ℝ ∂volume, ∀ᵐ x : E m ∂volume, x + t • h ∉ N :=
    ae_of_all _ (fun t => (measurePreserving_add_right volume (t • h)).quasiMeasurePreserving.ae hgood)
  have hline := (Measure.ae_ae_comm hmeas).mpr hswapped
  filter_upwards [hline] with x hx
  filter_upwards [hx] with t ht
  by_contra hn
  exact ht (hPN hn)

theorem lipschitz_monotoneOn_of_ae_deriv_nonneg {g : ℝ → ℝ} {L : NNReal}
    (hL : LipschitzWith L g) {a b : ℝ}
    (hder : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 ≤ deriv g t) : MonotoneOn g (Icc a b) := by
  intro x hx y hy hxy
  have hac : AbsolutelyContinuousOnInterval g x y := hL.lipschitzOnWith.absolutelyContinuousOnInterval
  have hh : 0 ≤ ∫ t in x..y, deriv g t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hxy
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with t ht hti
    exact ht ⟨hx.1.trans hti.1, hti.2.trans hy.2⟩
  rw [hac.integral_deriv_eq_sub] at hh
  linarith

theorem scalar_secondDifference_of_ae_deriv2_le {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) {L : NNReal} (hL : LipschitzWith L (deriv f)) {C : ℝ}
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc (-1 : ℝ) 1 → deriv (deriv f) t ≤ C) :
    f 1 + f (-1) - 2 * f 0 ≤ C := by
  let g : ℝ → ℝ := fun t => C / 2 * t ^ 2 - f t
  have hgd (t : ℝ) : HasDerivAt g (C * t - deriv f t) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (C / 2)).sub (hf t).hasDerivAt using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
    ring
  have hg : Differentiable ℝ g := fun t => (hgd t).differentiableAt
  have hder : deriv g = fun t => C * t - deriv f t := funext (fun t => (hgd t).deriv)
  have hlin : LipschitzWith ‖C‖₊ (fun t : ℝ => C * t) := by
    simpa only [smul_eq_mul] using (lipschitzWith_smul C : LipschitzWith ‖C‖₊ (fun t : ℝ => C • t))
  have hLip : LipschitzWith (‖C‖₊ + L) (deriv g) := by rw [hder]; exact hlin.sub hL
  have hnonneg : ∀ᵐ t ∂volume, t ∈ Icc (-1 : ℝ) 1 → 0 ≤ deriv (deriv g) t := by
    filter_upwards [hbound, hL.ae_differentiableAt (μ := volume)] with t ht hd
    intro hti
    have hdd : HasDerivAt (deriv g) (C - deriv (deriv f) t) t := by
      rw [hder]
      convert! ((hasDerivAt_id t).const_mul C).sub hd.hasDerivAt using 1
      simp only [mul_one]
    rw [hdd.deriv]
    linarith [ht hti]
  have hmono := lipschitz_monotoneOn_of_ae_deriv_nonneg hLip hnonneg
  have hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) g :=
    MonotoneOn.convexOn_of_deriv (convex_Icc _ _) hg.continuous.continuousOn
      hg.differentiableOn (hmono.mono interior_subset)
  have hmid := hconv.2 (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [g, smul_eq_mul] at hmid
  linarith

theorem line_hasDerivAt_gradient {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (x h : E m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • h)) (inner ℝ (gradient u (x + t • h)) h) t := by
  rw [inner_gradient_left]
  have hd : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    convert! ((hasDerivAt_id t).smul_const h).const_add x using 1
    simp only [one_smul]
  exact (hu (x + t • h)).hasFDerivAt.comp_hasDerivAt t hd

theorem line_deriv_lipschitz {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) {L : NNReal} (hL : LipschitzWith L (gradient u)) (x h : E m) :
    ∃ C : NNReal, LipschitzWith C (deriv (fun s : ℝ => u (x + s • h))) := by
  have hline : LipschitzWith ‖ContinuousLinearMap.toSpanSingleton ℝ h‖₊
      (fun s : ℝ => x + s • h) := by
    simpa only [one_mul, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using
      (isometry_add_left x).lipschitz.comp (ContinuousLinearMap.toSpanSingleton ℝ h).lipschitz
  have he : deriv (fun s : ℝ => u (x + s • h)) =
      fun s => (innerSL ℝ h) (gradient u (x + s • h)) := by
    funext s
    rw [(line_hasDerivAt_gradient hu x h s).deriv]
    exact real_inner_comm _ _
  refine ⟨‖innerSL ℝ h‖₊ * (L * ‖ContinuousLinearMap.toSpanSingleton ℝ h‖₊), ?_⟩
  rw [he]
  exact (innerSL ℝ h).lipschitz.comp (hL.comp hline)

/-- Almost-everywhere directional Hessian bounds control the second difference
on each segment in an open convex region. Fubini is essential: the exceptional
set need not have null intersection with every fixed line. -/
theorem secondDifference_of_ae_hessian_bound {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : NNReal} (hL : LipschitzWith L (gradient u))
    {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (h : E m) {M : ℝ}
    (hH : ∀ᵐ y ∂volume, y ∈ Ω →
      inner ℝ ((fderiv ℝ (gradient u) y) h) h ≤ M * ‖h‖ ^ 2)
    {x : E m} (hxm : x - h ∈ Ω) (hxp : x + h ∈ Ω) :
    u (x + h) + u (x - h) - 2 * u x ≤ M * ‖h‖ ^ 2 := by
  have hslice := ae_ae_line_translate ((hL.ae_differentiableAt (μ := volume)).and hH) h
  have hae : ∀ᵐ y ∂volume, y - h ∈ Ω → y + h ∈ Ω →
      u (y + h) + u (y - h) - 2 * u y ≤ M * ‖h‖ ^ 2 := by
    filter_upwards [hslice] with y hy
    intro hym hyp
    have hseg (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : y + t • h ∈ Ω := by
      have hh := hc hym hyp (by linarith [ht.2] : 0 ≤ (1 - t) / 2)
        (by linarith [ht.1] : 0 ≤ (1 + t) / 2) (by ring : (1 - t) / 2 + (1 + t) / 2 = 1)
      convert! hh using 1
      module
    let f : ℝ → ℝ := fun t => u (y + t • h)
    have hf : Differentiable ℝ f := fun t => (line_hasDerivAt_gradient hu.differentiable_one y h t).differentiableAt
    obtain ⟨C, hC⟩ := line_deriv_lipschitz hu.differentiable_one hL y h
    have hdf : deriv f = fun t => inner ℝ (gradient u (y + t • h)) h :=
      funext (fun t => (line_hasDerivAt_gradient hu.differentiable_one y h t).deriv)
    have hbound : ∀ᵐ t ∂volume, t ∈ Icc (-1 : ℝ) 1 → deriv (deriv f) t ≤ M * ‖h‖ ^ 2 := by
      filter_upwards [hy] with t ht
      intro hti
      have hline : HasDerivAt (fun s : ℝ => y + s • h) h t := by
        convert! ((hasDerivAt_id t).smul_const h).const_add y using 1
        simp only [one_smul]
      have hdg : HasDerivAt (fun s : ℝ => gradient u (y + s • h))
          ((fderiv ℝ (gradient u) (y + t • h)) h) t := by
        convert! ht.1.hasFDerivAt.comp_hasDerivAt t hline using 1
      have hdd : HasDerivAt (deriv f)
          (inner ℝ ((fderiv ℝ (gradient u) (y + t • h)) h) h) t := by
        rw [hdf]
        convert! hdg.inner ℝ (hasDerivAt_const t h) using 1
        simp only [inner_zero_right, zero_add]
      rw [hdd.deriv]
      exact ht.2 (hseg t hti)
    have hh := scalar_secondDifference_of_ae_deriv2_le hf hC hbound
    simpa only [f, one_smul, neg_one_smul, zero_smul, add_zero, ← sub_eq_add_neg] using hh
  let bad : Set (E m) := {y | y - h ∈ Ω ∧ y + h ∈ Ω ∧
    M * ‖h‖ ^ 2 < u (y + h) + u (y - h) - 2 * u y}
  have hbopen : IsOpen bad :=
    (hΩ.preimage (continuous_id.sub continuous_const)).inter
      ((hΩ.preimage (continuous_id.add continuous_const)).inter
        (isOpen_lt continuous_const
          (((hu.continuous.comp (continuous_id.add continuous_const)).add
            (hu.continuous.comp (continuous_id.sub continuous_const))).sub
              (continuous_const.mul hu.continuous))))
  have hbnull : volume bad = 0 := by
    have hh : ∀ᵐ y ∂volume, y ∉ bad := hae.mono (fun y hy hyb =>
      (hy hyb.1 hyb.2.1).not_gt hyb.2.2)
    convert! ae_iff.mp hh using 1
    congr 1
    ext y
    simp only [mem_ofPred_eq, not_not]
  have hbempty := hbopen.eq_empty_of_measure_zero hbnull
  by_contra hn
  have hx : x ∈ bad := ⟨hxm, hxp, lt_of_not_ge hn⟩
  rw [hbempty] at hx
  exact hx

theorem normalizedSecondDifference_le_of_ae_hessian_bound {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) {L : NNReal} (hL : LipschitzWith L (gradient u))
    {Ω : Set (E m)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {h : E m} (hh : h ≠ 0) {M : ℝ}
    (hH : ∀ᵐ y ∂volume, y ∈ Ω →
      inner ℝ ((fderiv ℝ (gradient u) y) h) h ≤ M * ‖h‖ ^ 2)
    {x : E m} (hxm : x - h ∈ Ω) (hxp : x + h ∈ Ω) :
    normalizedSecondDifference u h x ≤ M := by
  have hb := secondDifference_of_ae_hessian_bound hu hL hΩ hc h hH hxm hxp
  have hsq : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
  unfold normalizedSecondDifference secondDifference symmetricAverage
  have he : (2 / ‖h‖ ^ 2) * ((u (x + h) + u (x - h)) / 2 - u x) =
      (u (x + h) + u (x - h) - 2 * u x) / ‖h‖ ^ 2 := by ring
  rw [he]
  exact (div_le_iff₀ hsq).mpr hb

end Submission.Obl.Entropy__smooth_gaussian_transport
