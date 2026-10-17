import Submission.Obl.Entropy__smooth_gaussian_transport.SymmetricAverage
import Submission.Obl.Entropy__smooth_gaussian_transport.WeakComparison

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem exists_scale_near_one {m : ℕ} {a b : ℝ} (hab : a < b) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ a < c ^ m * b := by
  have hn : {c : ℝ | 0 < c ∧ a < c ^ m * b} ∈ 𝓝 (1 : ℝ) := by
    apply ((isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const ((continuous_id.pow m).mul continuous_const))).mem_nhds
    simpa using And.intro (show (0 : ℝ) < 1 by norm_num) hab
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hh : 1 - r / 2 ∈ Metric.ball (1 : ℝ) r := by
    change |1 - r / 2 - 1| < r
    rw [show 1 - r / 2 - 1 = -(r / 2) by ring, abs_neg, abs_of_pos (half_pos hr)]
    linarith
  exact ⟨1 - r / 2, (hb hh).1, by linarith, (hb hh).2⟩

/-- At a local maximum of the difference, a continuous lower density for the
strictly convex potential cannot exceed the other potential's density.
Neither potential is assumed twice differentiable. -/
theorem density_le_at_localMax_difference {m : ℕ} (hm : 1 ≤ m)
    {u v f g : E m → ℝ} (hu : ConvexOn ℝ univ u)
    (hv : StrictConvexOn ℝ univ v) (hdu : conjugateDomain u = univ)
    (hdv : conjugateDomain v = univ) (hf : Continuous f) (hg : Continuous g)
    (hMu : alexandrovMeasure u = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hMv : volume.withDensity (fun y => ENNReal.ofReal (g y)) ≤ alexandrovMeasure v)
    {x : E m} (hfx : 0 ≤ f x) (hmax : IsLocalMax (fun y => v y - u y) x) :
    g x ≤ f x := by
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  by_contra hn
  obtain ⟨c, hc, hc1, hcg⟩ := exists_scale_near_one (m := m) (lt_of_not_ge hn)
  obtain ⟨F, hxF, hFc⟩ := exists_between hcg
  obtain ⟨G, hFG, hGc⟩ := exists_between hFc
  have hGpos : 0 < G := hfx.trans_lt (hxF.trans hFG)
  have hnearF : ∀ᶠ y in 𝓝 x, f y < F := hf.continuousAt (gt_mem_nhds hxF)
  have hnearG : ∀ᶠ y in 𝓝 x, G < c ^ m * g y :=
    (continuous_const.mul hg).continuousAt (lt_mem_nhds hGc)
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp (hmax.and (hnearF.and hnearG))
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hloc (z : E m) (hz : z ∈ Metric.closedBall x R) :
      v z - u z ≤ v x - u x ∧ f z < F ∧ G < c ^ m * g z := by
    apply hnear
    change dist z x < r
    have hh : dist z x ≤ R := hz
    dsimp only [R] at hh
    linarith
  obtain ⟨p, hp⟩ := exists_subgradient hv.convexOn hdv x
  let gap := fun z => v z - v x - inner ℝ p (z - x)
  have hgapcont : Continuous gap :=
    (hv.convexOn.locallyLipschitz.continuous.sub continuous_const).sub
      (continuous_const.inner (continuous_id.sub continuous_const))
  have hgappos (z : E m) (hz : z ∈ Metric.sphere x R) : 0 < gap z := by
    have hne : x ≠ z := by
      intro he
      subst z
      have hh : (0 : ℝ) = R := by simpa only [Metric.mem_sphere, dist_self] using hz
      linarith
    have hh := strict_subgradient_support hv hp hne
    dsimp [gap]
    linarith
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere x R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hgapcont.continuousOn
  let d := gap z
  have hd : 0 < d := hgappos z hz
  have hgap (y : E m) (hy : y ∈ Metric.sphere x R) : d ≤ gap y := hmin hy
  let ε := (1 - c) * d / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q := tilt (fun y => c * v y) (-(1 - c) • p)
    (c * v x + (1 - c) * inner ℝ p x - u x - ε)
  have hqconv : ConvexOn ℝ univ q :=
    tilt_convex (hv.convexOn.smul hc.le) _ _
  have hqdom : conjugateDomain q = univ :=
    tilt_conjugateDomain (positiveScale_conjugateDomain hdv hc) _ _
  have hqval (y : E m) :
      q y - u y = (v y - u y) - (v x - u x) - (1 - c) * gap y + ε := by
    simp only [q, tilt, gap, real_inner_smul_left, inner_sub_right]
    ring
  have hboundary : ∀ y ∈ frontier (Metric.closedBall x R), q y ≤ u y := by
    intro y hy
    have hyK := frontier_subset_closure hy
    rw [Metric.isClosed_closedBall.closure_eq] at hyK
    rw [frontier_closedBall x hR.ne'] at hy
    have h₁ := (hloc y hyK).1
    have h₂ := mul_le_mul_of_nonneg_left (hgap y hy) (sub_pos.mpr hc1).le
    have he := hqval y
    dsimp only [ε] at he
    nlinarith [mul_pos (sub_pos.mpr hc1) hd]
  have hmass (s : Set (E m)) (hs : MeasurableSet s)
      (hsK : s ⊆ Metric.closedBall x R) (hpos : 0 < volume s) :
      alexandrovMeasure u s < alexandrovMeasure q s := by
    have hup : alexandrovMeasure u s ≤ ENNReal.ofReal F * volume s := by
      rw [hMu, withDensity_apply _ hs]
      calc
        _ ≤ ∫⁻ y in s, ENNReal.ofReal F := setLIntegral_mono measurable_const
          (fun y hy => ENNReal.ofReal_le_ofReal (hloc y (hsK hy)).2.1.le)
        _ = _ := setLIntegral_const _ _
    have hlo : ENNReal.ofReal (G / c ^ m) * volume s ≤ alexandrovMeasure v s := by
      apply le_trans _ (hMv s)
      rw [withDensity_apply _ hs]
      calc
        _ = ∫⁻ y in s, ENNReal.ofReal (G / c ^ m) := (setLIntegral_const _ _).symm
        _ ≤ _ := setLIntegral_mono hg.measurable.ennreal_ofReal (fun y hy =>
          ENNReal.ofReal_le_ofReal ((div_le_iff₀ (pow_pos hc _)).mpr
            (by simpa only [mul_comm] using (hloc y (hsK hy)).2.2.le)))
    have hqMA : alexandrovMeasure q s = ENNReal.ofReal (c ^ m) * alexandrovMeasure v s := by
      dsimp only [q]
      rw [tilt_alexandrovMeasure (u := fun y => c * v y)
        (continuous_const.mul hv.convexOn.locallyLipschitz.continuous)
        (positiveScale_conjugateDomain hdv hc),
        positiveScale_alexandrov hv.convexOn.locallyLipschitz.continuous hdv hc hs]
    have hlow : ENNReal.ofReal G * volume s ≤ alexandrovMeasure q s := by
      rw [hqMA]
      have hh := mul_le_mul_right hlo (ENNReal.ofReal (c ^ m))
      simpa only [← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hc _).le,
        mul_div_cancel₀ G (pow_pos hc m).ne'] using hh
    apply hup.trans_lt (lt_of_lt_of_le _ hlow)
    apply (ENNReal.mul_lt_mul_iff_left hpos.ne'
      ((measure_mono hsK).trans_lt (isCompact_closedBall x R).measure_lt_top).ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff hGpos).mpr hFG
  have hcomp := comparison_of_strict_mass hu hqconv hdu hqdom
    (isCompact_closedBall x R) hboundary hmass x (Metric.mem_closedBall_self hR.le)
  have he := hqval x
  simp only [gap, sub_self, inner_zero_right] at he
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
