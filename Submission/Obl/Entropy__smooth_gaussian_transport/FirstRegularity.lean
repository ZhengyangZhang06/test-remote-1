import Submission.Obl.Entropy__smooth_gaussian_transport.Sections

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A unique subgradient varies continuously, by local boundedness and the
closedness of the subgradient graph. -/
theorem continuous_subgradient_selection {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    {p : E m → E m} (hp : ∀ x, IsSubgradient u x (p x))
    (hunique : ∀ x q, IsSubgradient u x q → q = p x) : Continuous p := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  let K := Metric.closedBall x 1
  let Q := subgradientImage u K
  let C := ((K ×ˢ Q) ∩ {z : E m × E m | IsSubgradient u z.1 z.2}) ∩
    {z : E m × E m | ε ≤ dist z.2 (p x)}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hQ : IsCompact Q := isCompact_subgradientImage hu hK
  have hC : IsCompact C := ((hK.prod hQ).inter_right (isClosed_subgradient_graph hu)).inter_right
    (isClosed_le continuous_const (continuous_snd.dist continuous_const))
  let A := Prod.fst '' C
  have hA : IsCompact A := hC.image continuous_fst
  have hxA : x ∉ A := by
    rintro ⟨⟨z, q⟩, ⟨⟨⟨hz, hq⟩, hs⟩, hd⟩, heq⟩
    change z = x at heq
    subst z
    have hqp : q = p x := hunique x q hs
    have hd' : ε ≤ dist q (p x) := hd
    rw [hqp, dist_self] at hd'
    exact (not_le_of_gt hε) hd'
  have hnear : K ∈ 𝓝 x := Metric.closedBall_mem_nhds _ (by norm_num)
  have havoid : Aᶜ ∈ 𝓝 x := hA.isClosed.isOpen_compl.mem_nhds hxA
  filter_upwards [hnear, havoid] with y hy hyA
  by_contra hd
  apply hyA
  refine ⟨(y, p y), ?_, rfl⟩
  exact ⟨⟨⟨hy, ⟨y, hy, hp y⟩⟩, hp y⟩, le_of_not_gt hd⟩

theorem hasFDerivAt_of_continuous_subgradient {m : ℕ} {u : E m → ℝ}
    {p : E m → E m} (hp : ∀ x, IsSubgradient u x (p x)) (hc : Continuous p)
    (x : E m) : HasFDerivAt u (innerSL ℝ (p x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hpos
  have hcont : Continuous (fun h => ‖p (x + h) - p x‖) :=
    ((hc.comp (continuous_const.add continuous_id)).sub continuous_const).norm
  have hn : ∀ᶠ h : E m in 𝓝 0, ‖p (x + h) - p x‖ < c := by
    exact (hcont.tendsto 0).eventually (p := fun t : ℝ => t < c)
      (Iio_mem_nhds (by simpa only [add_zero, sub_self, norm_zero] using hpos))
  filter_upwards [hn] with h hh
  have hlo := hp x (x + h)
  have hhi := hp (x + h) x
  rw [add_sub_cancel_left] at hlo
  have hsub : x - (x + h) = -h := by abel
  rw [hsub, inner_neg_right] at hhi
  have hr : 0 ≤ u (x + h) - u x - inner ℝ (p x) h := by linarith
  have hupper : u (x + h) - u x - inner ℝ (p x) h ≤
      inner ℝ (p (x + h) - p x) h := by rw [inner_sub_left]; linarith
  simp only [innerSL_apply_apply, Real.norm_eq_abs, abs_of_nonneg hr]
  exact hupper.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hh.le (norm_nonneg h)))

theorem contDiff_one_of_unique_subgradient {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hunique : ∀ x p q, IsSubgradient u x p → IsSubgradient u x q → p = q) :
    ContDiff ℝ 1 u := by
  choose p hp using exists_subgradient hu hdom
  have hc : Continuous p := continuous_subgradient_selection hu.locallyLipschitz.continuous
    hp (fun x q hq => hunique x q (p x) hq (hp x))
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => innerSL ℝ (p x),
    (innerSL ℝ).continuous.comp hc, hasFDerivAt_of_continuous_subgradient hp hc⟩

theorem contDiff_one_of_dual_contactSet_subsingleton {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ)
    (hcontact : ∀ p, (contactSet (finiteConjugate u) p).Subsingleton) :
    ContDiff ℝ 1 u := by
  apply contDiff_one_of_unique_subgradient hu hdom
  intro x p q hp hq
  exact hcontact x (hp.conjugate hdom) (hq.conjugate hdom)

end Submission.Obl.Entropy__smooth_gaussian_transport
