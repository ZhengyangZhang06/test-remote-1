import Submission.Obl.Entropy__smooth_gaussian_transport.UniformConvexConvergence

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- If the boundary of a ball lies strictly above all affine functions of
slope at most P based at zero, such slopes have no contact outside the ball. -/
theorem norm_contact_lt_of_sphere_growth {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) {R P : ℝ} (hR : 0 < R)
    (hg : ∀ z : E m, ‖z‖ = R → u 0 + P * R < u z)
    {x p : E m} (hp : ‖p‖ ≤ P) (hxp : IsSubgradient u x p) : ‖x‖ < R := by
  by_contra hlt
  have hxR : R ≤ ‖x‖ := le_of_not_gt hlt
  have hxpos : 0 < ‖x‖ := hR.trans_le hxR
  let t : ℝ := R / ‖x‖
  have ht : 0 ≤ t := (div_pos hR hxpos).le
  have ht1 : t ≤ 1 := (div_le_one hxpos).mpr hxR
  have htz : ‖t • x‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact div_mul_cancel₀ R hxpos.ne'
  have hcv : u ((1 - t) • (0 : E m) + t • x) ≤
      (1 - t) • u 0 + t • u x :=
    hu.2 (mem_univ 0) (mem_univ x) (sub_nonneg.mpr ht1) ht (by ring)
  simp only [smul_zero, zero_add, smul_eq_mul] at hcv
  have hsup := hxp 0
  simp only [zero_sub, inner_neg_right] at hsup
  have hip : inner ℝ p x ≤ P * ‖x‖ :=
    (real_inner_le_norm p x).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg x))
  have hmul := mul_le_mul_of_nonneg_left (show u x ≤ u 0 + P * ‖x‖ by linarith) ht
  have htR : t * ‖x‖ = R := div_mul_cancel₀ _ hxpos.ne'
  have hbound : u (t • x) ≤ u 0 + P * R := by
    calc
      u (t • x) ≤ (1 - t) * u 0 + t * u x := hcv
      _ ≤ (1 - t) * u 0 + t * (u 0 + P * ‖x‖) := add_le_add le_rfl hmul
      _ = u 0 + P * (t * ‖x‖) := by ring
      _ = u 0 + P * R := by rw [htR]
  exact (hg (t • x) htz).not_ge hbound

/-- Contacts for bounded slopes remain in one ball for a convergent convex
sequence whose limit has a finite conjugate everywhere. -/
theorem eventually_bounded_contacts {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n)) (hv : ConvexOn ℝ univ v)
    (hdv : conjugateDomain v = univ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {P : ℝ} (hP : 0 ≤ P) : ∃ R : ℝ, 0 < R ∧
      (∀ x p, ‖p‖ ≤ P → IsSubgradient v x p → ‖x‖ < R) ∧
      ∀ᶠ n in atTop, ∀ x p, ‖p‖ ≤ P → IsSubgradient (u n) x p → ‖x‖ < R := by
  obtain ⟨M, hM⟩ := arbitrary_linear_minorant hdv (R := P + 1) (by positivity)
  let R : ℝ := max 1 (M + v 0 + 3)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hgap : M + v 0 + 3 ≤ R := le_max_right _ _
  have hg : ∀ z : E m, ‖z‖ = R → v 0 + P * R + 2 < v z := by
    intro z hz
    have hzM := hM z
    rw [hz] at hzM
    nlinarith
  refine ⟨R, hR, ?_, ?_⟩
  · intro x p hp hxp
    exact norm_contact_lt_of_sphere_growth hv hR
      (fun z hz => by linarith [hg z hz]) hp hxp
  · have hunif := tendstoUniformlyOn_of_convex_pointwise hu hlim
      (isCompact_closedBall (0 : E m) R)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif 1 (by norm_num)] with n hn
    intro x p hp hxp
    apply norm_contact_lt_of_sphere_growth (hu n) hR _ hp hxp
    intro z hz
    have hzball : z ∈ Metric.closedBall (0 : E m) R := by simp [hz]
    have h0ball : (0 : E m) ∈ Metric.closedBall 0 R := by simpa using hR.le
    have hnz := hn z hzball
    have hn0 := hn 0 h0ball
    rw [Real.dist_eq] at hnz hn0
    have hzlo := (abs_lt.mp hnz).2
    have h0hi := (abs_lt.mp hn0).1
    linarith [hg z hz]

/-- Finite conjugates converge pointwise when the primal finite convex
potentials do and the limit is superlinear. -/
theorem tendsto_finiteConjugate_of_pointwise {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n)) (hv : ConvexOn ℝ univ v)
    (hdu : ∀ n, conjugateDomain (u n) = univ) (hdv : conjugateDomain v = univ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) (p : E m) :
    Tendsto (fun n => finiteConjugate (u n) p) atTop (𝓝 (finiteConjugate v p)) := by
  obtain ⟨R, hR, hvR, huR⟩ := eventually_bounded_contacts hu hv hdv hlim (norm_nonneg p)
  obtain ⟨x, hx⟩ := exists_subgradient_contact hv.locallyLipschitz.continuous hdv p
  have hxR : x ∈ Metric.closedBall (0 : E m) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hvR x p le_rfl hx).le
  have hunif := tendstoUniformlyOn_of_convex_pointwise hu hlim (isCompact_closedBall (0 : E m) R)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hevent : ∀ᶠ n in atTop, dist (finiteConjugate (u n) p) (finiteConjugate v p) < ε := by
    filter_upwards [huR, Metric.tendstoUniformlyOn_iff.mp hunif ε hε] with n hnR hn
    obtain ⟨y, hy⟩ := exists_subgradient_contact (hu n).locallyLipschitz.continuous (hdu n) p
    have hyR : y ∈ Metric.closedBall (0 : E m) R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hnR y p le_rfl hy).le
    have hnx := hn x hxR
    have hny := hn y hyR
    rw [Real.dist_eq] at hnx hny ⊢
    apply abs_lt.mpr
    constructor
    · have hfen := fenchel_inequality (hdu n) x p
      rw [hx.finiteConjugate_eq]
      linarith [(abs_lt.mp hnx).1]
    · have hfen := fenchel_inequality hdv y p
      rw [hy.finiteConjugate_eq]
      linarith [(abs_lt.mp hny).2]
  exact eventually_atTop.mp hevent

theorem tendstoUniformlyOn_finiteConjugate_of_pointwise {m : ℕ}
    {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n)) (hv : ConvexOn ℝ univ v)
    (hdu : ∀ n, conjugateDomain (u n) = univ) (hdv : conjugateDomain v = univ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {K : Set (E m)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => finiteConjugate (u n)) (finiteConjugate v) atTop K :=
  tendstoUniformlyOn_of_convex_pointwise (fun n => finiteConjugate_convex (hdu n))
    (tendsto_finiteConjugate_of_pointwise hu hv hdu hdv hlim) hK

end Submission.Obl.Entropy__smooth_gaussian_transport
