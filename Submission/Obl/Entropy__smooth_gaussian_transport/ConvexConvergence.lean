import Submission.Obl.Entropy__smooth_gaussian_transport.Subgradient

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

private theorem eventually_inner_subgradient_lt {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    {x : E m} {p : ℕ → E m} (hp : ∀ᶠ n in atTop, IsSubgradient (u n) x (p n))
    (hlim : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    (hd : DifferentiableAt ℝ v x) (e : E m) {b : ℝ}
    (hb : inner ℝ (gradient v x) e < b) :
    ∀ᶠ n in atTop, inner ℝ (p n) e < b := by
  have hline : HasDerivAt (fun t : ℝ => v (x + t • e)) (fderiv ℝ v x e) 0 := by
    have hx : DifferentiableAt ℝ v (x + (0 : ℝ) • e) := by simpa using hd
    convert! hx.hasFDerivAt.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x) using 1 <;> simp
  have hgrad : fderiv ℝ v x e = inner ℝ (gradient v x) e := by
    rw [← toDual_gradient]
    rfl
  have hslope : Tendsto (fun t : ℝ => (v (x + t • e) - v x) / t)
      (𝓝[>] 0) (𝓝 (inner ℝ (gradient v x) e)) := by
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul, div_eq_inv_mul, hgrad] using
      hline.tendsto_slope_zero_right
  have hsmall := hslope.eventually (gt_mem_nhds hb)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htb⟩ := (hpos.and hsmall).exists
  have htpos : 0 < t := ht
  have hquot : Tendsto (fun n => (u n (x + t • e) - u n x) / t) atTop
      (𝓝 ((v (x + t • e) - v x) / t)) := ((hlim _).sub (hlim _)).div_const t
  filter_upwards [hp, hquot.eventually (gt_mem_nhds htb)] with n hn hnb
  have hs := hn (x + t • e)
  rw [add_sub_cancel_left, real_inner_smul_right] at hs
  have hle : inner ℝ (p n) e ≤ (u n (x + t • e) - u n x) / t :=
    (le_div_iff₀ htpos).mpr (by linarith)
  exact hle.trans_lt hnb

/-- Pointwise convergence of convex functions forces convergence of any
supporting vectors at a differentiability point of the limit. -/
theorem tendsto_subgradient_of_pointwise {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    {x : E m} {p : ℕ → E m} (hp : ∀ᶠ n in atTop, IsSubgradient (u n) x (p n))
    (hlim : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    (hd : DifferentiableAt ℝ v x) : Tendsto p atTop (𝓝 (gradient v x)) := by
  have hinner (e : E m) : Tendsto (fun n => inner ℝ (p n) e) atTop
      (𝓝 (inner ℝ (gradient v x) e)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have hneg := eventually_inner_subgradient_lt hp hlim hd (-e)
        (b := -a) (by simpa only [inner_neg_right, neg_lt_neg_iff] using ha)
      simpa only [inner_neg_right, neg_lt_neg_iff] using hneg
    · intro b hb
      exact eventually_inner_subgradient_lt hp hlim hd e hb
  have hcoords : Tendsto (fun n => WithLp.ofLp (p n)) atTop
      (𝓝 (WithLp.ofLp (gradient v x))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [EuclideanSpace.inner_basisFun_real] using
      hinner (EuclideanSpace.basisFun (Fin m) ℝ i)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).continuousAt.tendsto.comp hcoords

/-- Gradients of a pointwise convergent convex sequence converge wherever all
the functions in question are differentiable. -/
theorem tendsto_gradient_of_convex_pointwise {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n))
    (hlim : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    {x : E m} (hd : DifferentiableAt ℝ v x)
    (hdu : ∀ᶠ n in atTop, DifferentiableAt ℝ (u n) x) :
    Tendsto (fun n => gradient (u n) x) atTop (𝓝 (gradient v x)) := by
  apply tendsto_subgradient_of_pointwise _ hlim hd
  filter_upwards [hdu] with n hn
  exact convex_gradient_support (hu n) hn

/-- Almost-everywhere gradient convergence under pointwise convergence of
finite convex potentials. -/
theorem ae_tendsto_gradient_of_convex_pointwise {m : ℕ} {u : ℕ → E m → ℝ} {v : E m → ℝ}
    (hu : ∀ n, ConvexOn ℝ univ (u n)) (hv : ConvexOn ℝ univ v)
    (hlim : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (v y))) :
    ∀ᵐ x ∂volume, Tendsto (fun n => gradient (u n) x) atTop (𝓝 (gradient v x)) := by
  have hdn : ∀ n, ∀ᵐ x ∂volume, DifferentiableAt ℝ (u n) x :=
    fun n => Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex (hu n) volume
  filter_upwards [Submission.Lib.Brenier.ConvexGradientLaw.ae_differentiable_convex hv volume,
    ae_all_iff.mpr hdn] with x hx hxn
  exact tendsto_gradient_of_convex_pointwise hu hlim hx (Eventually.of_forall hxn)

end Submission.Obl.Entropy__smooth_gaussian_transport
