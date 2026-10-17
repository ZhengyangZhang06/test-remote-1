import Submission.Obl.Entropy__smooth_gaussian_transport.InverseDifferentiability
import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport
import Submission.Obl.Entropy__moreau_envelope_sequence.Variational

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem convex_gradient_monotone {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u) (x y : E m) :
    0 ≤ inner ℝ (gradient u x - gradient u y) (x - y) := by
  have hx := convex_gradient_support hu (hd x) y
  have hy := convex_gradient_support hu (hd y) x
  rw [show y - x = -(x - y) by abel, inner_neg_right] at hx
  rw [inner_sub_left]
  linarith

/-- Adding the identity to the gradient gives a homeomorphism with a
1-Lipschitz inverse (the resolvent of the convex gradient). -/
theorem exists_gradient_resolvent_homeomorph {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hdom : conjugateDomain u = univ) :
    ∃ e : E m ≃ₜ E m, (∀ x, e x = x + gradient u x) ∧ LipschitzWith 1 e.symm := by
  let G : E m → E m := fun x => x + gradient u x
  have hc : Continuous G := continuous_id.add (continuous_gradient_of_contDiff_one hC1)
  have hanti : AntilipschitzWith 1 G := by
    apply antilipschitzWith_iff_le_mul_dist.mpr
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm_sub]
    have hmono := convex_gradient_monotone hu hC1.differentiable_one x y
    have hsplit : G x - G y = (x - y) + (gradient u x - gradient u y) := by dsimp [G]; abel
    have hinner : ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y) := by
      rw [hsplit, inner_add_left, real_inner_self_eq_norm_sq]
      linarith
    have hnorm := hinner.trans (real_inner_le_norm _ _)
    nlinarith [norm_nonneg (x - y), norm_nonneg (G x - G y)]
  have hsurj : Function.Surjective G := by
    intro x
    let F : E m → ℝ := fun y => u y + (1 / 2 : ℝ) * ‖x - y‖ ^ 2
    have hFc : Continuous F := hC1.continuous.add
      (continuous_const.mul ((continuous_const.sub continuous_id).norm.pow 2))
    have hFlim : Tendsto F (cocompact (E m)) atTop :=
      tendsto_atTop_mono (fun y => le_add_of_nonneg_right (by positivity))
        (tendsto_atTop_of_finite_conjugate hdom)
    obtain ⟨p, hp⟩ := hFc.exists_forall_le hFlim
    have hsupport : IsSubgradient u p (x - p) := by
      intro y
      have h := Submission.Obl.Entropy__moreau_envelope_sequence.minimizer_variational hu
        (t := 1) (by norm_num) (x := x) (p := p) (mem_univ p)
        (fun z _ => hp z) (mem_univ y)
      simp only [one_mul] at h
      linarith
    have hgrad := Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support
      (hC1.differentiable_one p) hsupport
    refine ⟨p, ?_⟩
    dsimp [G]
    rw [hgrad]
    abel
  let e : E m ≃ₜ E m := (hanti.isEmbedding hc).toHomeomorphOfSurjective hsurj
  refine ⟨e, fun x => rfl, ?_⟩
  exact hanti.to_rightInverse e.apply_symm_apply

/-- A C¹ convex potential with finite conjugate has a differentiable gradient
almost everywhere. This is the second differentiability step of Alexandrov's
theorem, obtained through the Lipschitz resolvent and the inverse theorem. -/
theorem ae_differentiable_gradient_convex {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hdom : conjugateDomain u = univ) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (gradient u) x := by
  obtain ⟨e, he, hLip⟩ := exists_gradient_resolvent_homeomorph hu hC1 hdom
  have hae := ae_differentiable_inverse_of_lipschitz e.symm hLip
  filter_upwards [hae] with x hx
  have hG : DifferentiableAt ℝ (fun y => y + gradient u y) x := by
    simpa only [Homeomorph.symm_symm, show (e : E m → E m) = (fun y => y + gradient u y) from funext he]
      using hx
  have hsub := hG.sub (differentiableAt_id (𝕜 := ℝ) (x := x))
  have heq : ((fun y => y + gradient u y) - id) = gradient u := by
    funext y
    simp
  rwa [heq] at hsub

end Submission.Obl.Entropy__smooth_gaussian_transport
