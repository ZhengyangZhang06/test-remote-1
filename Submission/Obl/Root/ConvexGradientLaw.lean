import Mathlib

open MeasureTheory Measure Set Metric Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Root.ConvexGradientLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A finite convex potential on the whole space is differentiable almost everywhere. -/
theorem ae_differentiable_convex {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    (μ : Measure E) [IsAddHaarMeasure μ] : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hlocal (n : ℕ) : ∃ C, LipschitzOnWith C φ (ball (0 : E) (n : ℝ)) := by
    apply (hφ.subset (subset_univ _) (convex_ball (0 : E) ((n : ℝ) + 1))).exists_lipschitzOnWith_of_isBounded
      (by linarith)
    exact ((isCompact_closedBall (0 : E) ((n : ℝ) + 1)).image hc).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hae (n : ℕ) : ∀ᵐ x ∂μ, x ∈ ball (0 : E) (n : ℝ) → DifferentiableAt ℝ φ x := by
    obtain ⟨C, hC⟩ := hlocal n
    filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxn
    exact (hx hxn).differentiableAt (isOpen_ball.mem_nhds hxn)
  filter_upwards [ae_all_iff.mpr hae] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa using hn)

/-- At a differentiability point, a supporting vector is the gradient. -/
theorem gradient_eq_of_support {φ : E → ℝ} {x y : E}
    (hx : DifferentiableAt ℝ φ x)
    (hy : ∀ z, φ x + inner ℝ y (z - x) ≤ φ z) : gradient φ x = y := by
  let A : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E y
  have hm : IsLocalMin (fun z => φ z - A z) x := by
    apply Eventually.of_forall
    intro z
    have h := hy z
    simp only [inner_sub_right] at h
    change φ x - inner ℝ y x ≤ φ z - inner ℝ y z
    linarith
  have hd := (hx.hasFDerivAt.sub A.hasFDerivAt).fderiv
  have he : fderiv ℝ φ x = A := by
    apply sub_eq_zero.mp
    rw [← hd]
    exact hm.fderiv_eq_zero
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, he]

/-- The totalized gradient is measurable, including its value at singular points. -/
theorem measurable_gradient (φ : E → ℝ) : Measurable (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)

/-- An absolutely continuous first marginal makes a subgradient coupling deterministic. -/
theorem coupling_eq_graph_map {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {μ : Measure E} {π : Measure (E × E)}
    (hμ : μ ≪ volume) (hfst : Measure.map Prod.fst π = μ)
    (hsupport : ∀ᵐ p ∂π, ∀ z, φ p.1 + inner ℝ p.2 (z - p.1) ≤ φ z) :
    π = Measure.map (fun x => (x, gradient φ x)) μ := by
  have hdμ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x :=
    hμ.ae_le (ae_differentiable_convex hφ volume)
  have hdπ : ∀ᵐ p ∂π, DifferentiableAt ℝ φ p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rwa [hfst]
  have he : (fun p : E × E => (p.1, gradient φ p.1)) =ᵐ[π] id := by
    filter_upwards [hdπ, hsupport] with p hp hs
    exact Prod.ext rfl (gradient_eq_of_support hp hs)
  have hgraph : Measurable (fun x : E => (x, gradient φ x)) :=
    measurable_id.prodMk (measurable_gradient φ)
  rw [← hfst, Measure.map_map hgraph measurable_fst]
  simp only [Function.comp_def]
  rw [Measure.map_congr he, Measure.map_id]

/-- A coupling in the subgradient graph transports its first marginal by the gradient. -/
theorem gradient_map_of_subgradient_coupling {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {μ ν : Measure E} {π : Measure (E × E)}
    (hμ : μ ≪ volume) (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = ν)
    (hsupport : ∀ᵐ p ∂π, ∀ z, φ p.1 + inner ℝ p.2 (z - p.1) ≤ φ z) :
    Measure.map (gradient φ) μ = ν := by
  have hgraph : Measurable (fun x : E => (x, gradient φ x)) :=
    measurable_id.prodMk (measurable_gradient φ)
  rw [coupling_eq_graph_map hφ hμ hfst hsupport,
    Measure.map_map measurable_snd hgraph] at hsnd
  exact hsnd

end Submission.Obl.Root.ConvexGradientLaw
