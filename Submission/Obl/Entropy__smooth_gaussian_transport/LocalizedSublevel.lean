import Submission.Obl.Entropy__smooth_gaussian_transport.LocalizedAbp
import Submission.Obl.Entropy__smooth_gaussian_transport.RadialBarrier

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem gradient_add_of_differentiable {m : ℕ} {u v : E m → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (x : E m) :
    gradient (fun y => u y + v y) x = gradient u x + gradient v x := by
  have hd : HasFDerivAt (fun y => u y + v y) (fderiv ℝ u x + fderiv ℝ v x) x :=
    (hu x).hasFDerivAt.add (hv x).hasFDerivAt
  simp only [gradient, hd.fderiv, map_add]

/-- The measure-to-point input for weak Harnack: a low value anywhere in the
ball of radius three forces a uniformly positive sublevel measure in the unit
ball. Only almost-everywhere bounds on the elliptic coefficients are required. -/
theorem exists_localized_sublevel_constants {m : ℕ} (hm : 1 ≤ m) {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ T C : ℝ, 1 < T ∧ 0 < C ∧
      ∀ (u : E m → ℝ) (L : NNReal) (A : E m → E m →L[ℝ] E m) (b : E m → E m),
        ContDiff ℝ 1 u → LipschitzWith L (gradient u) →
        (∀ z, ‖z‖ ≤ 4 → 0 ≤ u z) →
        (∀ᵐ z ∂volume, ‖z‖ ≤ 4 → ‖b z‖ ≤ M ∧
          (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
            δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
          linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) →
        (∀ᵐ z ∂volume, ‖z‖ ≤ 4 →
          linearizedTrace (A z) (fderiv ℝ (gradient u) z) -
            inner ℝ (b z) (gradient u z) ≤ 1) →
        ∀ x, ‖x‖ ≤ 3 → u x ≤ 1 →
          volume (Metric.ball (0 : E m) (1 / 8)) ≤
            ENNReal.ofReal C * volume {z | ‖z‖ < 1 ∧ u z < T} := by
  obtain ⟨D, hD, hdet⟩ := exists_operator_det_bound hm
  obtain ⟨ψ, T, N, hT, hN, hψ, ⟨Lψ, hLψ⟩, hψlo, hψbd, hψinner, hψop⟩ :=
    exists_elliptic_radial_barrier (m := m) hδ hΛ hM
  let C : ℝ := D * ((1 + N + M * (1 / 8)) / δ) ^ m
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨T, C, hT, hC, ?_⟩
  intro u L A b hu hLip hu0 hcoeff hineq x hx hux
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  let w : E m → ℝ := fun z => u z + ψ z
  have hw : ContDiff ℝ 1 w := hu.add hψ1
  have hgrad : gradient w = fun z => gradient u z + gradient ψ z :=
    funext (gradient_add_of_differentiable hu.differentiable_one hψ1.differentiable_one)
  have hwLip : LipschitzWith (L + Lψ) (gradient w) := by
    rw [hgrad]
    exact hLip.add hLψ
  have hboundary : ∀ z ∈ frontier (Metric.closedBall (0 : E m) 4), 0 ≤ w z := by
    intro z hz
    rw [frontier_closedBall _ (by norm_num : (4 : ℝ) ≠ 0)] at hz
    have hn : ‖z‖ = 4 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    dsimp [w]
    rw [hψbd z hn, add_zero]
    exact hu0 z hn.le
  have hcoeff' : ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : E m) 4 →
      ‖b z‖ ≤ M ∧ ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (A z) B := by
    filter_upwards [hcoeff] with z hc
    intro hz
    have hh := hc (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    exact ⟨hh.1, hh.2.1⟩
  have hineq' : ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : E m) 4 →
      linearizedTrace (A z) (fderiv ℝ (gradient w) z) - inner ℝ (b z) (gradient w z) ≤ 1 + N ∧
      (z ∉ Metric.ball (0 : E m) 1 →
        linearizedTrace (A z) (fderiv ℝ (gradient w) z) - inner ℝ (b z) (gradient w z) <
          -M * (1 / 8)) := by
    filter_upwards [hcoeff, hineq, hLip.ae_differentiableAt (μ := volume),
      hLψ.ae_differentiableAt (μ := volume)] with z hc hi hdu hdψ
    intro hz
    have hz4 : ‖z‖ ≤ 4 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hh := hc hz4
    have hop := hψop z (A z) (b z) hz4 hh.1 hh.2.1 hh.2.2
    have hwd : HasFDerivAt (gradient w)
        (fderiv ℝ (gradient u) z + fderiv ℝ (gradient ψ) z) z := by
      rw [hgrad]
      exact hdu.hasFDerivAt.add hdψ.hasFDerivAt
    rw [hwd.fderiv, linearizedTrace_add, hgrad]
    simp only [inner_add_right]
    have hi' := hi hz4
    constructor
    · linarith [hop.1]
    · intro hzout
      have hz1 : 1 ≤ ‖z‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hzout
      have hout := hop.2 hz1
      linarith
  have hxK : x ∈ Metric.closedBall (0 : E m) 4 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.trans (by norm_num : (3 : ℝ) ≤ 4)
  have hwx : w x ≤ -1 := by have hh := hψinner x hx; dsimp [w]; linarith
  have hKD : Metric.closedBall (0 : E m) 4 ⊆ Metric.closedBall x 8 := by
    intro z hz
    have hz4 : ‖z‖ ≤ 4 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_sub_le z x).trans (by linarith)
  have habp := abp_contact_bound_localized hD.le hdet hw hwLip
    (isCompact_closedBall (0 : E m) 4) hboundary hδ hM hcoeff' hineq' hxK
      (D := 8) (r := 1 / 8) (by norm_num) hKD (by linarith)
  change volume (Metric.ball (0 : E m) (1 / 8)) ≤ ENNReal.ofReal C *
    volume {z | z ∈ Metric.closedBall (0 : E m) 4 ∧ z ∈ Metric.ball (0 : E m) 1 ∧ w z < 0} at habp
  apply habp.trans
  gcongr 1
  apply measure_mono
  intro z hz
  refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hz.2.1, ?_⟩
  have hh := hψlo z
  have hwz := hz.2.2
  dsimp [w] at hwz
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
