import Submission.Obl.Entropy__smooth_gaussian_transport.AbpEstimate
import Submission.Obl.Entropy__smooth_gaussian_transport.QuadraticBarrier

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def sublevelBarrier {m : ℕ} (c x : E m) : ℝ := ‖x - c‖ ^ 2 - 4

theorem sublevelBarrier_contDiff {m : ℕ} (c : E m) {n : WithTop ENat} :
    ContDiff ℝ n (sublevelBarrier c) :=
  ((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const

theorem sublevelBarrier_gradient {m : ℕ} (c x : E m) :
    gradient (sublevelBarrier c) x = (2 : ℝ) • (x - c) := by
  have he : sublevelBarrier c = fun y => quadraticBarrier 2 (-4) (y - c) := by
    ext y
    simp only [sublevelBarrier, quadraticBarrier]
    ring
  have hd := (hasFDerivAt_comp_sub c).mpr
    ((quadraticBarrier_contDiff (m := m) 2 (-4)).differentiable (by simp) (x - c)).hasFDerivAt
  rw [he]
  change (InnerProductSpace.toDual ℝ (E m)).symm
    (fderiv ℝ (fun y => quadraticBarrier 2 (-4) (y - c)) x) = _
  rw [hd.fderiv]
  exact quadraticBarrier_gradient (by norm_num : (0 : ℝ) ≤ 2) (-4) (x - c)

theorem gradient_add_sublevelBarrier {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (c x : E m) :
    gradient (fun y => u y + sublevelBarrier c y) x =
      gradient u x + (2 : ℝ) • (x - c) := by
  have hd : HasFDerivAt (fun y => u y + sublevelBarrier c y)
      (fderiv ℝ u x + fderiv ℝ (sublevelBarrier c) x) x :=
    (hu x).hasFDerivAt.add ((sublevelBarrier_contDiff c (n := 1)).differentiable_one x).hasFDerivAt
  have hg : gradient (fun y => u y + sublevelBarrier c y) x =
      gradient u x + gradient (sublevelBarrier c) x := by
    simp only [gradient, hd.fderiv, map_add]
  rw [hg, sublevelBarrier_gradient]

/-- If a nonnegative elliptic supersolution has value at most one in the
unit ball, a definite amount of the ball of radius two lies below level four.
This is the contact-measure step towards weak Harnack. -/
theorem elliptic_sublevel_measure_bound {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hdet : ∀ B : E m →L[ℝ] E m, |B.det| ≤ C * ‖B‖ ^ m)
    {u : E m → ℝ} (hu : ContDiff ℝ 1 u) {L : NNReal} (hLip : LipschitzWith L (gradient u))
    {c : E m} (hu0 : ∀ z ∈ Metric.closedBall c 2, 0 ≤ u z)
    {A : E m → E m →L[ℝ] E m} {b : E m → E m} {δ Λ M F : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hcoeff : ∀ᵐ z ∂volume, z ∈ Metric.closedBall c 2 →
      ‖b z‖ ≤ M ∧
      (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
      linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ)
    (hineq : ∀ᵐ z ∂volume, z ∈ Metric.closedBall c 2 →
      linearizedTrace (A z) (fderiv ℝ (gradient u) z) - inner ℝ (b z) (gradient u z) ≤ F)
    {x : E m} (hx : x ∈ Metric.closedBall c 1) (hux : u x ≤ 1) :
    volume (Metric.ball (0 : E m) (1 / 4)) ≤
      ENNReal.ofReal (C * ((F + 2 * Λ + 4 * M + M * (1 / 4)) / δ) ^ m) *
        volume {z | z ∈ Metric.closedBall c 2 ∧ u z < 4} := by
  let w : E m → ℝ := fun z => u z + sublevelBarrier c z
  have hw : ContDiff ℝ 1 w := hu.add (sublevelBarrier_contDiff c)
  have hgrad : gradient w = fun z => gradient u z + (2 : ℝ) • (z - c) :=
    funext (gradient_add_sublevelBarrier hu.differentiable_one c)
  have hquadLip : LipschitzWith 2 (fun z : E m => (2 : ℝ) • (z - c)) := by
    have hh := (lipschitzWith_smul (2 : ℝ)).comp (isometry_add_right (-c)).lipschitz
    have hn : ‖(2 : ℝ)‖₊ = (2 : NNReal) := by norm_num
    simpa only [Function.comp_def, sub_eq_add_neg, mul_one, hn] using hh
  have hwLip : LipschitzWith (L + 2) (gradient w) := by
    rw [hgrad]
    exact hLip.add hquadLip
  have hboundary : ∀ z ∈ frontier (Metric.closedBall c 2), 0 ≤ w z := by
    intro z hz
    rw [frontier_closedBall c (by norm_num : (2 : ℝ) ≠ 0)] at hz
    have hn : ‖z - c‖ = 2 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hzK : z ∈ Metric.closedBall c 2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, hn] using (le_refl (2 : ℝ))
    simpa only [w, sublevelBarrier, hn, show (2 : ℝ) ^ 2 - 4 = 0 by norm_num, add_zero] using hu0 z hzK
  have hcoeff' : ∀ᵐ z ∂volume, z ∈ Metric.closedBall c 2 →
      ‖b z‖ ≤ M ∧ ∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
        δ * ‖B‖ ≤ linearizedTrace (A z) B :=
    hcoeff.mono (fun _ hz hzK => ⟨(hz hzK).1, (hz hzK).2.1⟩)
  have hineq' : ∀ᵐ z ∂volume, z ∈ Metric.closedBall c 2 →
      linearizedTrace (A z) (fderiv ℝ (gradient w) z) - inner ℝ (b z) (gradient w z) ≤
        F + 2 * Λ + 4 * M := by
    filter_upwards [hcoeff, hineq, hLip.ae_differentiableAt (μ := volume)] with z hc hi hd
    intro hzK
    have hwd : HasFDerivAt (gradient w)
        (fderiv ℝ (gradient u) z + (2 : ℝ) • ContinuousLinearMap.id ℝ (E m)) z := by
      rw [hgrad]
      exact hd.hasFDerivAt.add (((hasFDerivAt_id z).sub_const c).const_smul (2 : ℝ))
    have hz : ‖z - c‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hzK
    have hinner : -(2 * M) ≤ inner ℝ (b z) (z - c) := by
      have he := (abs_le.mp (abs_real_inner_le_norm (b z) (z - c))).1
      have hb : ‖b z‖ * ‖z - c‖ ≤ M * 2 :=
        mul_le_mul (hc hzK).1 hz (norm_nonneg _) hM
      linarith
    rw [hwd.fderiv, linearizedTrace_add, linearizedTrace_smul, hgrad]
    simp only [inner_add_right, real_inner_smul_right]
    have hi' := hi hzK
    have ht := (hc hzK).2.2
    linarith
  have hxK : x ∈ Metric.closedBall c 2 := Metric.closedBall_subset_closedBall (by norm_num) hx
  have hn : ‖x - c‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hwx : w x ≤ -2 := by
    dsimp [w, sublevelBarrier]
    nlinarith [norm_nonneg (x - c)]
  have hKD : Metric.closedBall c 2 ⊆ Metric.closedBall x 4 := by
    intro z hz
    rw [Metric.mem_closedBall] at *
    have ht := dist_triangle z c x
    rw [dist_comm c x] at ht
    linarith
  have hb := abp_contact_bound hC hdet hw hwLip (isCompact_closedBall c 2) hboundary hδ hM
    hcoeff' hineq' hxK (D := 4) (r := 1 / 4) (by norm_num) hKD (by linarith)
  have hsub : {z | z ∈ Metric.closedBall c 2 ∧ w z < 0} ⊆
      {z | z ∈ Metric.closedBall c 2 ∧ u z < 4} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hh := hz.2
    dsimp [w, sublevelBarrier] at hh
    nlinarith [sq_nonneg ‖z - c‖]
  apply hb.trans
  gcongr 1
  exact measure_mono hsub

end Submission.Obl.Entropy__smooth_gaussian_transport
