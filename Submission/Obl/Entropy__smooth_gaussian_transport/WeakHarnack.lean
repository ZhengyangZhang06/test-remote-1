import Submission.Obl.Entropy__smooth_gaussian_transport.CubeSublevel

open MeasureTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Geometric decay of superlevel measures, the weak Harnack estimate in
distribution form. The constants are independent of the gradient Lipschitz
constant of the supersolution. -/
theorem exists_sublevel_tail_constants {m : ℕ} (hm : 1 ≤ m) {T η : ℝ}
    (hT : 1 < T) (hη : 0 < η) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (u : E m → ℝ), Continuous u →
        HasSublevelMeasure u (Metric.closedBall 0 (m + 4)) T η →
        ∀ k : ℝ, 1 ≤ k → ∀ x ∈ closedBoxRegion (unitCoordinateBox m), u x ≤ k →
          ∀ n : ℕ,
            volume ({y : Fin m → ℝ | Q ^ n * k < u (WithLp.toLp 2 y)} ∩
              (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
            ENNReal.ofReal (θ ^ n) * volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
  let Q : ℝ := T ^ (2 * m + 1)
  let κ : ℝ := min (1 / 2) (η / (2 : ℝ) ^ m)
  let θ : ℝ := 1 - κ
  have hQ : 1 < Q := one_lt_pow₀ hT (by omega)
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hκhalf : κ ≤ 1 / 2 := min_le_left _ _
  have hκ1 : κ ≤ 1 := by linarith
  have hκη : κ * (2 : ℝ) ^ m ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  refine ⟨Q, θ, hQ, hθ, hθ1, ?_⟩
  intro u hu h k hk x hx hux
  let f : (Fin m → ℝ) → ℝ := fun y => u (WithLp.toLp 2 y)
  have hf : Continuous f := hu.comp (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ))
  have hbase : volume ({y | Q * k < f y} ∩ (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
      ENNReal.ofReal θ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
    apply cube_superlevel_small hm hu h hT.le hη hκ.le hκ1 hκη le_rfl le_rfl
      (r := 1) (by norm_num) le_rfl hk
      (fun _ => by norm_num [unitCoordinateBox]) (fun _ => by norm_num [unitCoordinateBox]) hx hux
  have hstep (n : ℕ) :
      volume ({y | Q ^ (n + 1) * k < f y} ∩ (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
        ENNReal.ofReal θ *
          volume ({y | Q ^ n * k < f y} ∩ (unitCoordinateBox m : Set (Fin m → ℝ))) := by
    apply box_levelset_measure_decay volume (unitCoordinateBox m) hf
      (show Q ^ n * k < Q ^ (n + 1) * k by
        rw [pow_succ]
        have hn := pow_pos (zero_lt_one.trans hQ) n
        have hk0 : 0 < k := zero_lt_one.trans_le hk
        simpa only [mul_one] using mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hQ hn) hk0)
      (Q := IsCoordinateCube) (unitCoordinateBox_isCube m)
      (fun _ hJ s => hJ.split s) ?_ ?_
    · apply le_trans _ hbase
      apply measure_mono
      intro y hy
      refine ⟨?_, hy.2⟩
      have hn : Q ≤ Q ^ (n + 1) := le_self_pow₀ hQ.le (by omega)
      exact (mul_le_mul_of_nonneg_right hn (zero_le_one.trans hk)).trans_lt hy.1
    · intro J hJ hcube s hheavy y hy
      by_contra hn
      have hyu : u (WithLp.toLp 2 y) ≤ Q ^ n * k := le_of_not_gt hn
      obtain ⟨ℓ, hℓ, hwidth⟩ := hcube
      have hℓ2 := coordinate_cube_side_le_two hm hJ hwidth
      have hr : 0 < ℓ / 4 := by positivity
      have hr1 : ℓ / 4 ≤ 1 := by linarith
      have hk' : 1 ≤ Q ^ n * k :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ.le) hk
      have hchild (i : Fin m) :
          (J.splitCenterBox s).upper i - (J.splitCenterBox s).lower i = 2 * (ℓ / 4) := by
        rw [Box.upper_sub_lower_splitCenterBox, hwidth]
        ring
      have hparent (i : Fin m) : J.upper i - J.lower i ≤ 4 * (ℓ / 4) := by
        rw [hwidth]
        linarith
      have hy' : WithLp.toLp 2 y ∈ closedBoxRegion J := Box.coe_subset_Icc hy
      have hsmall := cube_superlevel_small hm hu h hT.le hη hκ.le hκ1 hκη hJ
        (J.splitCenterBox_le s) hr hr1 hk' hchild hparent hy' hyu
      change volume ({z | Q * (Q ^ n * k) < f z} ∩
        (J.splitCenterBox s : Set (Fin m → ℝ))) ≤
          ENNReal.ofReal θ * volume (J.splitCenterBox s : Set (Fin m → ℝ)) at hsmall
      have he : Q * (Q ^ n * k) = Q ^ (n + 1) * k := by rw [pow_succ]; ring
      rw [he] at hsmall
      exact (not_lt_of_ge hsmall) hheavy
  intro n
  change volume ({y | Q ^ n * k < f y} ∩ (unitCoordinateBox m : Set (Fin m → ℝ))) ≤ _
  induction n with
  | zero =>
    simpa only [pow_zero, ENNReal.ofReal_one, one_mul] using
      (measure_mono (inter_subset_right :
        {y | k < f y} ∩ (unitCoordinateBox m : Set (Fin m → ℝ)) ⊆ _))
  | succ n ih =>
    calc
      _ ≤ ENNReal.ofReal θ * volume ({y | Q ^ n * k < f y} ∩
          (unitCoordinateBox m : Set (Fin m → ℝ))) := hstep n
      _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (θ ^ n) *
          volume (unitCoordinateBox m : Set (Fin m → ℝ))) := by gcongr
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hθ.le, mul_comm θ (θ ^ n), ← pow_succ]

def HasWeakHarnackTail {m : ℕ} (u : E m → ℝ) (Q θ : ℝ) : Prop :=
  ∀ k : ℝ, 1 ≤ k → ∀ x ∈ closedBoxRegion (unitCoordinateBox m), u x ≤ k →
    ∀ n : ℕ,
      volume ({y : Fin m → ℝ | Q ^ n * k < u (WithLp.toLp 2 y)} ∩
        (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
      ENNReal.ofReal (θ ^ n) * volume (unitCoordinateBox m : Set (Fin m → ℝ))

theorem exists_elliptic_weakHarnack {m : ℕ} (hm : 1 ≤ m) {δ Λ M : ℝ}
    (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    ∃ Q θ : ℝ, 1 < Q ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (u : E m → ℝ) (L : NNReal) (A : E m → E m →L[ℝ] E m) (b : E m → E m),
        ContDiff ℝ 1 u → LipschitzWith L (gradient u) →
        (∀ z ∈ Metric.closedBall (0 : E m) (m + 4), 0 ≤ u z) →
        (∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : E m) (m + 4) → ‖b z‖ ≤ M ∧
          (∀ B : E m →L[ℝ] E m, (operatorMatrix B).PosSemidef →
            δ * ‖B‖ ≤ linearizedTrace (A z) B) ∧
          linearizedTrace (A z) (ContinuousLinearMap.id ℝ (E m)) ≤ Λ) →
        (∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : E m) (m + 4) →
          linearizedTrace (A z) (fderiv ℝ (gradient u) z) -
            inner ℝ (b z) (gradient u z) ≤ 1) →
        HasWeakHarnackTail u Q θ := by
  obtain ⟨T, η, hT, hη, hsub⟩ := exists_sublevel_measure hm hδ hΛ hM
  obtain ⟨Q, θ, hQ, hθ, hθ1, htail⟩ := exists_sublevel_tail_constants hm hT hη
  refine ⟨Q, θ, hQ, hθ, hθ1, ?_⟩
  intro u L A b hu hLip hu0 hcoeff hineq
  exact htail u hu.continuous
    (hsub u L A b _ hu hLip hu0 hcoeff hineq)

end Submission.Obl.Entropy__smooth_gaussian_transport
