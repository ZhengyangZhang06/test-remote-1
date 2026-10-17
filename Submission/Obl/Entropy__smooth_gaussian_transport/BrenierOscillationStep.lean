import Submission.Obl.Entropy__smooth_gaussian_transport.BrenierHessianComparison
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianWeakHarnack
import Submission.Obl.Entropy__smooth_gaussian_transport.CubeDilation
import Submission.Obl.Entropy__smooth_gaussian_transport.OscillationStep

open MeasureTheory ProbabilityTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem directional_difference_le_norm {m : ℕ} (A B : E m →L[ℝ] E m)
    {v : E m} (hv : ‖v‖ = 1) :
    inner ℝ (A v) v - inner ℝ (B v) v ≤ ‖B - A‖ := by
  calc
    _ = inner ℝ ((A - B) v) v := by simp only [sub_apply, inner_sub_left]
    _ ≤ ‖(A - B) v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (‖A - B‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((A - B).le_opNorm v) (norm_nonneg v)
    _ = ‖B - A‖ := by rw [hv, mul_one, mul_one, norm_sub_rev]

/-- Quantitative reduction of the sum of directional Hessian oscillations
from a ball of radius `(m+6)r` to the concentric ball of radius `r`. -/
theorem brenier_hessian_oscillation_step {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ F : Finset (E m), F.Nonempty ∧ (∀ v ∈ F, ‖v‖ = 1) ∧
      ∃ θ B A : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < B ∧ 0 < A ∧
        (∀ᵐ x ∂volume, ∀ᵐ y ∂volume, x ∈ K → y ∈ K →
          ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤
            A * ((∑ v ∈ F, max 0
              (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
                inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) + ‖y - x‖)) ∧
        ∀ (c : E m) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.closedBall c (r * (m + 6)) ⊆ K →
          ∀ l U : E m → ℝ, (∀ v ∈ F, l v ≤ U v) →
            (∀ᵐ x ∂volume, x ∈ Metric.ball c (r * (m + 6)) → ∀ v ∈ F,
              l v ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
                inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ U v) →
            ∃ l' U' : E m → ℝ,
              (∀ v ∈ F, l v ≤ l' v ∧ l' v ≤ U' v ∧ U' v ≤ U v) ∧
              (∀ᵐ x ∂volume, x ∈ Metric.ball c r → ∀ v ∈ F,
                l' v ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
                  inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ U' v) ∧
              (∑ v ∈ F, (U' v - l' v)) ≤ θ * (∑ v ∈ F, (U v - l v)) + B * r := by
  classical
  obtain ⟨F₀, hF₀, A, hA, hcomparison⟩ := brenier_ae_hessian_comparison hm hV ha hH hφ hlaw hK
  let v₀ : E m := (EuclideanSpace.basisFun (Fin m) ℝ) ⟨0, by omega⟩
  have hv₀ : ‖v₀‖ = 1 := (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.norm_eq_one _
  let F := insert v₀ F₀
  have hF : F.Nonempty := Finset.insert_nonempty _ _
  have hFunit (v : E m) (hv : v ∈ F) : ‖v‖ = 1 := by
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hv₀
    · exact hF₀ v hv
  have hσ : 0 < (1 / (2 * (F.card : ℝ))) := by
    have hn : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
    positivity
  obtain ⟨C, hC, hpoint⟩ := brenier_hessian_measure_to_point hm hV ha hH hφ hlaw hK hσ
  obtain ⟨θ, B, hθ, hθ1, hB, hstep⟩ := finite_oscillation_step F hF hA.le hC
  let B' : ℝ := B * (1 + 2 * A * m)
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hcomparisonF : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume, x ∈ K → y ∈ K →
      ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤
        A * ((∑ v ∈ F, max 0
          (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
            inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) + ‖y - x‖) := by
    filter_upwards [hcomparison] with x hx
    filter_upwards [hx] with y hy
    intro hxK hyK
    apply (hy hxK hyK).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply add_le_add _ le_rfl
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _)
      (fun v _ _ => le_max_left (0 : ℝ)
        (inner ℝ ((fderiv ℝ (gradient φ) y) v) v - inner ℝ ((fderiv ℝ (gradient φ) x) v) v))
  refine ⟨F, hF, hFunit, θ, B', A, hθ, hθ1, hB', hA, hcomparisonF, ?_⟩
  intro c r hr hr1 hinside l U hlu hbounds
  let I : Set (Fin m → ℝ) := unitCoordinateBox m
  let μ : Measure (Fin m → ℝ) := volume.restrict I
  let w : E m → (Fin m → ℝ) → ℝ := fun v y =>
    inner ℝ ((fderiv ℝ (gradient φ) (c + r • WithLp.toLp 2 y)) v) v
  have hμuniv : μ univ = volume I := by simp [μ]
  have hμ : 0 < μ univ := by rw [hμuniv]; exact unitCoordinateBox_volume_pos m
  have hμfin : μ univ < ∞ := by rw [hμuniv]; exact (unitCoordinateBox m).measure_coe_lt_top volume
  have hmem : ∀ᵐ x ∂μ, x ∈ I := ae_restrict_mem (unitCoordinateBox m).measurableSet_coe
  have hb : ∀ᵐ x ∂μ, ∀ v ∈ F, l v ≤ w v x ∧ w v x ≤ U v := by
    filter_upwards [ae_restrict_of_ae (ae_coordinate_dilation hbounds c hr.ne'), hmem] with x hx hxi
    exact hx (dilated_cube_mem_ball c hr hxi)
  have hcoord := ae_coordinate_dilation hcomparison c hr.ne'
  have hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ v ∈ F,
      w v x - w v y ≤ A * (∑ j ∈ F, (U j - w j x)) + A * (2 * m * r) := by
    filter_upwards [ae_restrict_of_ae hcoord, hb, hmem] with x hx hbx hxi
    have hcoordY := ae_coordinate_dilation hx c hr.ne'
    filter_upwards [ae_restrict_of_ae hcoordY, hb, hmem] with y hy hby hyi
    intro v hv
    have hxK := hinside (Metric.ball_subset_closedBall (dilated_cube_mem_ball c hr hxi))
    have hyK := hinside (Metric.ball_subset_closedBall (dilated_cube_mem_ball c hr hyi))
    have hcmp := hy hxK hyK
    have hsum : (∑ j ∈ F₀, max 0 (w j y - w j x)) ≤ ∑ j ∈ F, (U j - w j x) := by
      calc
        _ ≤ ∑ j ∈ F, max 0 (w j y - w j x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => le_max_left _ _)
        _ ≤ ∑ j ∈ F, (U j - w j x) := by
          apply Finset.sum_le_sum
          intro j hj
          exact max_le (sub_nonneg.mpr (hbx j hj).2) (sub_le_sub_right (hby j hj).2 _)
    have hd := dilated_cube_distance_le c hr.le hxi hyi
    calc
      w v x - w v y ≤ ‖fderiv ℝ (gradient φ) (c + r • WithLp.toLp 2 y) -
          fderiv ℝ (gradient φ) (c + r • WithLp.toLp 2 x)‖ :=
        directional_difference_le_norm _ _ (hFunit v hv)
      _ ≤ A * ((∑ j ∈ F₀, max 0 (w j y - w j x)) +
          ‖(c + r • WithLp.toLp 2 y) - (c + r • WithLp.toLp 2 x)‖) := hcmp
      _ ≤ A * ((∑ j ∈ F, (U j - w j x)) + 2 * m * r) := by gcongr
      _ = _ := by ring
  have hp (v : E m) (hv : v ∈ F) (t : ℝ)
      (hmass : ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ ≤ μ {x | t ≤ U v - w v x}) :
      ∀ᵐ x ∂μ, t ≤ C * max (r ^ 2) (U v - w v x) := by
    have hupper : ∀ᵐ y ∂volume, y ∈ Metric.ball c (r * (m + 6)) →
        inner ℝ ((fderiv ℝ (gradient φ) y) v) v ≤ U v :=
      hbounds.mono (fun y hy hyl => (hy hyl v hv).2)
    have hm' : ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * volume I ≤
        volume ({x | t ≤ U v - w v x} ∩ I) := by
      simpa only [hμuniv, μ, I, Measure.restrict_apply₀' (unitCoordinateBox m).measurableSet_coe.nullMeasurableSet] using hmass
    have hh := hpoint c r v (U v) t hr hr1 (hFunit v hv) hinside hupper hm'
    have hh' := (PiLp.volume_preserving_toLp (Fin m)).quasiMeasurePreserving.ae hh
    filter_upwards [ae_restrict_of_ae hh', hmem] with x hx hxi
    exact hx (Box.coe_subset_Icc hxi)
  obtain ⟨l', U', hnested, hnew, hwidth⟩ := hstep μ hμ hμfin w l U (r ^ 2)
    (A * (2 * m * r)) (sq_nonneg _) (by positivity) hlu hb hc hp
  refine ⟨l', U', hnested, ae_ball_of_ae_dilated_cube c hr hnew, ?_⟩
  apply hwidth.trans
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have herr : B * (r ^ 2 + A * (2 * m * r)) ≤ B' * r := by
    calc
      _ ≤ B * (r + A * (2 * m * r)) := by gcongr
      _ = _ := by dsimp [B']; ring
  exact add_le_add le_rfl herr

end Submission.Obl.Entropy__smooth_gaussian_transport
