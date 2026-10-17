import Submission.Obl.Entropy__smooth_gaussian_transport.WeakHarnackPoint

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Superlevel measure bounds pass to almost-everywhere pointwise limits.
No regularity of the limiting function is needed. -/
theorem measure_superlevel_le_of_ae_tendsto {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ} {a : ℝ} {B : ℝ≥0∞}
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ᶠ n in atTop, μ {x | a < f n x} ≤ B) :
    μ {x | a < g x} ≤ B := by
  let S : ℕ → Set X := fun n => ⋂ k ≥ n, {x | a < f k x}
  have hmono : Monotone S := by
    intro n n' hnn x hx
    simp only [S, mem_iInter] at hx ⊢
    exact fun k hk => hx k (hnn.trans hk)
  have hsub : {x | a < g x} ≤ᵐ[μ] ⋃ n, S n := by
    filter_upwards [hlim] with x hx hax
    obtain ⟨n, hn⟩ := eventually_atTop.mp (hx.eventually (lt_mem_nhds hax))
    exact mem_iUnion.mpr ⟨n, by simpa only [S, mem_iInter, mem_ofPred_eq] using hn⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  calc
    μ {x | a < g x} ≤ μ (⋃ n, S n) := measure_mono_ae hsub
    _ = ⨆ n, μ (S n) := hmono.measure_iUnion
    _ ≤ B := by
      apply iSup_le
      intro n
      apply le_trans (measure_mono (show S n ⊆ {x | a < f (max n N) x} from ?_))
        (hN (max n N) (le_max_right _ _))
      intro x hx
      exact mem_iInter.mp (mem_iInter.mp hx (max n N)) (le_max_left _ _)

def HasAeWeakHarnackTail {m : ℕ} (u : E m → ℝ) (Q θ : ℝ) : Prop :=
  ∀ᵐ x ∂volume, ∀ k : ℝ, 1 ≤ k → x ∈ closedBoxRegion (unitCoordinateBox m) → u x ≤ k →
    ∀ n : ℕ,
      volume ({y : Fin m → ℝ | Q ^ n * k < u (WithLp.toLp 2 y)} ∩
        (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
      ENNReal.ofReal (θ ^ n) * volume (unitCoordinateBox m : Set (Fin m → ℝ))

/-- Uniform weak Harnack tails are stable under almost-everywhere convergence.
The geometric threshold is enlarged by a factor of two. -/
theorem ae_weakHarnack_of_ae_tendsto {m : ℕ} {u : ℕ → E m → ℝ} {w : E m → ℝ}
    {Q θ : ℝ} (hQ : 0 < Q) (hu : ∀ n, HasWeakHarnackTail (u n) Q θ)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (w x))) :
    HasAeWeakHarnackTail w (2 * Q) θ := by
  have hlim' : ∀ᵐ y : Fin m → ℝ ∂volume,
      Tendsto (fun n => u n (WithLp.toLp 2 y)) atTop (𝓝 (w (WithLp.toLp 2 y))) :=
    (PiLp.volume_preserving_toLp (Fin m)).quasiMeasurePreserving.ae hlim
  filter_upwards [hlim] with x hx
  intro k hk hxi hwx n
  cases n with
  | zero =>
    simpa only [pow_zero, ENNReal.ofReal_one, one_mul] using
      (measure_mono (inter_subset_right :
        {y : Fin m → ℝ | k < w (WithLp.toLp 2 y)} ∩
          (unitCoordinateBox m : Set (Fin m → ℝ)) ⊆ _))
  | succ n =>
    have hk0 : 0 < k := zero_lt_one.trans_le hk
    have hevent : ∀ᶠ j in atTop, u j x ≤ 2 * k :=
      (hx.eventually (gt_mem_nhds (by linarith : w x < 2 * k))).mono fun _ h => h.le
    have htail : ∀ᶠ j in atTop,
        volume ({y : Fin m → ℝ | Q ^ (n + 1) * (2 * k) < u j (WithLp.toLp 2 y)} ∩
          (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
        ENNReal.ofReal (θ ^ (n + 1)) * volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
      filter_upwards [hevent] with j hj
      exact hu j (2 * k) (by linarith) x hxi hj (n + 1)
    have hμlim := ae_restrict_of_ae (s := (unitCoordinateBox m : Set (Fin m → ℝ))) hlim'
    have hb := measure_superlevel_le_of_ae_tendsto (μ := volume.restrict
      (unitCoordinateBox m : Set (Fin m → ℝ)))
      (a := Q ^ (n + 1) * (2 * k))
      (B := ENNReal.ofReal (θ ^ (n + 1)) * volume (unitCoordinateBox m : Set (Fin m → ℝ))) hμlim ?_
    · have hb' : volume ({y : Fin m → ℝ | Q ^ (n + 1) * (2 * k) < w (WithLp.toLp 2 y)} ∩
          (unitCoordinateBox m : Set (Fin m → ℝ))) ≤
          ENNReal.ofReal (θ ^ (n + 1)) * volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
        simpa only [Measure.restrict_apply₀' (unitCoordinateBox m).measurableSet_coe.nullMeasurableSet] using hb
      apply le_trans (measure_mono ?_) hb'
      intro y hy
      refine ⟨?_, hy.2⟩
      change Q ^ (n + 1) * (2 * k) < w (WithLp.toLp 2 y)
      apply lt_of_le_of_lt _ hy.1
      have hp : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow₀ (by norm_num) (by omega)
      calc
        Q ^ (n + 1) * (2 * k) = 2 * (Q ^ (n + 1) * k) := by ring
        _ ≤ 2 ^ (n + 1) * (Q ^ (n + 1) * k) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg (pow_nonneg hQ.le _) hk0.le)
        _ = (2 * Q) ^ (n + 1) * k := by rw [mul_pow]; ring
    · filter_upwards [htail] with j hj
      simpa only [Measure.restrict_apply₀' (unitCoordinateBox m).measurableSet_coe.nullMeasurableSet] using hj

/-- Distributional weak Harnack gives the same measure-to-point estimate at
almost every point, sufficient for an essential oscillation argument. -/
theorem ae_weakHarnack_measure_to_point {m : ℕ} {Q θ σ : ℝ}
    (hQ : 1 < Q) (hθ : 0 < θ) (hθ1 : θ < 1) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E m → ℝ, HasAeWeakHarnackTail u Q θ →
      ∀ t : ℝ,
        ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
          volume ({y : Fin m → ℝ | t ≤ u (WithLp.toLp 2 y)} ∩
            (unitCoordinateBox m : Set (Fin m → ℝ))) →
        ∀ᵐ x ∂volume, x ∈ closedBoxRegion (unitCoordinateBox m) →
          t ≤ C * max 1 (u x) := by
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).eventually
    (gt_mem_nhds hσ)).exists
  refine ⟨Q ^ N, pow_pos (zero_lt_one.trans hQ) N, ?_⟩
  intro u hu t hmass
  filter_upwards [hu] with x hx hxi
  by_contra hn
  have ht : Q ^ N * max 1 (u x) < t := lt_of_not_ge hn
  have htail := hx (max 1 (u x)) (le_max_left _ _) hxi (le_max_right _ _) N
  have hsubset : {y : Fin m → ℝ | t ≤ u (WithLp.toLp 2 y)} ∩
      (unitCoordinateBox m : Set (Fin m → ℝ)) ⊆
      {y | Q ^ N * max 1 (u x) < u (WithLp.toLp 2 y)} ∩
        (unitCoordinateBox m : Set (Fin m → ℝ)) := by
    intro y hy
    exact ⟨ht.trans_le hy.1, hy.2⟩
  have hvol : 0 < volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
    rw [coordinate_cube_volume (ℓ := 2) (by norm_num)
      (fun _ => by norm_num [unitCoordinateBox])]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hfin := (unitCoordinateBox m).measure_coe_lt_top volume
  have hstrict : ENNReal.ofReal (θ ^ N) * volume (unitCoordinateBox m : Set (Fin m → ℝ)) <
      ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) := by
    apply (ENNReal.mul_lt_mul_iff_left hvol.ne' hfin.ne).mpr
    exact (ENNReal.ofReal_lt_ofReal_iff hσ).mpr hN
  exact (not_le_of_gt hstrict) (hmass.trans ((measure_mono hsubset).trans htail))

end Submission.Obl.Entropy__smooth_gaussian_transport
