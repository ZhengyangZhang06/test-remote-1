import Submission.Obl.Entropy__smooth_gaussian_transport.WeakHarnack

open MeasureTheory Set Filter BoxIntegral
open scoped Topology RealInnerProductSpace NNReal ENNReal

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A positive fraction of a superlevel set forces a lower bound at every
point of the cube. This consequence is convenient for oscillation estimates. -/
theorem weakHarnack_measure_to_point {m : ℕ} {Q θ σ : ℝ}
    (hQ : 1 < Q) (hθ : 0 < θ) (hθ1 : θ < 1) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : E m → ℝ), HasWeakHarnackTail u Q θ →
      ∀ t : ℝ,
        ENNReal.ofReal σ * volume (unitCoordinateBox m : Set (Fin m → ℝ)) ≤
          volume ({y : Fin m → ℝ | t ≤ u (WithLp.toLp 2 y)} ∩
            (unitCoordinateBox m : Set (Fin m → ℝ))) →
        ∀ x ∈ closedBoxRegion (unitCoordinateBox m), t ≤ C * max 1 (u x) := by
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).eventually
    (gt_mem_nhds hσ)).exists
  refine ⟨Q ^ N, pow_pos (zero_lt_one.trans hQ) N, ?_⟩
  intro u hu t hmass x hx
  by_contra hn
  have ht : Q ^ N * max 1 (u x) < t := lt_of_not_ge hn
  have htail := hu (max 1 (u x)) (le_max_left _ _) x hx (le_max_right _ _) N
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
