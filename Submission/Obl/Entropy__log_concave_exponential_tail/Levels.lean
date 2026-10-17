import Submission.Obl.Entropy__log_concave_exponential_tail.Geometry

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.Entropy__log_concave_exponential_tail

/-- A log-concave probability density has a bounded positive superlevel set
and a point strictly above that level. -/
theorem exists_bounded_superlevel {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfuc : UpperSemicontinuous f)
    (hfconc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hfint : Integrable f volume) (hfmass : ∫ x, f x = 1) :
    ∃ t : ℝ, ∃ c : EuclideanSpace ℝ (Fin m),
      0 < t ∧ t < f c ∧ Bornology.IsBounded {x | t ≤ f x} := by
  have hsupp : 0 < volume (Function.support f) :=
    (integral_pos_iff_support_of_nonneg hf0 hfint).mp (by rw [hfmass]; norm_num)
  have hlevel : ∃ u : ℝ, 0 < u ∧ 0 < volume {x | u ≤ f x} := by
    by_contra! h
    have hnull : volume (⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) ≤ f x}) = 0 := by
      apply measure_iUnion_null
      intro n
      exact le_zero_iff.mp (h _ (by positivity))
    have hsub : Function.support f ⊆ ⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) ≤ f x} := by
      intro x hx
      have hxpos : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hxpos
      exact mem_iUnion.mpr ⟨n, hn.le⟩
    exact hsupp.ne' (measure_mono_null hsub hnull)
  obtain ⟨u, hu, hupos⟩ := hlevel
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hupos.ne'
  let t : ℝ := u / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htc : t < f c := by dsimp [t]; dsimp at hc; linarith
  have heq : {x | t ≤ f x} = {x ∈ {x | 0 < f x} | Real.log t ≤ Real.log (f x)} := by
    ext x
    constructor
    · intro hx
      have hxpos : 0 < f x := ht.trans_le hx
      exact ⟨hxpos, (Real.log_le_log_iff ht hxpos).mpr hx⟩
    · rintro ⟨hxpos, hx⟩
      exact (Real.log_le_log_iff ht hxpos).mp hx
  have hconv : Convex ℝ {x | t ≤ f x} := by
    rw [heq]
    exact hfconc.convex_ge (Real.log t)
  have hmeas : MeasurableSet {x | t ≤ f x} := (hfuc.isClosed_preimage t).measurableSet
  have hpos : 0 < volume {x | t ≤ f x} := hupos.trans_le (measure_mono (by
    intro x hx
    dsimp [t] at *
    linarith))
  exact ⟨t, c, ht, htc,
    convex_isBounded_of_volume hconv hmeas hpos (hfint.measure_ge_lt_top ht)⟩

end Submission.Obl.Entropy__log_concave_exponential_tail
