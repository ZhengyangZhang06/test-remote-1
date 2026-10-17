import Submission.Obl.Entropy__smooth_gaussian_transport.WeakHarnackLimit

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_good_outside_of_measure_lt {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {s : Set X}
    (hs : μ s < μ univ) : ∃ x, P x ∧ x ∉ s := by
  by_contra hn
  push Not at hn
  have hmem : ∀ᵐ x ∂μ, x ∈ s := hP.mono (fun x hx => hn x hx)
  have hh : μ univ ≤ μ s := measure_mono_ae (hmem.mono (fun x hx _ => hx))
  exact (not_le_of_gt hs) hh

/-- The oscillation alternative: either one directional upper bound improves,
or all directional functions lie close to their upper bounds. Weak Harnack
controls the exceptional sets; the comparison inequality transfers a common
near-maximal point to almost every point. -/
theorem finite_oscillation_alternative {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (hμ : 0 < μ univ) (hfin : μ univ < ∞)
    (F : Finset ι) (hF : F.Nonempty) (w : ι → X → ℝ) (U : ι → ℝ)
    {A C k e τ : ℝ} (hA : 0 ≤ A) (hC : 0 < C) (hk : 0 ≤ k)
    (hupper : ∀ᵐ x ∂μ, ∀ i ∈ F, w i x ≤ U i)
    (hcomparison : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ i ∈ F,
      w i x - w i y ≤ A * (∑ j ∈ F, (U j - w j x)) + e)
    (hpoint : ∀ i ∈ F, ∀ t : ℝ,
      ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ ≤ μ {x | t ≤ U i - w i x} →
      ∀ᵐ x ∂μ, t ≤ C * max k (U i - w i x)) :
    (∃ i ∈ F, ∀ᵐ x ∂μ, τ ≤ U i - w i x) ∨
      (∀ᵐ x ∂μ, ∀ i ∈ F,
        U i - w i x ≤ (1 + A * (F.card : ℝ)) * C * (τ + k) + e) := by
  classical
  by_cases hcase : ∃ i ∈ F, ∀ᵐ x ∂μ, τ ≤ U i - w i x
  · exact Or.inl hcase
  right
  have hN : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  let t : ℝ := C * (τ + k)
  let bad : ι → Set X := fun i => {x | t ≤ U i - w i x}
  have hsmall (i : ι) (hi : i ∈ F) : μ (bad i) <
      ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ := by
    by_contra hn
    have hp := hpoint i hi t (le_of_not_gt hn)
    apply hcase
    refine ⟨i, hi, ?_⟩
    filter_upwards [hp, hupper] with x hx hux
    have hd : 0 ≤ U i - w i x := sub_nonneg.mpr (hux i hi)
    have hm : max k (U i - w i x) ≤ k + (U i - w i x) := max_le (by linarith) (by linarith)
    change C * (τ + k) ≤ C * max k (U i - w i x) at hx
    have hh := le_of_mul_le_mul_left hx hC
    linarith
  have hunion : μ (⋃ i ∈ F, bad i) ≤ ENNReal.ofReal (1 / 2 : ℝ) * μ univ := by
    calc
      _ ≤ ∑ i ∈ F, μ (bad i) := measure_biUnion_finset_le F bad
      _ ≤ ∑ _i ∈ F, ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ :=
        Finset.sum_le_sum (fun i hi => (hsmall i hi).le)
      _ = ENNReal.ofReal (1 / 2 : ℝ) * μ univ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← mul_assoc,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
        congr 2
        field_simp
  have hstrict : ENNReal.ofReal (1 / 2 : ℝ) * μ univ < μ univ := by
    calc
      _ < 1 * μ univ := by
        apply (ENNReal.mul_lt_mul_iff_left hμ.ne' hfin.ne).mpr
        norm_num
      _ = _ := one_mul _
  obtain ⟨x, hx, hxgood⟩ := exists_good_outside_of_measure_lt hcomparison (hunion.trans_lt hstrict)
  have hdef (i : ι) (hi : i ∈ F) : U i - w i x ≤ t := by
    have hn : x ∉ bad i := fun hb => hxgood (mem_iUnion₂.mpr ⟨i, hi, hb⟩)
    exact (lt_of_not_ge hn).le
  have hsum : (∑ j ∈ F, (U j - w j x)) ≤ (F.card : ℝ) * t := by
    calc
      _ ≤ ∑ _j ∈ F, t := Finset.sum_le_sum hdef
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  filter_upwards [hx] with y hy
  intro i hi
  have hh := hy i hi
  have hs := mul_le_mul_of_nonneg_left hsum hA
  have hd := hdef i hi
  change U i - w i y ≤ (1 + A * (F.card : ℝ)) * C * (τ + k) + e
  dsimp only [t] at hs hd
  nlinarith

end Submission.Obl.Entropy__smooth_gaussian_transport
