import Submission.Obl.Entropy__smooth_gaussian_transport.OscillationAlternative

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- One quantitative oscillation step. Nested interval bounds for finitely
many directional derivatives improve by a uniform factor, with an additive
error coming from the forcing and the comparison equation. -/
theorem finite_oscillation_step {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C) :
    ∃ θ B : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < B ∧
      ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X), 0 < μ univ → μ univ < ∞ →
        ∀ (w : ι → X → ℝ) (l U : ι → ℝ) (k e : ℝ), 0 ≤ k → 0 ≤ e →
          (∀ i ∈ F, l i ≤ U i) →
          (∀ᵐ x ∂μ, ∀ i ∈ F, l i ≤ w i x ∧ w i x ≤ U i) →
          (∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ i ∈ F,
            w i x - w i y ≤ A * (∑ j ∈ F, (U j - w j x)) + e) →
          (∀ i ∈ F, ∀ t : ℝ,
            ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ ≤ μ {x | t ≤ U i - w i x} →
              ∀ᵐ x ∂μ, t ≤ C * max k (U i - w i x)) →
          ∃ l' U' : ι → ℝ,
            (∀ i ∈ F, l i ≤ l' i ∧ l' i ≤ U' i ∧ U' i ≤ U i) ∧
            (∀ᵐ x ∂μ, ∀ i ∈ F, l' i ≤ w i x ∧ w i x ≤ U' i) ∧
            (∑ i ∈ F, (U' i - l' i)) ≤ θ * (∑ i ∈ F, (U i - l i)) + B * (k + e) := by
  classical
  let N : ℝ := F.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Finset.card_pos.mpr hF
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Finset.card_pos.mpr hF
  let P : ℝ := (1 + A * N) * (C + 1)
  have hP1 : 1 ≤ P := by
    have hh : 1 ≤ 1 + A * N := by nlinarith
    exact one_le_mul_of_one_le_of_one_le hh (by linarith)
  have hP : 0 < P := zero_lt_one.trans_le hP1
  let K : ℝ := 2 * N * P
  have hK : 0 < K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := by dsimp [K]; nlinarith [mul_le_mul hN1 hP1 (by norm_num) hN.le]
  let θ : ℝ := 1 - K⁻¹
  let B : ℝ := N * (P + 1)
  have hθ : 0 < θ := by
    have hh : K⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hK (by norm_num)).mpr hK2
    dsimp [θ]
    norm_num at hh
    linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith [inv_pos.mpr hK]
  have hθhalf : 1 / 2 ≤ θ := by
    have hh : K⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hK (by norm_num)).mpr hK2
    dsimp [θ]
    norm_num at hh
    linarith
  refine ⟨θ, B, hθ, hθ1, by dsimp [B]; positivity, ?_⟩
  intro X _ μ hμ hfin w l U k e hk he hlu hbounds hcomparison hpoint
  let D : ℝ := ∑ i ∈ F, (U i - l i)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (hlu i hi))
  let τ : ℝ := D / K
  have hτ : 0 ≤ τ := div_nonneg hD hK.le
  have hpoint' (i : ι) (hi : i ∈ F) (t : ℝ)
      (hmass : ENNReal.ofReal (1 / (2 * (F.card : ℝ))) * μ univ ≤ μ {x | t ≤ U i - w i x}) :
      ∀ᵐ x ∂μ, t ≤ (C + 1) * max k (U i - w i x) := by
    filter_upwards [hpoint i hi t hmass] with x hx
    have hm : 0 ≤ max k (U i - w i x) := hk.trans (le_max_left _ _)
    nlinarith
  have hupper := hbounds.mono (fun x hx i hi => (hx i hi).2)
  rcases finite_oscillation_alternative hμ hfin F hF w U hA (by linarith : 0 < C + 1) hk
    hupper hcomparison hpoint' (τ := τ) with hcase | hcase
  · obtain ⟨i, hi, hgain⟩ := hcase
    let U' : ι → ℝ := fun j => U j - if j = i then τ else 0
    obtain ⟨x, hx, _⟩ := exists_good_outside_of_measure_lt (hbounds.and hgain)
      (s := ∅) (by simpa only [measure_empty] using hμ)
    have hlow : l i ≤ U i - τ := by linarith [(hx.1 i hi).1, hx.2]
    refine ⟨l, U', ?_, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst j
        simpa only [U', ite_true, le_refl, true_and] using And.intro hlow (sub_le_self _ hτ)
      · simp only [U', if_neg hji, sub_zero, le_refl, true_and, and_true]
        exact hlu j hj
    · filter_upwards [hbounds, hgain] with y hy hgy
      intro j hj
      refine ⟨(hy j hj).1, ?_⟩
      by_cases hji : j = i
      · subst j
        simp only [U', ite_true]
        linarith
      · simpa only [U', if_neg hji, sub_zero] using (hy j hj).2
    · have hsum : (∑ j ∈ F, (U' j - l j)) = D - τ := by
        calc
          _ = ∑ j ∈ F, ((U j - l j) - if j = i then τ else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [U']
            ring
          _ = D - τ := by rw [Finset.sum_sub_distrib]; simp [D, hi]
      rw [hsum]
      have heq : D - τ = θ * D := by dsimp [τ, θ]; ring
      rw [heq]
      have herr : 0 ≤ B * (k + e) := by dsimp [B]; positivity
      linarith
  · let b : ℝ := P * (τ + k) + e
    have hb : 0 ≤ b := by dsimp [b]; positivity
    let l' : ι → ℝ := fun i => max (l i) (U i - b)
    refine ⟨l', U, ?_, ?_, ?_⟩
    · intro i hi
      refine ⟨le_max_left _ _, max_le (hlu i hi) (sub_le_self _ hb), le_rfl⟩
    · filter_upwards [hbounds, hcase] with x hx hc
      intro i hi
      refine ⟨max_le (hx i hi).1 ?_, (hx i hi).2⟩
      have hh := hc i hi
      change U i - b ≤ w i x
      dsimp only [b, P, N]
      linarith
    · have hsum : (∑ i ∈ F, (U i - l' i)) ≤ N * b := by
        calc
          _ ≤ ∑ _i ∈ F, b := by
            apply Finset.sum_le_sum
            intro i hi
            have hh : U i - b ≤ l' i := le_max_right _ _
            linarith
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, N]
      have heq : N * b = D / 2 + N * P * k + N * e := by
        dsimp [b, τ, K]
        field_simp
      have hDhalf : D / 2 ≤ θ * D := by nlinarith
      have herr : N * P * k + N * e ≤ B * (k + e) := by
        dsimp [B]
        nlinarith [mul_nonneg hN.le hk, mul_nonneg (mul_nonneg hN.le hP.le) he]
      apply hsum.trans
      rw [heq]
      linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
