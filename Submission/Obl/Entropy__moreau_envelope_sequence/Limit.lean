import Submission.Obl.Entropy__moreau_envelope_sequence.Minimizer

noncomputable section
open Set Filter Topology

namespace Submission.Obl.Entropy__moreau_envelope_sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weight_max_tendsto {f : E → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hu : UpperSemicontinuous f) {b : ℝ} (hb : ∀ y, f y ≤ Real.exp b)
    (x : E) (p : ℕ → E)
    (hmax : ∀ (n : ℕ) y, weight f ((n : ℝ) + 1) x y ≤ weight f ((n : ℝ) + 1) x (p n)) :
    Tendsto (fun n : ℕ => weight f ((n : ℝ) + 1) x (p n)) atTop (𝓝 (f x)) := by
  have hlo (n : ℕ) : f x ≤ weight f ((n : ℝ) + 1) x (p n) := by
    simpa [weight] using hmax n x
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le (hlo n))
  · intro u hu'
    have hu0 : 0 < u := (hf x).trans_lt hu'
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hu x u hu')
    have hgrowth : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / 2 * δ ^ 2) atTop atTop := by
      have h := (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).atTop_mul_const (by positivity : 0 < δ ^ 2 / 2)
      convert h using 1
      ext n
      ring
    have hdecay : Tendsto (fun n : ℕ => Real.exp (b - ((n : ℝ) + 1) / 2 * δ ^ 2))
        atTop (𝓝 0) := by
      exact Real.tendsto_exp_atBot.comp
        (tendsto_atBot_add_const_left atTop b (tendsto_neg_atTop_atBot.comp hgrowth))
    filter_upwards [hdecay.eventually (Iio_mem_nhds hu0)] with n hn
    by_cases hp : p n ∈ Metric.ball x δ
    · exact (weight_le hf (by positivity) x (p n)).trans_lt (hball hp)
    · have hd : δ ≤ ‖x - p n‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hp
      have hsq : δ ^ 2 ≤ ‖x - p n‖ ^ 2 := by nlinarith [norm_nonneg (x - p n)]
      calc
        weight f ((n : ℝ) + 1) x (p n)
          ≤ Real.exp b * Real.exp (-(((n : ℝ) + 1) / 2 * ‖x - p n‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right (hb (p n)) (Real.exp_pos _).le
        _ ≤ Real.exp b * Real.exp (-(((n : ℝ) + 1) / 2 * δ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Real.exp_le_exp.mpr
          have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ ((n : ℝ) + 1) / 2)
          linarith
        _ = Real.exp (b - ((n : ℝ) + 1) / 2 * δ ^ 2) := by rw [← Real.exp_add]; rfl
        _ < u := hn

end Submission.Obl.Entropy__moreau_envelope_sequence
