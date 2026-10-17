import Submission.Obl.Entropy__transport_energy_surplus.Hyperbolic

/-!
The final algebraic combination of arithmetic/logarithmic average comparisons
in Proposition 2.5. `D` and `B` below are the averages of `D₀` and `b D₀`.
-/

namespace Submission.Obl.Entropy__transport_energy_surplus

/-- After the average comparisons, the hyperbolic inequalities give the exact
 surplus in the frozen transport-energy statement. -/
theorem pair_coefficient_surplus (m δ D B Mlog Mar : ℝ)
    (hm : 0 ≤ m)
    (hquarter : (3 / 4 : ℝ) * D ^ 2 ≤ D ^ 2 - B ^ 2)
    (hlog : D ^ 2 - B ^ 2 ≤ Mlog)
    (har : (1 + m * (1 - (shc (δ / 2))⁻¹ ^ 2)) * Mlog ≤ Mar) :
    (shc (δ / 2))⁻¹ ^ 2 *
      (D ^ 2 - B ^ 2 +
        (1 + m) / 16 * (δ ^ 2 + δ ^ 4 / 30 + δ ^ 6 / 1680) * D ^ 2) ≤ Mar := by
  let c := shc (δ / 2)
  have hc0 : 0 < c := shc_pos _
  have hc : 1 ≤ c ^ 2 := by
    have h := shc_sq_taylor_lower (δ / 2)
    dsimp [c]
    nlinarith [sq_nonneg (δ / 2), sq_nonneg ((δ / 2) ^ 2), sq_nonneg ((δ / 2) ^ 3)]
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hinv : 0 ≤ 1 - c⁻¹ ^ 2 := by
    rw [inv_pow, sub_nonneg, inv_le_one₀ hc2]
    exact hc
  have hfac : 0 ≤ 1 + m * (1 - c⁻¹ ^ 2) := by positivity
  have hbase := mul_le_mul_of_nonneg_left hlog hfac
  have hmain : (1 + m * (1 - c⁻¹ ^ 2)) * (D ^ 2 - B ^ 2) ≤ Mar :=
    hbase.trans har
  have hmain' := mul_le_mul_of_nonneg_left hmain hc2.le
  have he : c ^ 2 * ((1 + m * (1 - c⁻¹ ^ 2)) * (D ^ 2 - B ^ 2)) =
      (D ^ 2 - B ^ 2) + (1 + m) * (c ^ 2 - 1) * (D ^ 2 - B ^ 2) := by
    field_simp
    ring
  rw [he] at hmain'
  have hquarter' := mul_le_mul_of_nonneg_left hquarter
    (show 0 ≤ (1 + m) * (c ^ 2 - 1) by positivity)
  have hs := mul_le_mul_of_nonneg_right (hyperbolic_surplus_lower m δ hm) (sq_nonneg D)
  change (1 + m) / 16 * (δ ^ 2 + δ ^ 4 / 30 + δ ^ 6 / 1680) * D ^ 2 ≤
    (3 / 4 : ℝ) * (1 + m) * (c ^ 2 - 1) * D ^ 2 at hs
  have hfinal : D ^ 2 - B ^ 2 +
      (1 + m) / 16 * (δ ^ 2 + δ ^ 4 / 30 + δ ^ 6 / 1680) * D ^ 2 ≤ c ^ 2 * Mar := by
    nlinarith only [hmain', hquarter', hs]
  change c⁻¹ ^ 2 * _ ≤ Mar
  rw [inv_pow, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hc2]
  nlinarith only [hfinal]


end Submission.Obl.Entropy__transport_energy_surplus
