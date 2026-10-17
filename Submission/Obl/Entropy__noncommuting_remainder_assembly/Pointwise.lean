import Submission.Obl.Entropy__noncommuting_remainder_assembly.CFCProducts

open scoped BigOperators
open Submission.Lib.MatrixEntropy

namespace Submission.Obl.Entropy__noncommuting_remainder_assembly

variable {ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- The pointwise block and weighted completions following Lemma 3.4. -/
lemma pointwise_weighted_remainder (X : ν → Matrix ι ι ℝ)
    (hX : ∀ r, (X r).IsHermitian) (A Y : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hY : Y.IsHermitian)
    (b h p : ℝ → ℝ) (hp : ∀ a, 0 < p a)
    (D L M g : ν → Matrix ι ι ℝ) (hg : ∀ r, (g r).IsHermitian) :
    let cost := fun a => (40 / 37 : ℝ) * ((b a - 7 / 25) ^ 2 + (5 / 96) * (h a) ^ 2 / p a);
    let B := ∑ r, X r * X r;
    let S := ((37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B)⁻¹;
    let T := S - 1;
    let H := -T * (B - 1);
    let ρ := (3 / 20 : ℝ) • (1 : Matrix ι ι ℝ) + (1813 / 4000 : ℝ) • S;
    let v := fun r => D r - (7 / 25 : ℝ) • g r;
    let F := Y * (cfc b A - (7 / 25 : ℝ) • 1) + ∑ r, X r * L r;
    -Matrix.trace (H * cfc p A) +
      Matrix.trace (T * (Y * cfc h A + ∑ r, X r * M r)) +
      Matrix.trace (F.transpose * S * F) +
      (∑ r, Matrix.trace ((v r).transpose * S * v r)) +
      (9 / 16 : ℝ) * Matrix.trace (T * ∑ r, g r * g r) ≤
    -Matrix.trace (H * ρ * cfc p A) + Matrix.trace (Y * Y * cfc cost A) +
      (∑ r, ((40 / 37 : ℝ) * squareSum (v r) + (27 / 592 : ℝ) * squareSum (g r) +
        (40 / 3 : ℝ) * squareSum (L r) +
        (5 / 17 : ℝ) * squareSum (M r * cfc (fun a => (Real.sqrt (p a))⁻¹) A))) := by
  intro cost B S T H ρ v F
  have hXs (r : ν) : (X r).transpose = X r := by simpa using (hX r).eq
  have hgs (r : ν) : (g r).transpose = g r := by simpa using (hg r).eq
  have hB : B.PosSemidef := Matrix.posSemidef_sum _ fun r _ => by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hXs] using
      Matrix.posSemidef_self_mul_conjTranspose (X r)
  let Q := (37 / 40 : ℝ) • (1 : Matrix ι ι ℝ) + (3 / 40 : ℝ) • B
  have hQ : Q.PosDef := (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 37 / 40)).add_posSemidef
    (hB.smul (by norm_num : (0 : ℝ) ≤ 3 / 40))
  have hS : S.PosDef := hQ.inv
  have hinv : S⁻¹ = (40 / 37 : ℝ)⁻¹ • (1 : Matrix ι ι ℝ) +
      (3 / 40 : ℝ) • ∑ r, X r * (X r).transpose := by
    norm_num
    simpa only [S, Q, B, hXs] using
      Matrix.nonsing_inv_nonsing_inv Q (Matrix.isUnit_iff_isUnit_det _ |>.mp hQ.isUnit)
  have hprod : Q * S = 1 := Matrix.mul_nonsing_inv _
    (Matrix.isUnit_iff_isUnit_det _ |>.mp hQ.isUnit)
  have hlinear : (37 / 40 : ℝ) • S + (3 / 40 : ℝ) • (B * S) = 1 := by
    simpa only [Q, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] using hprod
  have hrel : (3 / 40 : ℝ) • ((B - 1) * S) = -T := by
    calc
      _ = ((37 / 40 : ℝ) • S + (3 / 40 : ℝ) • (B * S)) - S := by
        simp only [Matrix.sub_mul, Matrix.one_mul, smul_sub]
        module
      _ = 1 - S := by rw [hlinear]
      _ = -T := by simp [T]
  have hT2 : T * T = (3 / 40 : ℝ) • (H * S) := by
    calc
      _ = -(T * ((3 / 40 : ℝ) • ((B - 1) * S))) := by rw [hrel]; simp
      _ = _ := by simp only [H, Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_neg]
  have hT : T.IsHermitian := hS.isHermitian.sub Matrix.isHermitian_one
  have hTS : Commute T S := by change (S - 1) * S = S * (S - 1); noncomm_ring
  have hP := matrix_cfc_posDef A hA p hp
  have hw := entropy_weighted_completion X M (Y * cfc h A) T H S (cfc p A)
    (s := 40 / 37) (α := 3 / 40) (ε := 3 / 20) (κ := 49 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hS hP hT hTS hinv hT2
  have hρ : ((1 - 3 / 20 : ℝ) • (1 : Matrix ι ι ℝ) -
      ((49 / 100 : ℝ) / (40 / 37)) • S) = 1 - ρ := by
    dsimp [ρ]
    module
  rw [hρ, ← squareSum_cfc_inverse_sqrt (Y * cfc h A) A hA p hp] at hw
  simp_rw [← squareSum_cfc_inverse_sqrt (M _) A hA p hp] at hw
  norm_num at hw
  have hblock := matrix_block_bound_add X L (Y * (cfc b A - (7 / 25 : ℝ) • 1))
    (s := 40 / 37) (α := 3 / 40) (by norm_num) (by norm_num) S hS hinv
  simp only [← squareSum_trace] at hblock
  norm_num only at hblock
  have hweight (a : Matrix ι ι ℝ) : Matrix.trace (a.transpose * S * a) ≤
      (40 / 37 : ℝ) * squareSum a := by
    have hh := matrix_block_bound_add X (fun _ => 0) a
      (s := 40 / 37) (α := 3 / 40) (by norm_num) (by norm_num) S hS hinv
    simpa [squareSum_trace] using hh
  have hv := Finset.sum_le_sum (s := Finset.univ) fun r _ => hweight (v r)
  have hgw := Finset.sum_le_sum (s := Finset.univ) fun r _ => hweight (g r)
  have hgeq : Matrix.trace (T * ∑ r, g r * g r) =
      (∑ r, Matrix.trace ((g r).transpose * S * g r)) - ∑ r, squareSum (g r) := by
    simp only [Matrix.trace_sum, Matrix.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [T]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, squareSum_trace, hgs]
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle S (g r) (g r)
  have hgb : (9 / 16 : ℝ) * Matrix.trace (T * ∑ r, g r * g r) ≤
      (27 / 592 : ℝ) * ∑ r, squareSum (g r) := by
    rw [hgeq]
    rw [← Finset.mul_sum] at hgw
    linarith
  have hcost := cfc_cost_identity Y A hY hA b h p hp
  have hreserve : -Matrix.trace (H * cfc p A) + Matrix.trace (H * (1 - ρ) * cfc p A) =
      -Matrix.trace (H * ρ * cfc p A) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub]
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hv ⊢
  change -_ + _ + _ + _ + _ ≤ -_ + Matrix.trace (Y * Y * cfc cost A) + _
  linarith

end Submission.Obl.Entropy__noncommuting_remainder_assembly
