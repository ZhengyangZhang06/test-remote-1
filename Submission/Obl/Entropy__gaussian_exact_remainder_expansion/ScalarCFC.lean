import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Scalar

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cfc_scalar_identities (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (2:ℝ) • cfc t A - cfc k A * cfc k A =
      A * cfc f A - cfc (deriv f) A + cfc b A * cfc b A + 1 ∧
    cfc p A = cfc (deriv f) A - cfc b A * cfc b A -
      (40/3:ℝ) • (cfc l A * cfc l A) ∧
    cfc h A = cfc f A - (3/2:ℝ) • cfc k A -
      (80/3:ℝ) • ((cfc b A - (7/25:ℝ) • 1) * cfc l A) := by
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := A.finite_real_spectrum.continuousOn g
  have hsa : IsSelfAdjoint A := hA
  have ht := congrArg (fun g : ℝ → ℝ => cfc g A) (funext scalar_multiplier_identity)
  constructor
  · simpa only [cfc_sub _ _ _ (hc _) (hc _), cfc_add _ _ _ (hc _) (hc _),
      cfc_const_mul _ _ _ (hc _), cfc_mul _ _ _ (hc _) (hc _),
      cfc_pow _ _ _ (hc _) hsa, cfc_id' ℝ A hsa, cfc_const_one ℝ A,
      pow_two] using ht
  constructor
  · unfold p
    simp only [ cfc_sub _ _ _ (hc _) (hc _), cfc_const_mul _ _ _ (hc _),
      cfc_pow _ _ _ (hc _) hsa, cfc_mul _ _ _ (hc _) (hc _), pow_two]
  · unfold h
    simp only [ cfc_sub _ _ _ (hc _) (hc _), cfc_const_mul _ _ _ (hc _),
      cfc_mul _ _ _ (hc _) (hc _), cfc_const _ _ hsa, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc]

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
