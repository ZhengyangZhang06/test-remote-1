import Submission.Obl.Entropy__gaussian_chaos_resolvent.HermiteCompleteness
import Submission.Obl.Entropy__gaussian_chaos_resolvent.L2Products

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

noncomputable def gaussianPi (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

scoped instance (m : ℕ) : IsProbabilityMeasure (gaussianPi m) := by
  unfold gaussianPi
  infer_instance

noncomputable def hermiteTensor {m : ℕ} (a : Fin m → ℕ) (x : Fin m → ℝ) : ℝ :=
  ∏ i, hermiteFunction (a i) (x i)

theorem continuous_hermiteFunction (n : ℕ) : Continuous (hermiteFunction n) :=
  (hermitePoly n).continuous.div_const _

theorem continuous_hermiteTensor {m : ℕ} (a : Fin m → ℕ) : Continuous (hermiteTensor a) := by
  unfold hermiteTensor
  exact continuous_finsetProd _ fun i _ => (continuous_hermiteFunction (a i)).comp (continuous_apply i)

theorem memLp_hermiteTensor {m : ℕ} (a : Fin m → ℕ) :
    MemLp (hermiteTensor a) 2 (gaussianPi m) := by
  apply (memLp_two_iff_integrable_sq (continuous_hermiteTensor a).aestronglyMeasurable).mpr
  have h := Integrable.fintype_prod (fun i => (memLp_hermiteFunction (a i)).integrable_sq)
  convert h using 1
  · ext x
    exact (Finset.prod_pow _ _ _).symm
  · rfl

theorem integral_hermiteTensor_mul {m : ℕ} (a b : Fin m → ℕ) :
    (∫ x, hermiteTensor a x * hermiteTensor b x ∂gaussianPi m) = if a = b then 1 else 0 := by
  classical
  simp only [hermiteTensor, ← Finset.prod_mul_distrib, gaussianPi]
  rw [integral_fintype_prod_eq_prod (fun i x => hermiteFunction (a i) x * hermiteFunction (b i) x)]
  simp only [integral_hermiteFunction_mul]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The tensor products of normalized Hermite polynomials are complete. -/
theorem ae_eq_zero_of_integral_hermiteTensor (m : ℕ) {f : (Fin m → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussianPi m))
    (horth : ∀ a : Fin m → ℕ, (∫ x, f x * hermiteTensor a x ∂gaussianPi m) = 0) :
    f =ᵐ[gaussianPi m] 0 := by
  induction m with
  | zero =>
    have he : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    have h := horth 0
    rw [he] at h ⊢
    simp [hermiteTensor] at h
    apply Eventually.of_forall
    intro x
    change f 0 = 0
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _
  | succ m ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
    have he : MeasurePreserving e (gaussianPi (m+1))
        ((gaussianReal 0 1).prod (gaussianPi m)) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) 0
    have hf' := hf.comp_measurePreserving he.symm
    have hzero : (f ∘ e.symm) =ᵐ[(gaussianReal 0 1).prod (gaussianPi m)] 0 := by
      apply ae_eq_zero_of_product_system
        memLp_hermiteFunction (fun a => memLp_hermiteTensor a)
        (fun _ hf h => ae_eq_zero_of_integral_hermiteFunction hf h)
        (fun _ hf h => ih hf h) hf'
      intro n a
      have h := horth (Fin.cons n a)
      rw [← he.symm.integral_comp e.symm.measurableEmbedding] at h
      convert h using 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hermiteTensor, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero]
    have hcomp := he.quasiMeasurePreserving.ae hzero
    filter_upwards [hcomp] with x hx
    simpa using hx

end Submission.Obl.Entropy__gaussian_chaos_resolvent
