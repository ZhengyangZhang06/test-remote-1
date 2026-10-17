import Submission.Obl.Root.GaussianInverseSmooth
import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCContinuity

/-!
# Bounded smooth inverse-hazard parameters

A smooth positive Jacobian with a common positive spectral interval yields the
bounded smooth matrix parameter required in the normalized transport statement.
-/

open Matrix Set
open scoped Matrix.Norms.L2Operator ContDiff

namespace Submission.Obl.Root.GaussianMatrixSmooth

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ

lemma inverseGaussianHazard_abs_le {l u t : ℝ} (hl : 0 < l) (ht : t ∈ Icc l u) :
    |inverseGaussianHazard t| ≤ |inverseGaussianHazard l| + |inverseGaussianHazard u| := by
  have ht0 : 0 < t := lt_of_lt_of_le hl ht.1
  have hu0 : 0 < u := lt_of_lt_of_le ht0 ht.2
  have hlo := strictMonoOn_inverseGaussianHazard.monotoneOn hl ht0 ht.1
  have hhi := strictMonoOn_inverseGaussianHazard.monotoneOn ht0 hu0 ht.2
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (inverseGaussianHazard l), abs_nonneg (inverseGaussianHazard u)]
  · linarith [le_abs_self (inverseGaussianHazard u), abs_nonneg (inverseGaussianHazard l)]

lemma norm_inverseGaussianHazard_le {J : Mat} {l u : ℝ} (hl : 0 < l)
    (hs : spectrum ℝ J ⊆ Icc l u) :
    ‖cfc inverseGaussianHazard J‖ ≤ |inverseGaussianHazard l| + |inverseGaussianHazard u| := by
  apply norm_cfc_le (by positivity)
  intro t ht
  simpa only [Real.norm_eq_abs] using inverseGaussianHazard_abs_le hl (hs ht)

/-- A common positive spectral interval gives a common entry bound on the parameters. -/
lemma bounded_inverseGaussianHazard_entries {X : Type*} (J : X → Mat) {l u : ℝ}
    (hl : 0 < l) (hs : ∀ x, spectrum ℝ (J x) ⊆ Icc l u) :
    ∃ R : ℝ, 0 < R ∧ ∀ x i j, |cfc inverseGaussianHazard (J x) i j| ≤ R := by
  let L : Mat →L[ℝ] (ι → ι → ℝ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let C : ℝ := |inverseGaussianHazard l| + |inverseGaussianHazard u|
  refine ⟨‖L‖ * C + 1, by dsimp [C]; positivity, ?_⟩
  intro x i j
  have hc := norm_inverseGaussianHazard_le hl (hs x)
  have hn : ‖L (cfc inverseGaussianHazard (J x))‖ ≤ ‖L‖ * C :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hc (norm_nonneg L))
  have he : |cfc inverseGaussianHazard (J x) i j| ≤
      ‖L (cfc inverseGaussianHazard (J x))‖ := by
    simpa [L, Real.norm_eq_abs] using
      (norm_le_pi_norm (L (cfc inverseGaussianHazard (J x)) i) j).trans
        (norm_le_pi_norm (L (cfc inverseGaussianHazard (J x))) i)
  exact he.trans (hn.trans (by linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All parameter regularity clauses follow from a smooth uniformly elliptic Jacobian. -/
lemma smooth_bounded_inverseGaussianHazard {J : E → Mat} (hJ : ContDiff ℝ ∞ J)
    (hpos : ∀ x, (J x).PosDef) {l u : ℝ} (hl : 0 < l)
    (hs : ∀ x, spectrum ℝ (J x) ⊆ Icc l u) :
    (∀ i j, ContDiff ℝ ∞ (fun x => cfc inverseGaussianHazard (J x) i j)) ∧
    (∀ x, (cfc inverseGaussianHazard (J x)).IsHermitian) ∧
    (∃ R : ℝ, 0 < R ∧ ∀ x i j, |cfc inverseGaussianHazard (J x) i j| ≤ R) ∧
    (∀ x, cfc gaussianHazard (cfc inverseGaussianHazard (J x)) = J x) := by
  refine ⟨?_, fun _ => cfc_predicate _ _, bounded_inverseGaussianHazard_entries J hl hs,
    fun x => cfc_gaussianHazard_inverseGaussianHazard (hpos x)⟩
  intro i j
  let ev : Mat →L[ℝ] ℝ :=
    { toLinearMap :=
        { toFun := fun M => M i j
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply j).comp (continuous_apply i) }
  exact ev.contDiff.comp (contDiff_cfc_inverseGaussianHazard hJ hpos)

lemma smooth_bounded_inverseGaussianHazard_of_entries {J : E → Mat}
    (hJ : ∀ i j, ContDiff ℝ ∞ (fun x => J x i j)) (hpos : ∀ x, (J x).PosDef)
    {l u : ℝ} (hl : 0 < l) (hs : ∀ x, spectrum ℝ (J x) ⊆ Icc l u) :
    (∀ i j, ContDiff ℝ ∞ (fun x => cfc inverseGaussianHazard (J x) i j)) ∧
    (∀ x, (cfc inverseGaussianHazard (J x)).IsHermitian) ∧
    (∃ R : ℝ, 0 < R ∧ ∀ x i j, |cfc inverseGaussianHazard (J x) i j| ≤ R) ∧
    (∀ x, cfc gaussianHazard (cfc inverseGaussianHazard (J x)) = J x) :=
  smooth_bounded_inverseGaussianHazard (contDiff_matrix_of_entries hJ) hpos hl hs

end Submission.Obl.Root.GaussianMatrixSmooth
