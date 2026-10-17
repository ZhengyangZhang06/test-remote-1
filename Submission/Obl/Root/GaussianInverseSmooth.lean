import Submission.Obl.Root.GaussianMatrixSmooth
import Submission.Lib.GaussianTransport.ScalarMatrixDerivative
import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCEntry

/-!
# Smooth inverse Gaussian hazard on positive matrices

The matrix hazard is smooth by its matrix exponential formula. Its derivative
on symmetric matrices is invertible because all divided differences are positive.
The inverse function theorem then gives smoothness of the spectral inverse.
-/

open Matrix Set Filter
open scoped Matrix.Norms.L2Operator ContDiff Topology

namespace Submission.Obl.Root.GaussianMatrixSmooth

open Submission.Lib.GaussianTransport
open Submission.Obl.Entropy__c1_bounded_matrix_calculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local notation "Sym" => selfAdjoint Mat

local instance : FiniteDimensional ℝ Sym := finiteDimensional_selfAdjointMatrix

/-- The symmetric matrix space has its inherited norm. -/
noncomputable def symInclusion : Sym →L[ℝ] Mat :=
  (selfAdjoint.submodule ℝ Mat).subtypeL

@[simp] lemma symInclusion_apply (A : Sym) : symInclusion A = (A : Mat) := rfl

/-- The Gaussian hazard is smooth at every symmetric matrix. -/
lemma contDiff_selfAdjoint_gaussianHazard :
    ContDiff ℝ ∞ (selfAdjointCFC (ι := ι) gaussianHazard) := by
  let p : Mat →L[ℝ] Sym := (selfAdjointPart ℝ).toContinuousLinearMap
  have he : selfAdjointCFC (ι := ι) gaussianHazard =
      fun A => p (hazardMatrix (symInclusion A)) := by
    funext A
    apply Subtype.ext
    rw [symInclusion_apply, hazardMatrix_eq_cfc A.property]
    exact ((cfc_predicate gaussianHazard (A : Mat)).coe_selfAdjointPart_apply ℝ).symm
  rw [he, contDiff_iff_contDiffAt]
  intro A
  exact p.contDiff.contDiffAt.comp A
    ((contDiffAt_hazardMatrix A.property).comp A (symInclusion (ι := ι)).contDiff.contDiffAt)

lemma dslope_gaussianHazard_pos (a b : ℝ) : 0 < dslope gaussianHazard a b := by
  by_cases h : b = a
  · rw [h, dslope_same]
    exact deriv_gaussianHazard_pos a
  · rw [dslope_of_ne _ h]
    exact (strictMono_gaussianHazard.strictMonoOn univ).slope_pos
      (mem_univ _) (mem_univ _) (Ne.symm h)

/-- The derivative is the positive divided-difference operator in an eigenbasis. -/
lemma fderiv_selfAdjoint_gaussianHazard_coe (A B : Sym) :
    (fderiv ℝ (selfAdjointCFC gaussianHazard) A B : Mat) =
      spectralDerivative A.property gaussianHazard (B : Mat) := by
  have hd := (symInclusion (ι := ι)).hasFDerivAt.comp A
    ((contDiff_selfAdjoint_gaussianHazard.differentiable (by norm_num) A).hasFDerivAt)
  have he := hasFDerivAt_cfc (symInclusion (ι := ι)).continuous
    (fun A : Sym => A.property)
    (contDiff_gaussianHazard.differentiable (by norm_num))
    ((symInclusion (ι := ι)).hasFDerivAt (x := A))
  have hh := hd.unique he
  simpa [spectralDerivative, ContinuousLinearMap.comp_apply] using
    congrArg (fun D : Sym →L[ℝ] Mat => D B) hh

lemma injective_fderiv_selfAdjoint_gaussianHazard (A : Sym) :
    Function.Injective (fderiv ℝ (selfAdjointCFC gaussianHazard) A) := by
  intro B C h
  have he : spectralDerivative A.property gaussianHazard (B : Mat) =
      spectralDerivative A.property gaussianHazard (C : Mat) := by
    simpa only [fderiv_selfAdjoint_gaussianHazard_coe] using congrArg Subtype.val h
  have hA : (A : Mat).IsHermitian := A.property
  let e := (Unitary.conjStarAlgAut ℝ Mat hA.eigenvectorUnitary).symm
  apply Subtype.ext
  apply e.injective
  ext i j
  have hh := congrArg (fun M : Mat => e M i j) he
  simp only [e, spectralDerivative_eigenbasis] at hh
  exact mul_left_cancel₀ (dslope_gaussianHazard_pos _ _).ne' hh

/-- The derivative is an isomorphism of the finite-dimensional symmetric space. -/
noncomputable def hazardDerivEquiv (A : Sym) : Sym ≃L[ℝ] Sym :=
  (LinearEquiv.ofBijective (fderiv ℝ (selfAdjointCFC gaussianHazard) A).toLinearMap
    ⟨injective_fderiv_selfAdjoint_gaussianHazard A,
      LinearMap.injective_iff_surjective.mp
        (injective_fderiv_selfAdjoint_gaussianHazard A)⟩).toContinuousLinearEquiv

@[simp] lemma hazardDerivEquiv_toContinuousLinearMap (A : Sym) :
    (hazardDerivEquiv A : Sym →L[ℝ] Sym) =
      fderiv ℝ (selfAdjointCFC gaussianHazard) A := rfl

/-- Smoothness of the inverse at every value of the hazard. -/
lemma contDiffAt_inverse_at_hazard (A : Sym) :
    ContDiffAt ℝ ∞ (selfAdjointCFC inverseGaussianHazard)
      (selfAdjointCFC gaussianHazard A) := by
  let f : Sym → Sym := selfAdjointCFC gaussianHazard
  let g : Sym → Sym := selfAdjointCFC inverseGaussianHazard
  have hgf : Function.LeftInverse g f := by
    intro B
    apply Subtype.ext
    exact cfc_inverseGaussianHazard_gaussianHazard B.property
  have hf : ContDiffAt ℝ ∞ f A := contDiff_selfAdjoint_gaussianHazard.contDiffAt
  have hd : HasFDerivAt f (hazardDerivEquiv A : Sym →L[ℝ] Sym) A := by
    rw [hazardDerivEquiv_toContinuousLinearMap]
    exact (contDiff_selfAdjoint_gaussianHazard.differentiable (by norm_num) A).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hf.hasStrictFDerivAt' hd hn
  have he : g =ᶠ[𝓝 (f A)] hf.localInverse hd hn := by
    filter_upwards [hs.eventually_right_inverse] with B hB
    change f (hf.localInverse hd hn B) = B at hB
    exact (congrArg g hB).symm.trans (hgf _)
  exact (hf.to_localInverse hd hn).congr_of_eventuallyEq he

/-- The spectral inverse Gaussian hazard is smooth throughout the positive cone. -/
lemma contDiffAt_selfAdjoint_inverseGaussianHazard (J : Sym) (hJ : (J : Mat).PosDef) :
    ContDiffAt ℝ ∞ (selfAdjointCFC inverseGaussianHazard) J := by
  have he : selfAdjointCFC gaussianHazard (selfAdjointCFC inverseGaussianHazard J) = J := by
    apply Subtype.ext
    exact cfc_gaussianHazard_inverseGaussianHazard hJ
  simpa only [he] using contDiffAt_inverse_at_hazard (selfAdjointCFC inverseGaussianHazard J)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth positive definite matrix fields admit smooth inverse-hazard parameters. -/
lemma contDiff_cfc_inverseGaussianHazard {J : E → Mat} (hJ : ContDiff ℝ ∞ J)
    (hpos : ∀ x, (J x).PosDef) :
    ContDiff ℝ ∞ (fun x => cfc inverseGaussianHazard (J x)) := by
  let p : Mat →L[ℝ] Sym := (selfAdjointPart ℝ).toContinuousLinearMap
  have he (x : E) : (p (J x) : Mat) = J x :=
    (hpos x).isHermitian.isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  have hs : ContDiff ℝ ∞ (fun x => selfAdjointCFC inverseGaussianHazard (p (J x))) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    apply (contDiffAt_selfAdjoint_inverseGaussianHazard (p (J x)) ?_).comp x
      (p.contDiff.comp hJ).contDiffAt
    simpa only [he] using hpos x
  convert! (symInclusion (ι := ι)).contDiff.comp hs using 1
  funext x
  exact congrArg (cfc inverseGaussianHazard) (he x).symm

end Submission.Obl.Root.GaussianMatrixSmooth
