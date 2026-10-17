import Submission.Obl.Root.GaussianInverseSmooth

/-!
# Global Gaussian hazard coordinates on positive definite matrices

These coordinates turn the Gaussian endpoint of the normalization homotopy into
the identity map. The coordinate choice was suggested by session x0014 at 08:10
on 2026-10-17; the smooth matrix calculus is the original x0119 construction.
-/

open Matrix Set Filter
open scoped Matrix.Norms.L2Operator ContDiff Topology

namespace Submission.Obl.Root.GaussianMatrixSmooth

open Submission.Lib.GaussianTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local notation "Sym" => selfAdjoint Mat

/-- The positive definite cone as a subtype of symmetric matrices. -/
def positiveCone : Set Sym := {J | (J : Mat).PosDef}

lemma inverse_hazard_leftInverse :
    Function.LeftInverse (selfAdjointCFC (ι := ι) inverseGaussianHazard)
      (selfAdjointCFC gaussianHazard) := by
  intro A
  apply Subtype.ext
  exact cfc_inverseGaussianHazard_gaussianHazard A.property

lemma continuousOn_inverse_hazard :
    ContinuousOn (selfAdjointCFC (ι := ι) inverseGaussianHazard) positiveCone := by
  intro J hJ
  exact (contDiffAt_selfAdjoint_inverseGaussianHazard J hJ).continuousAt.continuousWithinAt

/-- Gaussian hazard provides global coordinates on the positive definite cone. -/
noncomputable def hazardChart : Sym ≃ₜ positiveCone (ι := ι) where
  toFun A := ⟨selfAdjointCFC gaussianHazard A, posDef_cfc_gaussianHazard A.property⟩
  invFun J := selfAdjointCFC inverseGaussianHazard J.val
  left_inv := inverse_hazard_leftInverse
  right_inv J := by
    apply Subtype.ext
    apply Subtype.ext
    exact cfc_gaussianHazard_inverseGaussianHazard J.property
  continuous_toFun := (contDiff_selfAdjoint_gaussianHazard (ι := ι)).continuous.subtype_mk _
  continuous_invFun := (continuousOn_inverse_hazard (ι := ι)).domRestrict

@[simp] lemma hazardChart_apply (A : Sym) :
    (hazardChart A).val = selfAdjointCFC gaussianHazard A := rfl

@[simp] lemma hazardChart_symm_apply (J : positiveCone (ι := ι)) :
    hazardChart.symm J = selfAdjointCFC inverseGaussianHazard J.val := rfl

/-- A compact positive matrix set has compact preimage in hazard coordinates. -/
lemma isCompact_hazard_preimage {K : Set Sym} (hK : IsCompact K)
    (hpos : K ⊆ positiveCone) :
    IsCompact ((selfAdjointCFC gaussianHazard) ⁻¹' K) := by
  have he : (selfAdjointCFC gaussianHazard) ⁻¹' K =
      (selfAdjointCFC inverseGaussianHazard) '' K := by
    ext A
    constructor
    · intro hA
      exact ⟨selfAdjointCFC gaussianHazard A, hA, inverse_hazard_leftInverse A⟩
    · rintro ⟨J, hJ, rfl⟩
      have hh : selfAdjointCFC gaussianHazard (selfAdjointCFC inverseGaussianHazard J) = J := by
        apply Subtype.ext
        exact cfc_gaussianHazard_inverseGaussianHazard (hpos hJ)
      simpa only [mem_preimage, hh] using hJ
  rw [he]
  exact hK.image_of_continuousOn (continuousOn_inverse_hazard.mono hpos)

/-- Compose the normalization homotopy with global hazard coordinates. -/
noncomputable def chartHomotopy (F : ℝ → Sym → Sym) (t : ℝ) (A : Sym) : Sym :=
  F t (selfAdjointCFC gaussianHazard A)

lemma chartHomotopy_initial {F : ℝ → Sym → Sym}
    (hF : ∀ J ∈ positiveCone, F 0 J = selfAdjointCFC inverseGaussianHazard J) (A : Sym) :
    chartHomotopy F 0 A = A := by
  rw [chartHomotopy, hF _ (posDef_cfc_gaussianHazard A.property)]
  exact inverse_hazard_leftInverse A

lemma continuous_chartHomotopy {F : ℝ → Sym → Sym}
    (hF : Continuous (Function.uncurry F)) :
    Continuous (Function.uncurry (chartHomotopy F)) := by
  exact hF.comp (continuous_fst.prodMk
    ((contDiff_selfAdjoint_gaussianHazard (ι := ι)).continuous.comp continuous_snd))

lemma continuousOn_chartHomotopy {F : ℝ → Sym → Sym}
    (hF : ContinuousOn (Function.uncurry F) (Icc (0 : ℝ) 1 ×ˢ positiveCone)) :
    ContinuousOn (Function.uncurry (chartHomotopy F)) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  apply hF.comp (continuous_fst.prodMk
    ((contDiff_selfAdjoint_gaussianHazard (ι := ι)).continuous.comp continuous_snd)).continuousOn
  intro p hp
  exact ⟨hp.1, posDef_cfc_gaussianHazard p.2.property⟩

/-- A uniform compact set containing positive normalization zeros gives a finite
radius containing every zero in the global symmetric coordinates. -/
lemma chartHomotopy_zero_bound {F : ℝ → Sym → Sym} {K : Set Sym}
    (hK : IsCompact K) (hpos : K ⊆ positiveCone)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ J ∈ positiveCone, F t J = 0 → J ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ A : Sym,
      chartHomotopy F t A = 0 → ‖A‖ < R := by
  obtain ⟨R, hR⟩ := (isCompact_hazard_preimage hK hpos).isBounded.exists_pos_norm_lt
  refine ⟨R, hR.1, ?_⟩
  intro t ht A hA
  exact hR.2 A (hzero t ht _ (posDef_cfc_gaussianHazard A.property) hA)

end Submission.Obl.Root.GaussianMatrixSmooth
