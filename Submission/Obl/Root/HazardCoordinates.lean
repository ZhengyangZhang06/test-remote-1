import Submission.Lib.GaussianTransport.ScalarMatrixDerivative

open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace Submission.Obl.Root

open Submission.Lib.GaussianTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PositiveMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {A : selfAdjoint (Matrix ι ι ℝ) // (A : Matrix ι ι ℝ).PosDef}

lemma continuous_selfAdjoint_hazard :
    Continuous (selfAdjointCFC (ι := ι) gaussianHazard) := by
  apply Continuous.subtype_mk
  exact Continuous.cfc_of_mem_nhdsSet (s := univ) gaussianHazard (by simp)
    continuous_subtype_val (fun A => A.property) contDiff_gaussianHazard.continuous.continuousOn

lemma continuous_positiveMatrix_inverse_hazard :
    Continuous (fun A : PositiveMatrix ι => selfAdjointCFC inverseGaussianHazard A.val) := by
  apply Continuous.subtype_mk
  refine Continuous.cfc_of_mem_nhdsSet (s := Ioi 0) inverseGaussianHazard ?_
    (continuous_subtype_val.comp continuous_subtype_val) (fun A => A.val.property)
    continuousOn_inverseGaussianHazard
  · apply isOpen_Ioi.mem_nhdsSet.2
    exact iUnion_subset fun A => posDef_spectrum_subset_pos A.property

/-- The Gaussian hazard gives global coordinates on the positive definite cone.
In these coordinates the Gaussian normalization map is the identity. -/
noncomputable def gaussianHazardHomeomorph : selfAdjoint (Matrix ι ι ℝ) ≃ₜ PositiveMatrix ι where
  toFun A := ⟨selfAdjointCFC gaussianHazard A, posDef_cfc_gaussianHazard A.property⟩
  invFun A := selfAdjointCFC inverseGaussianHazard A.val
  left_inv A := by
    apply Subtype.ext
    exact cfc_inverseGaussianHazard_gaussianHazard A.property
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    exact cfc_gaussianHazard_inverseGaussianHazard A.property
  continuous_toFun := continuous_selfAdjoint_hazard.subtype_mk _
  continuous_invFun := continuous_positiveMatrix_inverse_hazard

@[simp] lemma gaussianHazardHomeomorph_apply_coe (A : selfAdjoint (Matrix ι ι ℝ)) :
    ((gaussianHazardHomeomorph A).val : Matrix ι ι ℝ) = cfc gaussianHazard (A : Matrix ι ι ℝ) := rfl

@[simp] lemma gaussianHazardHomeomorph_symm_apply (A : PositiveMatrix ι) :
    gaussianHazardHomeomorph.symm A = selfAdjointCFC inverseGaussianHazard A.val := rfl

/-- Compact zero bounds in the positive cone become ordinary bounded zero
bounds in the full vector space of symmetric matrices. -/
theorem exists_bound_hazard_coordinates
    {F : ℝ → PositiveMatrix ι → selfAdjoint (Matrix ι ι ℝ)} {K : Set (PositiveMatrix ι)}
    (hK : IsCompact K)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ P, F t P = 0 → P ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ A : selfAdjoint (Matrix ι ι ℝ),
      F t (gaussianHazardHomeomorph A) = 0 → ‖A‖ < R := by
  obtain ⟨R, hR, hbound⟩ :=
    (hK.image (gaussianHazardHomeomorph (ι := ι)).symm.continuous).isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun t ht A hA => hbound A ?_⟩
  exact ⟨gaussianHazardHomeomorph A, hzero t ht _ hA, gaussianHazardHomeomorph.symm_apply_apply A⟩

/-- The spectral Gaussian endpoint is exactly the identity in hazard coordinates. -/
theorem hazard_coordinates_initial
    {F : ℝ → PositiveMatrix ι → selfAdjoint (Matrix ι ι ℝ)}
    (hzero : ∀ P, F 0 P = selfAdjointCFC inverseGaussianHazard P.val) :
    ∀ A, F 0 (gaussianHazardHomeomorph A) = A := by
  intro A
  rw [hzero]
  exact (gaussianHazardHomeomorph (ι := ι)).symm_apply_apply A

/-- Reparametrization preserves joint continuity of the normalization homotopy. -/
theorem continuousOn_hazard_coordinates
    {F : ℝ → PositiveMatrix ι → selfAdjoint (Matrix ι ι ℝ)}
    (hF : ContinuousOn (fun p : ℝ × PositiveMatrix ι => F p.1 p.2) (Icc 0 1 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × selfAdjoint (Matrix ι ι ℝ) =>
      F p.1 (gaussianHazardHomeomorph p.2)) (Icc 0 1 ×ˢ univ) := by
  exact hF.comp
    (continuous_fst.prodMk (gaussianHazardHomeomorph.continuous.comp continuous_snd)).continuousOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)

/-- Compact subsets of the positive cone remain compact in its subtype topology. -/
theorem isCompact_positiveMatrix_lift {K : Set (selfAdjoint (Matrix ι ι ℝ))}
    (hK : IsCompact K) (hpos : ∀ P ∈ K, (P : Matrix ι ι ℝ).PosDef) :
    IsCompact {P : PositiveMatrix ι | P.val ∈ K} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.2
  have he : Subtype.val '' {P : PositiveMatrix ι | P.val ∈ K} = K := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact hQ
    · intro hP
      exact ⟨⟨P, hpos P hP⟩, hP, rfl⟩
  rwa [he]

/-- The ambient formulation used by the normalization bounds. -/
theorem exists_bound_hazard_coordinates_of_compact
    {F : ℝ → selfAdjoint (Matrix ι ι ℝ) → selfAdjoint (Matrix ι ι ℝ)}
    {K : Set (selfAdjoint (Matrix ι ι ℝ))} (hK : IsCompact K)
    (hpos : ∀ P ∈ K, (P : Matrix ι ι ℝ).PosDef)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ P : selfAdjoint (Matrix ι ι ℝ),
      (P : Matrix ι ι ℝ).PosDef → F t P = 0 → P ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ A : selfAdjoint (Matrix ι ι ℝ),
      F t (selfAdjointCFC gaussianHazard A) = 0 → ‖A‖ < R := by
  exact exists_bound_hazard_coordinates (F := fun t P => F t P.val)
    (isCompact_positiveMatrix_lift hK hpos) (fun t ht P hz => hzero t ht P.val P.property hz)

/-- Continuity only on positive matrices is enough for a continuous homotopy
on the full symmetric space after the hazard substitution. -/
theorem continuousOn_hazard_coordinates_of_positive
    {F : ℝ → selfAdjoint (Matrix ι ι ℝ) → selfAdjoint (Matrix ι ι ℝ)}
    (hF : ContinuousOn (fun p : ℝ × selfAdjoint (Matrix ι ι ℝ) => F p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ {P : selfAdjoint (Matrix ι ι ℝ) | (P : Matrix ι ι ℝ).PosDef})) :
    ContinuousOn (fun p : ℝ × selfAdjoint (Matrix ι ι ℝ) =>
      F p.1 (selfAdjointCFC gaussianHazard p.2)) (Icc 0 1 ×ˢ univ) := by
  exact hF.comp
    (continuous_fst.prodMk (continuous_selfAdjoint_hazard.comp continuous_snd)).continuousOn
    (fun p hp => ⟨hp.1, posDef_cfc_gaussianHazard p.2.property⟩)

end Submission.Obl.Root
