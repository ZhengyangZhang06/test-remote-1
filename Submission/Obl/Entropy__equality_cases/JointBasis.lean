import Mathlib

namespace Submission.Obl.Entropy__equality_cases

/-- Commuting symmetric endomorphisms have a common orthonormal eigenbasis. -/
theorem joint_orthonormalBasis {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ι → E →ₗ[ℝ] E) (hT : ∀ r, (T r).IsSymmetric)
    (hcomm : ∀ r s, Commute (T r) (T s))
    {m : ℕ} (hm : Module.finrank ℝ E = m) :
    ∃ b : OrthonormalBasis (Fin m) ℝ E, ∃ eig : ι → Fin m → ℝ,
      ∀ r j, T r (b j) = eig r j • b j := by
  classical
  let χ : (∀ r, Module.End.Eigenvalues (T r)) → (ι → ℝ) := fun u r => u r
  have hχ : Function.Injective χ := by
    intro u v h
    funext r
    exact Subtype.ext (congrFun h r)
  have hO := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT).comp hχ
  have hsup : (⨆ u : ∀ r, Module.End.Eigenvalues (T r),
      ⨅ r, Module.End.eigenspace (T r) (χ u r)) = ⊤ := by
    apply top_unique
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT
      (fun r s _ => hcomm r s)]
    apply iSup_le
    intro u
    by_cases hu : ∀ r, Module.End.HasEigenvalue (T r) (u r)
    · exact le_iSup_of_le (fun r => ⟨u r, hu r⟩) le_rfl
    · obtain ⟨r, hr⟩ := not_forall.mp hu
      have hr' : Module.End.eigenspace (T r) (u r) = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using hr
      exact (iInf_le _ r).trans (hr'.le.trans bot_le)
  have hI := hO.isInternal_iff.mpr (by rw [hsup, Submodule.top_orthogonal_eq_bot])
  refine ⟨hI.subordinateOrthonormalBasis hm hO,
    fun r j => χ (hI.subordinateOrthonormalBasisIndex hm j hO) r, ?_⟩
  intro r j
  exact Module.End.mem_eigenspace_iff.mp
    ((Submodule.mem_iInf _).mp (hI.subordinateOrthonormalBasis_subordinate hm j hO) r)

/-- Matrix formulation of the common eigenbasis. -/
theorem matrix_joint_orthonormalBasis {m : ℕ} (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hcomm : ∀ r s, Commute (X r) (X s)) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ eig : Fin m → Fin m → ℝ,
        ∀ r j, (X r).toEuclideanLin (b j) = eig r j • b j := by
  apply joint_orthonormalBasis (fun r => (X r).toEuclideanLin)
  · intro r
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (hX r)
  · intro r s
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec, (hcomm r s).eq]
  · simp

end Submission.Obl.Entropy__equality_cases
