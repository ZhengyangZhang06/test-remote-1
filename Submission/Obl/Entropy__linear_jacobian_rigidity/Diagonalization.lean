import Submission.Obl.Entropy__linear_jacobian_rigidity.GaussianCompatibility

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open scoped BigOperators Matrix

variable {m : ℕ}

/-- The two Jacobian coefficient identities force pairwise commutation. -/
theorem coefficients_commute (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hlin : ∀ r s i, X r i s = X s i r)
    (hquad : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r) :
    ∀ r s, Commute (X r) (X s) := by
  have hm (r s t i : Fin m) : (X r * X t) i s = (X r * X s) i t := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ ↦ congrArg (X r i j * ·) (hlin t s j))
  intro r s
  ext i t
  have h := hquad r s t i
  simp only [Matrix.add_apply] at h
  rw [hm r s t i, hm s r t i, hm t s r i] at h
  linarith

/-- A commuting real Hermitian family admits a common orthonormal eigenbasis. -/
theorem common_eigenbasis (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian) (hcomm : ∀ r s, Commute (X r) (X s)) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ d : Fin m → Fin m → ℝ,
        ∀ r i, (X r).toEuclideanLin (b i) = d i r • b i := by
  classical
  let T : Fin m → Module.End ℝ (EuclideanSpace ℝ (Fin m)) :=
    fun r ↦ (X r).toEuclideanLin
  have hs : ∀ r, (T r).IsSymmetric :=
    fun r ↦ Matrix.isSymmetric_toEuclideanLin_iff.mpr (hX r)
  have hc : Pairwise (fun r s ↦ Commute (T r) (T s)) := by
    intro r s hrs
    show T r * T s = T s * T r
    ext x i
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦ (M *ᵥ x) i)
      (hcomm r s).eq
    simpa only [T, Module.End.mul_apply, Matrix.toEuclideanLin_apply,
      WithLp.ofLp_toLp, Matrix.mulVec_mulVec] using h
  have ho := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hs
  let V := fun d : Fin m → ℝ ↦ ⨅ r, Module.End.eigenspace (T r) (d r)
  let J := {d : Fin m → ℝ // V d ≠ ⊥}
  letI : Fintype J := ho.independent.fintypeNeBotOfFiniteDimensional
  have ho' := ho.comp (f := fun d : J ↦ d.val) Subtype.val_injective
  have hi : DirectSum.IsInternal (fun d : J ↦ V d.val) := by
    apply ho'.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff]
    change (⨆ d : {d // V d ≠ ⊥}, V d.val) = ⊤
    rw [iSup_ne_bot_subtype]
    exact LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hs hc
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  refine ⟨hi.subordinateOrthonormalBasis hn ho',
    fun i ↦ (hi.subordinateOrthonormalBasisIndex hn i ho').val, ?_⟩
  intro r i
  exact Module.End.mem_eigenspace_iff.mp
    ((Submodule.mem_iInf _).mp (hi.subordinateOrthonormalBasis_subordinate hn i ho') r)

end Submission.Obl.Entropy__linear_jacobian_rigidity
