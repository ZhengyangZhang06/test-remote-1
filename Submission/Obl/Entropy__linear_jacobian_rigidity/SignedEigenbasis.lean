import Submission.Obl.Entropy__linear_jacobian_rigidity.Diagonalization

namespace Submission.Obl.Entropy__linear_jacobian_rigidity

open scoped BigOperators Matrix

variable {m : ℕ}

/-- A unit common eigenvector has eigenvalue vector equal to itself up to sign. -/
theorem signed_eigenvector (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian)
    (hlin : ∀ r s i, X r i s = X s i r)
    (hnorm : ∑ r, X r * X r = 1)
    (v : EuclideanSpace ℝ (Fin m)) (hvnorm : ‖v‖ = 1)
    (d : Fin m → ℝ) (hd : ∀ r, (X r).toEuclideanLin v = d r • v) :
    ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ r, d r = s * v r := by
  have hvinner : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hvnorm]
    norm_num
  have hv : ∑ r, (v r) ^ 2 = 1 := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sq] using hvinner
  have hsym (r i j : Fin m) : X r i j = X r j i := by
    simpa only [star_trivial] using (hX r).apply j i
  have hcross (r k : Fin m) : d r * v k = d k * v r := by
    calc
      d r * v k = ((X r).toEuclideanLin v) k := by rw [hd]; rfl
      _ = ((X k).toEuclideanLin v) r := by
        change (∑ j, X r k j * v j) = ∑ j, X k r j * v j
        refine Finset.sum_congr rfl (fun j _ ↦ ?_)
        rw [hsym r k j, hlin r k j, hsym k j r]
      _ = d k * v r := by rw [hd]; rfl
  let s : ℝ := ∑ k, d k * v k
  have hds (r : Fin m) : d r = s * v r := by
    calc
      d r = d r * ∑ k, (v k) ^ 2 := by rw [hv, mul_one]
      _ = ∑ k, (d r * v k) * v k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ ↦ by ring)
      _ = ∑ k, (d k * v r) * v k :=
        Finset.sum_congr rfl (fun k _ ↦ by rw [hcross])
      _ = s * v r := by
        dsimp [s]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ ↦ by ring)
  have hsum : ∑ r, (d r) ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦
      (Matrix.toLpLin 2 2 M) v) hnorm
    change (Matrix.toEuclideanLin (∑ r, X r * X r)) v =
      (Matrix.toLpLin 2 2 (1 : Matrix (Fin m) (Fin m) ℝ)) v at h
    simp only [map_sum, LinearMap.sum_apply, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply, hd, map_smul, smul_smul,
      Matrix.toLpLin_one, LinearMap.id_apply] at h
    have h' := congrArg (inner ℝ v) h
    simpa only [inner_sum, inner_smul_right, hvinner, mul_one, sq] using h'
  refine ⟨s, ?_, hds⟩
  simp_rw [hds, mul_pow] at hsum
  rwa [← Finset.mul_sum, hv, mul_one] at hsum

/-- Orienting the common eigenbasis removes every sign from the linear field. -/
theorem unsigned_eigenbasis (X : Fin m → Matrix (Fin m) (Fin m) ℝ)
    (hX : ∀ r, (X r).IsHermitian)
    (hlin : ∀ r s i, X r i s = X s i r)
    (hquad : ∀ r s t i,
      (X r * X t + X t * X r) i s = (X s * X t + X t * X s) i r)
    (hnorm : ∑ r, X r * X r = 1) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∀ x i, (∑ r, x r • X r).toEuclideanLin (b i) = (b.repr x i) • b i := by
  classical
  obtain ⟨b, d, hd⟩ := common_eigenbasis X hX (coefficients_commute X hlin hquad)
  have hsg (i : Fin m) := signed_eigenvector X hX hlin hnorm
    (b i) (b.norm_eq_one i) (d i) (fun r ↦ hd r i)
  choose s hs hds using hsg
  let c : Fin m → EuclideanSpace ℝ (Fin m) := fun i ↦ s i • b i
  have hc : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [c]
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j]
    by_cases hij : i = j
    · subst j
      simpa [sq] using hs i
    · simp [hij]
  let B : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) :=
    OrthonormalBasis.mk hc
      (hc.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
  have hB (i : Fin m) : B i = s i • b i := by
    simp only [B, OrthonormalBasis.coe_mk, c]
  have heig (r i : Fin m) : (X r).toEuclideanLin (B i) = (B i r) • B i := by
    rw [hB, map_smul, hd, hds]
    simp only [PiLp.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    ring
  refine ⟨B, fun x i ↦ ?_⟩
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    heig, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [OrthonormalBasis.repr_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]

end Submission.Obl.Entropy__linear_jacobian_rigidity
