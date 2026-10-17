import Submission.Obl.Cone__simplex_iff_product.Algebra
import Submission.Obl.Cone__simplex_iff_product.Support

open Set MeasureTheory Module
open scoped BigOperators Topology

namespace Submission.Obl.Cone__simplex_iff_product

theorem simplex_linearEquiv {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsSimplex K) :
    ∃ L : E (n + 1) ≃ₗ[ℝ] E (n + 1),
      (∀ z, z ∈ cone K ↔ ∀ i, 0 ≤ L.symm z i) ∧
      (∀ z, ∑ i, L.symm z i = z 0) := by
  classical
  obtain ⟨v, hv, rfl⟩ := hK
  let b : Basis (Fin (n + 1)) ℝ (E (n + 1)) :=
    basisOfLinearIndependentOfCardEqFinrank ((affineIndependent_iff_lift v).mp hv)
      (by simp [E])
  let L : E (n + 1) ≃ₗ[ℝ] E (n + 1) :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.equiv b (Equiv.refl _)
  have hcol (i : Fin (n + 1)) :
      L ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i) = lift (v i) := by
    change ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.equiv b
      (Equiv.refl _)) ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis i) = _
    rw [Basis.equiv_apply]
    simp [b]
  have hL (u : E (n + 1)) : ∑ i, u i • lift (v i) = L u := by
    simpa only [hcol] using linearEquiv_sum L u
  refine ⟨L, ?_, ?_⟩
  · intro z
    rw [cone_convexHull_lift v z]
    constructor
    · rintro ⟨w, hw, hz⟩
      let u : E (n + 1) := WithLp.toLp 2 w
      have hu : L u = z := (hL u).symm.trans hz
      rw [← hu, L.symm_apply_apply]
      exact hw
    · intro hz
      exact ⟨fun i => L.symm z i, hz, (hL (L.symm z)).trans (L.apply_symm_apply z)⟩
  · intro z
    have hh := congrArg (fun x : E (n + 1) => x 0) (hL (L.symm z))
    simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_zero, mul_one,
      L.apply_symm_apply] using hh

theorem simplex_of_cone_orthant {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K)
    (L : E (n + 1) ≃ₗ[ℝ] E (n + 1))
    (he : cone K = affineOrthant L 0) : SimplexIsotropic.IsSimplex K := by
  classical
  let b : Basis (Fin (n + 1)) ℝ (E (n + 1)) :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.map L
  have hb (i : Fin (n + 1)) : b i ∈ cone K := by
    rw [he]
    change ∀ j, 0 ≤ L.symm (L ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i) - 0) j
    simp only [sub_zero, L.symm_apply_apply, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
    intro j
    split_ifs <;> norm_num
  have ht (i : Fin (n + 1)) : 0 < b i 0 := by
    apply lt_of_le_of_ne (hb i).1
    intro h
    exact b.ne_zero i (cone_height_zero (hb i) h.symm)
  let v : Fin (n + 1) → E n := fun i => WithLp.toLp 2 (fun j => b i j.succ / b i 0)
  have hv (i : Fin (n + 1)) : lift (v i) = (b i 0)⁻¹ • b i := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change 1 = (b i 0)⁻¹ * b i 0
      rw [inv_mul_cancel₀ (ht i).ne']
    · change b i k.succ / b i 0 = (b i 0)⁻¹ * b i k.succ
      rw [div_eq_mul_inv, mul_comm]
  have hvK (i : Fin (n + 1)) : v i ∈ K := by
    apply lift_mem_cone.mp
    rw [hv]
    exact cone_smul (hb i) (inv_nonneg.mpr (ht i).le)
  refine ⟨v, ?_, ?_⟩
  · apply (affineIndependent_iff_lift v).mpr
    rw [Fintype.linearIndependent_iff]
    intro w hw
    simp_rw [hv, smul_smul] at hw
    have hz := Fintype.linearIndependent_iff.mp b.linearIndependent _ hw
    intro i
    exact (mul_eq_zero.mp (hz i)).resolve_right (inv_ne_zero (ht i).ne')
  · apply subset_antisymm
    · intro x hx
      let u := L.symm (lift x)
      have hu : ∀ i, 0 ≤ u i := by
        have hh := lift_mem_cone.mpr hx
        rw [he] at hh
        simpa only [affineOrthant, mem_ofPred_eq, sub_zero] using hh
      have hs : ∑ i, u i • b i = lift x := by
        simpa only [b, Basis.map_apply, OrthonormalBasis.coe_toBasis,
          L.apply_symm_apply] using linearEquiv_sum L (L.symm (lift x))
      have hsum : ∑ i, u i * b i 0 = 1 := by
        have hh := congrArg (fun z : E (n + 1) => z 0) hs
        simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_zero] using hh
      apply mem_convexHull_of_exists_fintype (fun i => u i * b i 0) v
        (fun i => mul_nonneg (hu i) (ht i).le) hsum (fun i => mem_range_self i)
      ext j
      have hh := congrArg (fun z : E (n + 1) => z j.succ) hs
      simp only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_succ] at hh ⊢
      rw [← hh]
      apply Finset.sum_congr rfl
      intro i _
      change (u i * b i 0) * (b i j.succ / b i 0) = u i * b i j.succ
      field_simp [(ht i).ne']
    · exact convexHull_min (range_subset_iff.mpr hvK) hK

theorem simplex_of_affine_cone {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K)
    (L : E (n + 1) ≃ₗ[ℝ] E (n + 1)) (a : E (n + 1))
    (he : cone K = affineOrthant L a) : SimplexIsotropic.IsSimplex K := by
  have ha := translation_eq_zero (hK.interior_nonempty.mono interior_subset) L a he
  subst a
  exact simplex_of_cone_orthant hK.convex L he

end Submission.Obl.Cone__simplex_iff_product
