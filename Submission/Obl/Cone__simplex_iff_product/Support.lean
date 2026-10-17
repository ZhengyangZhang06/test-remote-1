import Submission.Obl.Cone__simplex_iff_product.Geometry

open Set MeasureTheory
open scoped BigOperators Topology

namespace Submission.Obl.Cone__simplex_iff_product

def affineOrthant {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (a : E m) : Set (E m) :=
  {x | ∀ i, 0 ≤ L.symm (x - a) i}

theorem isClosed_affineOrthant {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (a : E m) :
    IsClosed (affineOrthant L a) := by
  simp only [affineOrthant, ofPred_forall]
  have hc := L.symm.toContinuousLinearEquiv.continuous
  exact isClosed_iInter fun i => isClosed_le continuous_const
    ((PiLp.continuous_apply 2 _ i).comp (hc.comp (continuous_id.sub continuous_const)))

theorem convex_affineOrthant {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (a : E m) :
    Convex ℝ (affineOrthant L a) := by
  intro x hx y hy c d hc hd hcd i
  have he : c • x + d • y - a = c • (x - a) + d • (y - a) := by
    rw [smul_sub, smul_sub]
    calc
      _ = c • x + d • y - (c • a + d • a) := by rw [← add_smul, hcd, one_smul]
      _ = _ := by abel
  simp only [he, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hc (hx i)) (mul_nonneg hd (hy i))

theorem affineOrthant_interior_nonempty {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (a : E m) :
    (interior (affineOrthant L a)).Nonempty := by
  let p : E m := WithLp.toLp 2 (fun _ => 1)
  let U : Set (E m) := {x | ∀ i, 0 < L.symm (x - a) i}
  have hc := L.symm.toContinuousLinearEquiv.continuous
  have ho : IsOpen U := by
    simp only [U, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 _ i).comp (hc.comp (continuous_id.sub continuous_const)))
  have hsub : U ⊆ affineOrthant L a := fun x hx i => (hx i).le
  refine ⟨L p + a, interior_mono hsub ?_⟩
  rw [ho.interior_eq]
  intro i
  simp [p]

theorem affineOrthant_regular {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (a : E m) :
    closure (interior (affineOrthant L a)) = affineOrthant L a := by
  rw [(convex_affineOrthant L a).closure_interior_eq_closure_of_nonempty_interior
    (affineOrthant_interior_nonempty L a), (isClosed_affineOrthant L a).closure_eq]

theorem support_eq {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K)
    (L : E (n + 1) ≃ₗ[ℝ] E (n + 1)) (a : E (n + 1))
    (he : ∀ᵐ z ∂volume, (cone K).indicator
      (fun z => Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) z =
      |LinearMap.det L.toLinearMap|⁻¹ *
      (if ∀ i, 0 ≤ L.symm (z - a) i then Real.exp (-∑ i, L.symm (z - a) i) else 0)) :
    cone K = affineOrthant L a := by
  apply regular_set_eq_of_ae (isClosed_cone hK.isCompact) (isClosed_affineOrthant L a)
    (cone_regular hK) (affineOrthant_regular L a)
  have hvol := Submission.Lib.ConvexBody.body_vol_pos hK
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hdet : 0 < |LinearMap.det L.toLinearMap|⁻¹ :=
    inv_pos.mpr (abs_pos.mpr L.isUnit_det'.ne_zero)
  filter_upwards [he] with z hz
  change z ∈ cone K ↔ ∀ i, 0 ≤ L.symm (z - a) i
  by_cases hc : z ∈ cone K <;> by_cases ho : ∀ i, 0 ≤ L.symm (z - a) i
  · exact iff_of_true hc ho
  · have hp : 0 < Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K) :=
      div_pos (Real.exp_pos _) (mul_pos hfac hvol)
    simp only [indicator_of_mem hc, if_neg ho, mul_zero] at hz
    exact False.elim (hp.ne' hz)
  · have hp : 0 < |LinearMap.det L.toLinearMap|⁻¹ * Real.exp (-∑ i, L.symm (z - a) i) :=
      mul_pos hdet (Real.exp_pos _)
    simp only [indicator_of_notMem hc, if_pos ho] at hz
    exact False.elim (hp.ne' hz.symm)
  · exact iff_of_false hc ho

theorem translation_eq_zero {n : ℕ} {K : Set (E n)} (hK : K.Nonempty)
    (L : E (n + 1) ≃ₗ[ℝ] E (n + 1)) (a : E (n + 1))
    (he : cone K = affineOrthant L a) : a = 0 := by
  have ha : a ∈ cone K := by rw [he]; simp [affineOrthant]
  have h2 := cone_smul ha (r := 2) (by norm_num)
  have h0 := zero_mem_cone hK
  rw [he] at h0 h2
  have hp : ∀ i, 0 ≤ L.symm a i := by
    have hid : (2 : ℝ) • a - a = a := by module
    simpa only [affineOrthant, mem_ofPred_eq, hid] using h2
  have hn : ∀ i, L.symm a i ≤ 0 := by
    simpa only [affineOrthant, mem_ofPred_eq, zero_sub, map_neg, PiLp.neg_apply,
      neg_nonneg] using h0
  apply L.symm.injective
  ext i
  simpa only [map_zero, PiLp.zero_apply] using le_antisymm (hn i) (hp i)

end Submission.Obl.Cone__simplex_iff_product
