import Submission.Obl.Cone__simplex_iff_product.Geometry

open Set MeasureTheory Module
open scoped BigOperators Topology

namespace Submission.Obl.Cone__simplex_iff_product

@[simp] theorem esum_apply {m : ℕ} {ι : Type*} (s : Finset ι) (v : ι → E m) (j : Fin m) :
    (∑ i ∈ s, v i) j = ∑ i ∈ s, v i j := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

theorem affineIndependent_iff_lift {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → E n) :
    AffineIndependent ℝ v ↔ LinearIndependent ℝ (fun i => lift (v i)) := by
  rw [affineIndependent_iff_of_fintype, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw
    have hsum : ∑ i, w i = 0 := by
      have hh := congrArg (fun z : E (n + 1) => z 0) hw
      simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_zero, mul_one,
        PiLp.zero_apply] using hh
    apply h w hsum
    rw [Finset.weightedVSub_eq_linear_combination _ hsum]
    ext j
    have hh := congrArg (fun z : E (n + 1) => z j.succ) hw
    simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_succ, PiLp.zero_apply] using hh
  · intro h w hsum hv
    apply h w
    rw [Finset.weightedVSub_eq_linear_combination _ hsum] at hv
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_zero, mul_one,
        PiLp.zero_apply] using hsum
    · have hh := congrArg (fun z : E n => z k) hv
      simpa only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_succ, PiLp.zero_apply] using hh

theorem stdBasis_sum {m : ℕ} (x : E m) :
    ∑ i, x i • (EuclideanSpace.basisFun (Fin m) ℝ) i = x := by
  simpa using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x

theorem linearEquiv_sum {m : ℕ} (L : E m ≃ₗ[ℝ] E m) (x : E m) :
    ∑ i, x i • L ((EuclideanSpace.basisFun (Fin m) ℝ) i) = L x := by
  simpa only [map_sum, map_smul] using congrArg L (stdBasis_sum x)

theorem cone_sum {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K) (hne : K.Nonempty)
    {ι : Type*} (s : Finset ι) (z : ι → E (n + 1)) (hz : ∀ i ∈ s, z i ∈ cone K) :
    ∑ i ∈ s, z i ∈ cone K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_cone hne
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact cone_add hK (hz i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hz j (Finset.mem_insert_of_mem hj)))

theorem cone_convexHull_lift {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → E n) (z : E (n + 1)) :
    z ∈ cone (convexHull ℝ (range v)) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i • lift (v i) = z := by
  classical
  constructor
  · rintro ⟨ht, x, hx, he⟩
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw, hsum, hx⟩ := hx
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hx
    refine ⟨fun i => if i ∈ s then z 0 * w i else 0, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact mul_nonneg ht (hw i hi)
      · exact le_rfl
    · ext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [esum_apply, PiLp.smul_apply, lift_zero, smul_eq_mul, mul_one]
        simpa [← Finset.mul_sum, hsum] using
          (Finset.sum_subset (Finset.subset_univ s)
            (f := fun i => if i ∈ s then z 0 * w i else 0) (by simp)).symm
      · simp only [esum_apply, PiLp.smul_apply, smul_eq_mul, lift_succ]
        rw [he k, ← hx, esum_apply]
        simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_subset (Finset.subset_univ s)
          (f := fun i => (if i ∈ s then z 0 * w i else 0) * v i k)
            (by intro i _ hi; simp [hi])]
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
        ring
  · rintro ⟨w, hw, rfl⟩
    apply cone_sum (convex_convexHull ℝ _) ((range_nonempty v).mono (subset_convexHull ℝ _))
    intro i _
    exact cone_smul (lift_mem_cone.mpr (subset_convexHull ℝ _ (mem_range_self i))) (hw i)

end Submission.Obl.Cone__simplex_iff_product
