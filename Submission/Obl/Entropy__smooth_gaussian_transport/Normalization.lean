import Submission.Obl.Entropy__smooth_gaussian_transport.Tilting

open MeasureTheory Set Filter Module
open scoped Topology RealInnerProductSpace ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A maximal-volume parallelotope with its edges in a compact neighborhood gives
coordinates of absolute value at most one throughout that neighborhood. -/
theorem exists_bounded_coordinate_basis {m : ℕ} {K : Set (E m)}
    (hK : IsCompact K) (h0 : K ∈ 𝓝 (0 : E m)) :
    ∃ b : Basis (Fin m) ℝ (E m), (∀ i, b i ∈ K) ∧
      ∀ x ∈ K, ∀ i, |b.repr x i| ≤ 1 := by
  classical
  let e := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp h0
  let w : Fin m → E m := fun i => (ε / 2) • e i
  have hw : ∀ i, w i ∈ K := by
    intro i
    apply hεK
    have he : ‖e i‖ = 1 := (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.norm_eq_one i
    simp only [Metric.mem_ball, dist_zero_right, w, norm_smul, Real.norm_eq_abs, he,
      abs_of_pos (half_pos hε), mul_one]
    linarith
  have hwd : e.det w = (ε / 2) ^ m := by
    simp only [w, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, e.det_self, smul_eq_mul, mul_one]
  have hc : Continuous (fun v : Fin m → E m => |e.det v|) := by
    change Continuous (fun v : Fin m → E m => |(Matrix.of (fun i j => (v j) i)).det|)
    fun_prop
  have hprod : IsCompact {v : Fin m → E m | ∀ i, v i ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  obtain ⟨v, hv, hmax⟩ := hprod.exists_isMaxOn ⟨w, hw⟩ hc.continuousOn
  have hdet : e.det v ≠ 0 := by
    have hp : 0 < |e.det w| := by rw [hwd, abs_of_pos (pow_pos (half_pos hε) _)]; positivity
    exact abs_pos.mp (hp.trans_le (hmax hw))
  obtain ⟨hli, hspan⟩ := (e.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hdet)
  let b := Basis.mk hli hspan.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Basis.mk_apply] using hv i
  · intro x hx i
    have hu : ∀ j, Function.update v i x j ∈ K := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa using hx
      · simpa only [Function.update_of_ne hj] using hv j
    have hd := congrArg (fun f : E m →ₗ[ℝ] ℝ => f x)
      (e.det_smul_mk_coord_eq_det_update hli hspan.ge i)
    have heq : e.det v * b.repr x i = e.det (Function.update v i x) := by
      convert! hd using 1
    have hbound : |e.det (Function.update v i x)| ≤ |e.det v| := hmax hu
    rw [← heq, abs_mul] at hbound
    exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp (by simpa using hbound)

theorem sum_smul_mem_of_sum_le_one {m : ℕ} {K : Set (E m)} (hK : Convex ℝ K)
    (h0 : (0 : E m) ∈ K) {v : Fin m → E m} (hv : ∀ i, v i ∈ K)
    {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    ∑ i, w i • v i ∈ K := by
  let W (i : Option (Fin m)) := Option.elim i (1 - ∑ j, w j) w
  let P (i : Option (Fin m)) := Option.elim i (0 : E m) v
  have hW : ∀ i ∈ (Finset.univ : Finset (Option (Fin m))), 0 ≤ W i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hw i
  have hP : ∀ i ∈ (Finset.univ : Finset (Option (Fin m))), P i ∈ K := by
    intro i _
    cases i with
    | none => exact h0
    | some i => exact hv i
  have hWs : ∑ i, W i = 1 := by simp [W, Fintype.sum_option]
  simpa [W, P, Fintype.sum_option] using hK.sum_mem hW hWs hP

theorem norm_le_sum_abs_coordinates {m : ℕ} (x : E m) : ‖x‖ ≤ ∑ i, |x i| := by
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  have he : (∑ i, x i • e i) = x := by
    simpa only [e, EuclideanSpace.basisFun_repr] using e.sum_repr x
  calc
    ‖x‖ = ‖∑ i, x i • e i‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖x i • e i‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := by simp [norm_smul, e.orthonormal.norm_eq_one]

/-- Coordinate normalization of a compact convex neighborhood: a fixed simplex is
inside the image, while the image lies in the unit coordinate cube. -/
theorem exists_simplex_cube_normalization {m : ℕ} {K : Set (E m)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : E m)) :
    ∃ L : E m ≃L[ℝ] E m,
      {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ⊆ L '' K ∧
      L '' K ⊆ {y | ∀ i, |y i| ≤ 1} := by
  obtain ⟨b, hb, hbound⟩ := exists_bounded_coordinate_basis hK h0
  let L : E m ≃L[ℝ] E m := b.equivFunL.trans (EuclideanSpace.equiv (Fin m) ℝ).symm
  have hL (x : E m) (i : Fin m) : (L x) i = b.repr x i := rfl
  refine ⟨L, ?_, ?_⟩
  · intro y hy
    have hmem : ∑ i, y i • b i ∈ K :=
      sum_smul_mem_of_sum_le_one hc (mem_of_mem_nhds h0) hb hy.1 hy.2
    refine ⟨∑ i, y i • b i, hmem, ?_⟩
    apply (EuclideanSpace.equiv (Fin m) ℝ).injective
    ext i
    simp [hL, map_sum, map_smul, b.repr_self, Finsupp.single_apply, mul_ite]
  · rintro _ ⟨x, hx, rfl⟩ i
    rw [hL]
    exact hbound x hx i

end Submission.Obl.Entropy__smooth_gaussian_transport
