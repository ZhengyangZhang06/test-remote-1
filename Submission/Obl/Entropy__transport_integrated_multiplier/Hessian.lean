import Submission.Obl.Entropy__transport_integrated_multiplier.MatrixLp

open MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma bilinear_matrix_quad
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (Matrix.mulVec (Matrix.of fun i j => B (PiLp.single 2 i 1) (PiLp.single 2 j 1)) v) =
      B (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  have hv : (∑ i, v i • (PiLp.single 2 i 1 : EuclideanSpace ℝ ι)) = WithLp.toLp 2 v := by
    ext i
    simp [Pi.single_apply, Finset.sum_apply]
  rw [← hv]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_trivial,
    map_sum, sum_apply, map_smul, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinear_matrix_posSemidef
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v, 0 ≤ B v v) :
    (Matrix.of fun i j => B (PiLp.single 2 i 1) (PiLp.single 2 j 1)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial] using hB _ _
  · intro v
    rw [bilinear_matrix_quad]
    exact hpos _

lemma bilinear_matrix_entry_bound
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v, 0 ≤ B v v)
    {C : ℝ} (hC : 0 ≤ C) (hupper : ∀ v, B v v ≤ C * ‖v‖ ^ 2) (i j : ι) :
    |B (PiLp.single 2 i 1) (PiLp.single 2 j 1)| ≤ C := by
  let u : EuclideanSpace ℝ ι := PiLp.single 2 i 1
  let v : EuclideanSpace ℝ ι := PiLp.single 2 j 1
  have hu : ‖u‖ = 1 := by simp [u, PiLp.norm_single]
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  have hp : ‖u + v‖ ^ 2 ≤ 4 := by
    have hn := norm_add_le u v
    rw [hu, hv] at hn
    nlinarith [norm_nonneg (u + v)]
  have hm : ‖u - v‖ ^ 2 ≤ 4 := by
    have hn := norm_sub_le u v
    rw [hu, hv] at hn
    nlinarith [norm_nonneg (u - v)]
  have h1 : B (u + v) (u + v) ≤ 4 * C := (hupper _).trans (by nlinarith)
  have h2 : B (u - v) (u - v) ≤ 4 * C := (hupper _).trans (by nlinarith)
  have h3 := hpos (u + v)
  have h4 := hpos (u - v)
  simp only [map_add, map_sub, add_apply, sub_apply,
    hB v u] at h1 h2 h3 h4
  change |B u v| ≤ C
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma hessian_matrix_posSemidef {V : EuclideanSpace ℝ ι → ℝ}
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (x : EuclideanSpace ℝ ι) :
    (Matrix.of fun i j => fderiv ℝ (fderiv ℝ V) x
      (PiLp.single 2 i 1) (PiLp.single 2 j 1)).PosSemidef := by
  apply bilinear_matrix_posSemidef _ _ (hpos x)
  exact hV.contDiffAt.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤))

lemma entryLp_top_hessian_comp
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ ∞ V)
    {g : X → EuclideanSpace ℝ ι} (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v ∧
      fderiv ℝ (fderiv ℝ V) x v v ≤ C * ‖v‖ ^ 2) :
    EntryLp ∞ (fun x => Matrix.of fun i j => fderiv ℝ (fderiv ℝ V) (g x)
      (PiLp.single 2 i 1) (PiLp.single 2 j 1)) μ := by
  intro i j
  have hc : Continuous (fderiv ℝ (fderiv ℝ V)) :=
    (hV.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  refine memLp_top_of_bound ?_ C (ae_of_all _ fun x => ?_)
  · exact (((hc.comp hg).eval_const _).eval_const _).aestronglyMeasurable
  · change |fderiv ℝ (fderiv ℝ V) (g x) (PiLp.single 2 i 1) (PiLp.single 2 j 1)| ≤ C
    exact bilinear_matrix_entry_bound _
      (hV.contDiffAt.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤)))
      (fun v => (hbound (g x) v).1) hC (fun v => (hbound (g x) v).2) i j

end Submission.Obl.Entropy__transport_integrated_multiplier
