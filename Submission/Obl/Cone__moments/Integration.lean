import Submission.Obl.Cone__moments.Geometry

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Submission.Obl.Cone__moments

noncomputable def coords (n : ℕ) : E (n + 1) ≃ᵐ ℝ × E n :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ)))

lemma coords_measurePreserving (n : ℕ) : MeasurePreserving (coords n) := by
  exact ((PiLp.volume_preserving_ofLp (Fin (n + 1))).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)).trans
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin n)))

noncomputable def join {n : ℕ} (t : ℝ) (x : E n) : E (n + 1) :=
  WithLp.toLp 2 (Fin.cons t x)

@[simp] lemma join_zero {n : ℕ} (t : ℝ) (x : E n) : join t x 0 = t := rfl
@[simp] lemma join_succ {n : ℕ} (t : ℝ) (x : E n) (i : Fin n) :
    join t x i.succ = x i := rfl

lemma coords_symm_apply {n : ℕ} (p : ℝ × E n) : (coords n).symm p = join p.1 p.2 := by
  rcases p with ⟨t, x⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [coords, join, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr]

lemma continuous_join (n : ℕ) : Continuous (fun p : ℝ × E n => join p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun p : ℝ × E n => p.1)
    exact continuous_fst
  · change Continuous (fun p : ℝ × E n => p.2 j)
    fun_prop

lemma join_smul {n : ℕ} (t : ℝ) (x : E n) : join t (t • x) = t • join 1 x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma join_mem_cone {n : ℕ} {K : Set (E n)} {t : ℝ} (ht : 0 < t) (x : E n) :
    join t x ∈ cone K ↔ t⁻¹ • x ∈ K := by
  constructor
  · rintro ⟨_, y, hy, heq⟩
    have : t⁻¹ • x = y := by
      ext i
      change t⁻¹ * x i = y i
      simpa only [join_zero, join_succ, inv_mul_cancel_left₀ ht.ne'] using
        congrArg (t⁻¹ * ·) (heq i)
    rwa [this]
  · intro hx
    refine ⟨ht.le, t⁻¹ • x, hx, fun i => ?_⟩
    simp [mul_inv_cancel_left₀ ht.ne']

lemma integrable_gamma_nat (k : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ k) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    (Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))

lemma integral_gamma_nat (k : ℕ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ k) = (k.factorial : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial]
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    (Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)).symm

lemma density_measurable {n : ℕ} {K : Set (E n)} (hK : IsCompact K) : Measurable (density K) := by
  exact (show Continuous (fun z : E (n + 1) =>
    Real.exp (-z 0) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) by fun_prop).measurable.indicator
      (cone_closed hK).measurableSet

lemma homogeneous_slice {n k : ℕ} {K : Set (E n)} {g : E (n + 1) → ℝ}
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z)
    {t : ℝ} (ht : 0 < t) (x : E n) :
    density K (join t x) * g (join t x) =
      (Real.exp (-t) * t ^ k / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) *
        (K.indicator (fun y => g (join 1 y))) (t⁻¹ • x) := by
  classical
  have hj : join t x = t • join 1 (t⁻¹ • x) := by
    simpa only [smul_inv_smul₀ ht.ne'] using join_smul t (t⁻¹ • x)
  by_cases hx : t⁻¹ • x ∈ K
  · rw [density, indicator_of_mem ((join_mem_cone ht x).mpr hx),
      indicator_of_mem hx, join_zero, hj, hg t ht]
    ring
  · rw [density, indicator_of_notMem (mt (join_mem_cone ht x).mp hx),
      indicator_of_notMem hx]
    simp

lemma density_join_neg {n : ℕ} (K : Set (E n)) {t : ℝ} (ht : t < 0) (x : E n) :
    density K (join t x) = 0 := by
  apply indicator_of_notMem
  intro h
  exact ht.not_ge h.1

lemma homogeneous_slice_integrable {n k : ℕ} {K : Set (E n)} (hK : IsCompact K)
    {g : E (n + 1) → ℝ} (hc : Continuous g)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z)
    {t : ℝ} (ht : 0 < t) : Integrable (fun x => density K (join t x) * g (join t x)) := by
  simp_rw [homogeneous_slice hg ht]
  apply Integrable.const_mul
  apply Integrable.comp_smul _ (inv_ne_zero ht.ne')
  apply IntegrableOn.integrable_indicator _ hK.measurableSet
  exact ContinuousOn.integrableOn_compact hK
    (hc.comp ((continuous_join n).comp (continuous_const.prodMk continuous_id))).continuousOn

lemma homogeneous_slice_integral {n k : ℕ} {K : Set (E n)} (hK : MeasurableSet K)
    {g : E (n + 1) → ℝ}
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, density K (join t x) * g (join t x)) =
      (Real.exp (-t) * t ^ (n + k) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) *
        ∫ x in K, g (join 1 x) := by
  simp_rw [homogeneous_slice hg ht]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ ht.le,
    integral_indicator hK]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_add]
  ring

lemma homogeneous_slice_integral_ae {n k : ℕ} {K : Set (E n)} (hK : MeasurableSet K)
    {g : E (n + 1) → ℝ}
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z) :
    (fun t => ∫ x, density K (join t x) * g (join t x)) =ᵐ[volume]
      (Ioi 0).indicator (fun t =>
        (Real.exp (-t) * t ^ (n + k) / ((n.factorial : ℝ) * SimplexIsotropic.vol K)) *
          ∫ x in K, g (join 1 x)) := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff]
  filter_upwards [hne] with t ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · simp [density_join_neg K ht, indicator_of_notMem (show t ∉ Ioi 0 from not_lt.mpr ht.le)]
  · rw [indicator_of_mem (show t ∈ Ioi 0 from ht), homogeneous_slice_integral hK hg ht]

lemma homogeneous_integrable {n k : ℕ} {K : Set (E n)}
    (hK : SimplexIsotropic.IsConvexBody K) {g : E (n + 1) → ℝ} (hc : Continuous g)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z) :
    Integrable (fun z => density K z * g z) := by
  have hm : Measurable (fun z => density K z * g z) :=
    (density_measurable hK.isCompact).mul hc.measurable
  apply ((coords_measurePreserving n).symm.integrable_comp hm.aestronglyMeasurable).mp
  change Integrable (fun p : ℝ × E n => density K ((coords n).symm p) * g ((coords n).symm p))
  simp_rw [coords_symm_apply]
  apply (integrable_prod_iff (hm.comp (continuous_join n).measurable).aestronglyMeasurable).mpr
  change (∀ᵐ t : ℝ, Integrable (fun x : E n => density K (join t x) * g (join t x))) ∧
    Integrable (fun t : ℝ => ∫ x : E n, ‖density K (join t x) * g (join t x)‖)
  constructor
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · simp only [density_join_neg K ht, zero_mul]
      exact integrable_zero _ _ _
    · exact homogeneous_slice_integrable hK.isCompact hc hg ht
  · have hgn : ∀ (t : ℝ), 0 < t → ∀ z, ‖g (t • z)‖ = t ^ k * ‖g z‖ := by
      intro t ht z
      rw [hg t ht z, norm_mul, norm_pow, Real.norm_of_nonneg ht.le]
    have hi : IntegrableOn (fun t : ℝ =>
        Real.exp (-t) * t ^ (n+k) / ((n.factorial : ℝ) * SimplexIsotropic.vol K) *
          ∫ x in K, ‖g (join 1 x)‖) (Ioi 0) :=
      ((integrable_gamma_nat (n+k)).div_const _).mul_const _
    apply (hi.integrable_indicator measurableSet_Ioi).congr
    filter_upwards [(homogeneous_slice_integral_ae (g := fun z => ‖g z‖) hK.isCompact.measurableSet hgn).symm] with t ht
    rw [ht]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (density_nonneg hK _)]

lemma homogeneous_integral {n k : ℕ} {K : Set (E n)}
    (hK : SimplexIsotropic.IsConvexBody K) {g : E (n + 1) → ℝ} (hc : Continuous g)
    (hg : ∀ (t : ℝ), 0 < t → ∀ z, g (t • z) = t ^ k * g z) :
    (∫ z, density K z * g z) =
      ((n+k).factorial : ℝ) / ((n.factorial : ℝ) * SimplexIsotropic.vol K) *
        ∫ x in K, g (join 1 x) := by
  rw [← (coords_measurePreserving n).symm.integral_comp' (fun z => density K z * g z)]
  simp_rw [coords_symm_apply]
  change (∫ p : ℝ × E n, density K (join p.1 p.2) * g (join p.1 p.2) ∂(volume.prod volume)) = _
  rw [integral_prod _ (by
    convert! (coords_measurePreserving n).symm.integrable_comp_of_integrable
        (homogeneous_integrable hK hc hg) using 1
    simp only [Function.comp_def, coords_symm_apply])]
  rw [integral_congr_ae (homogeneous_slice_integral_ae hK.isCompact.measurableSet hg),
    integral_indicator measurableSet_Ioi, integral_mul_const, integral_div, integral_gamma_nat]

end Submission.Obl.Cone__moments
