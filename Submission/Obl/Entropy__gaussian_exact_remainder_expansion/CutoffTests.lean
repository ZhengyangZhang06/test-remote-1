import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.CompactTests

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Metric Set ContinuousLinearMap
open scoped BigOperators Topology ContDiff

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

variable {m : ℕ}

noncomputable def cutoff (n : ℕ) (x : E m) : ℝ :=
  smallBump 0 ((1 / ((n : ℝ) + 1)) • x)

lemma cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff (m:=m) n) :=
  (smallBump 0).contDiff.comp (contDiff_const_smul _)

lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (m:=m) n) :=
  (smallBump 0).hasCompactSupport.comp_smul (by positivity)

lemma cutoff_norm_le (n : ℕ) (x : E m) : ‖cutoff n x‖ ≤ 1 := by
  unfold cutoff
  rw [Real.norm_of_nonneg (smallBump 0).nonneg]
  exact (smallBump 0).le_one

lemma cutoff_fderiv (n : ℕ) (x : E m) :
    fderiv ℝ (cutoff n) x = (1 / ((n : ℝ) + 1)) •
      fderiv ℝ (smallBump 0 : E m → ℝ) ((1 / ((n : ℝ) + 1)) • x) := by
  have hs : ContDiff ℝ ∞ (smallBump (m:=m) 0 : E m → ℝ) := (smallBump 0).contDiff
  have hh := (hs.differentiable (by simp) ((1 / ((n : ℝ) + 1)) • x)).hasFDerivAt
  have he := (hh.comp x ((hasFDerivAt_id x).const_smul (1 / ((n : ℝ) + 1)))).fderiv
  change fderiv ℝ (cutoff n) x = _ at he
  rw [he]
  ext y
  simp

lemma cutoff_fderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n (x : E m), ‖fderiv ℝ (cutoff n) x‖ ≤ C := by
  have hs : ContDiff ℝ ∞ (smallBump (m:=m) 0 : E m → ℝ) := (smallBump 0).contDiff
  obtain ⟨C,hC⟩ := ((smallBump (m:=m) 0).hasCompactSupport.fderiv (𝕜:=ℝ)).exists_bound_of_continuous
    (hs.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hC0,fun n x => ?_⟩
  rw [cutoff_fderiv, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))]
  have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  exact (mul_le_mul_of_nonneg_left (hC _) (by positivity)).trans (mul_le_of_le_one_left hC0 hn)

lemma cutoff_eventually (x : E m) :
    ∀ᶠ n : ℕ in atTop, cutoff n x = 1 ∧ fderiv ℝ (cutoff n) x = 0 := by
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).smul_const x
  have hb := ht.eventually (ball_mem_nhds (0 : E m) (smallBump (m:=m) 0).rIn_pos)
  filter_upwards [hb] with n hn
  have he := (smallBump (m:=m) 0).eventuallyEq_one_of_mem_ball hn
  refine ⟨he.eq_of_nhds,?_⟩
  rw [cutoff_fderiv, he.fderiv_eq]
  simp

lemma weak_test_bounded_c1 {μ : Measure (E m)} [IsFiniteMeasure μ]
    {q : E m → ℝ} {g : Fin m → E m → ℝ}
    (hq : Integrable q μ) (hg : ∀ r, MemLp (g r) 2 μ)
    (hw : ∀ z : E m → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, q x*z x ∂μ) = ∑ r, ∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ)
    {z : E m → ℝ} (hz : ContDiff ℝ 1 z) {R : ℝ} (hR : ∀ x, ‖z x‖ ≤ R)
    (hd : ∀ r, MemLp (fun x => fderiv ℝ z x (PiLp.single 2 r (1:ℝ))) 2 μ) :
    (∫ x, q x*z x ∂μ) = ∑ r, ∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ := by
  let zs (n : ℕ) (x : E m) := cutoff n x*z x
  have hs (n) : ContDiff ℝ 1 (zs n) :=
    ((cutoff_smooth n).of_le (by simp)).mul hz
  have hsc (n) : HasCompactSupport (zs n) := (cutoff_compact n).mul_right
  have hzs (n x) : ‖zs n x‖ ≤ R := by
    calc
      _ = ‖cutoff n x‖*‖z x‖ := norm_mul _ _
      _ ≤ ‖z x‖ := mul_le_of_le_one_left (norm_nonneg _) (cutoff_norm_le n x)
      _ ≤ R := hR x
  have hder (n x) : fderiv ℝ (zs n) x =
      cutoff n x • fderiv ℝ z x + z x • fderiv ℝ (cutoff n) x :=
    fderiv_fun_mul ((cutoff_smooth n).differentiable (by simp) x) (hz.differentiable one_ne_zero x)
  have hevent (x) : ∀ᶠ n : ℕ in atTop, zs n x = z x ∧ fderiv ℝ (zs n) x = fderiv ℝ z x := by
    filter_upwards [cutoff_eventually x] with n hn
    constructor
    · simp [zs,hn.1]
    · rw [hder,hn.1,hn.2]
      simp
  obtain ⟨C,hC0,hC⟩ := cutoff_fderiv_bound (m:=m)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  have hds (n x) (e : E m) : ‖fderiv ℝ (zs n) x e‖ ≤ ‖fderiv ℝ z x e‖ + R*(C*‖e‖) := by
    rw [hder]
    simp only [add_apply,smul_apply,smul_eq_mul]
    calc
      _ ≤ ‖cutoff n x*fderiv ℝ z x e‖ + ‖z x*fderiv ℝ (cutoff n) x e‖ := norm_add_le _ _
      _ = ‖cutoff n x‖*‖fderiv ℝ z x e‖ + ‖z x‖*‖fderiv ℝ (cutoff n) x e‖ := by simp only [norm_mul]
      _ ≤ ‖fderiv ℝ z x e‖ + R*(C*‖e‖) := by
        apply add_le_add
        · exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_norm_le n x)
        · exact mul_le_mul (hR x)
            (((fderiv ℝ (cutoff n) x).le_opNorm e).trans
              (mul_le_mul_of_nonneg_right (hC n x) (norm_nonneg _))) (norm_nonneg _) hR0
  have hlim : Tendsto (fun n => ∫ x, q x*zs n x ∂μ) atTop (𝓝 (∫ x, q x*z x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖q x‖*R)
      (fun n => hq.aestronglyMeasurable.mul (hs n).continuous.aestronglyMeasurable)
      (hq.norm.mul_const R)
      (fun n => ae_of_all _ fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hzs n x) (norm_nonneg _))
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((hevent x).mono fun n hn => by dsimp only; rw [hn.1]))
  have hlimd (r : Fin m) : Tendsto (fun n => ∫ x, g r x*fderiv ℝ (zs n) x (PiLp.single 2 r (1:ℝ)) ∂μ)
      atTop (𝓝 (∫ x, g r x*fderiv ℝ z x (PiLp.single 2 r (1:ℝ)) ∂μ)) := by
    let e : E m := PiLp.single 2 r (1:ℝ)
    have hi : Integrable (fun x => ‖g r x‖*(‖fderiv ℝ z x e‖+R*(C*‖e‖))) μ := by
      simp_rw [mul_add]
      exact ((hg r).norm.integrable_mul (hd r).norm).add
        (((hg r).integrable (by norm_num)).norm.mul_const _)
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖g r x‖*(‖fderiv ℝ z x e‖+R*(C*‖e‖)))
      (fun n => (hg r).aestronglyMeasurable.mul
        (((hs n).continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
      hi (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((hevent x).mono fun n hn => by dsimp only; rw [hn.2]))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hds n x e) (norm_nonneg _)
  have he (n) := weak_test_compact_c1 hq (fun r => (hg r).integrable (by norm_num)) hw (hs n) (hsc n)
  exact tendsto_nhds_unique hlim ((tendsto_finsetSum _ fun r _ => hlimd r).congr (fun n => (he n).symm))

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
