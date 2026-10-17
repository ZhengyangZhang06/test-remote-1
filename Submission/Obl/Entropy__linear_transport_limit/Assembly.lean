import Submission.Obl.Entropy__linear_transport_limit.L2Limit
import Submission.Obl.Entropy__gaussian_l2_poincare
import Submission.Obl.Entropy__continuous_jacobian_of_l2_limit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

/-- Transfer the entrywise field bounds to the classical derivative. -/
theorem memLp_fderiv_of_field {m : ℕ} {q : ℝ → ℝ}
    (hq : ∀ U V : Mat m, U.IsHermitian → V.IsHermitian →
      (∑ i, ∑ j, (cfc q U i j - cfc q V i j) ^ 2) ≤
        ∑ i, ∑ j, (U i j - V i j) ^ 2)
    {F : E m → E m} {A : E m → Mat m}
    (hF : ContDiff ℝ 1 F)
    (hA : ∀ x, (A x).IsHermitian)
    (hAmem : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (E m)))
    (hderiv : ∀ x v i, (fderiv ℝ F x v) i = ∑ j, cfc q (A x) i j * v j) :
    MemLp (fderiv ℝ F) 2 (stdGaussian (E m)) := by
  have hJmem := memLp_cfc_entries hq hA (memLp_entries hAmem)
    (continuous_jacobian_entries hF hderiv).aestronglyMeasurable
  have heq : fderiv ℝ F = fun x => entriesCLM m (entries (cfc q (A x))) := by
    funext x
    ext v i
    exact hderiv x v i
  rw [heq]
  exact hJmem.continuousLinearMap_comp (entriesCLM m)

/-- The two analytic children give a centered C1 limit with its prescribed derivative. -/
theorem centered_C1_limit {m : ℕ}
    (Fseq : ℕ → E m → E m) (J : E m → (E m →L[ℝ] E m))
    (hF : ∀ n, ContDiff ℝ 1 (Fseq n) ∧ MemLp (Fseq n) 2 (stdGaussian (E m)) ∧
      (∫ x, Fseq n x ∂stdGaussian (E m)) = 0)
    (hDF : ∀ n, MemLp (fderiv ℝ (Fseq n)) 2 (stdGaussian (E m)))
    (hJcont : Continuous J) (hJmem : MemLp J 2 (stdGaussian (E m)))
    (hJlim : Tendsto (fun n => ∫ x, ‖fderiv ℝ (Fseq n) x - J x‖ ^ 2
      ∂stdGaussian (E m)) atTop (𝓝 0)) :
    ∃ G : E m → E m, ContDiff ℝ 1 G ∧ MemLp G 2 (stdGaussian (E m)) ∧
      (∫ x, G x ∂stdGaussian (E m)) = 0 ∧ (∀ x, fderiv ℝ G x = J x) ∧
      Tendsto (fun n => ∫ x, ‖Fseq n x - G x‖ ^ 2 ∂stdGaussian (E m)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hPoincare⟩ := Submission.Entropy.gaussian_l2_poincare m
  have hbound (n k : ℕ) :
      (∫ x, ‖Fseq n x - Fseq k x‖ ^ 2 ∂stdGaussian (E m)) ≤
        C * ∫ x, ‖fderiv ℝ (Fseq n) x - fderiv ℝ (Fseq k) x‖ ^ 2
          ∂stdGaussian (E m) := by
    have hdiff : fderiv ℝ (fun x => Fseq n x - Fseq k x) =
        fun x => fderiv ℝ (Fseq n) x - fderiv ℝ (Fseq k) x := by
      funext x
      exact fderiv_sub ((hF n).1.differentiable (by norm_num)).differentiableAt
        ((hF k).1.differentiable (by norm_num)).differentiableAt
    have hmean : (∫ x, Fseq n x - Fseq k x ∂stdGaussian (E m)) = 0 := by
      rw [integral_sub ((hF n).2.1.integrable (by norm_num))
        ((hF k).2.1.integrable (by norm_num)), (hF n).2.2, (hF k).2.2, sub_self]
    have hdiffmem : MemLp (fderiv ℝ (fun x => Fseq n x - Fseq k x)) 2
        (stdGaussian (E m)) := by
      rw [hdiff]
      exact (hDF n).sub (hDF k)
    simpa only [hdiff] using hPoincare (fun x => Fseq n x - Fseq k x)
      ((hF n).1.sub (hF k).1) ((hF n).2.1.sub (hF k).2.1) hmean hdiffmem
  obtain ⟨H, hHmem, hHmean, hHlim⟩ :=
    exists_centered_L2_limit_of_difference_bound (fun n => (hF n).2.1)
      (fun n => (hF n).2.2) hDF hJmem hJlim hC hbound
  obtain ⟨G, hGcont, hGH, hDG⟩ :=
    Submission.Entropy.continuous_jacobian_of_l2_limit m Fseq H J
      (fun n => (hF n).1) (fun n => (hF n).2.1) hHmem hDF hJmem hJcont hHlim hJlim
  refine ⟨G, hGcont, (memLp_congr_ae hGH).mpr hHmem,
    (integral_congr_ae hGH).trans hHmean, hDG, ?_⟩
  have heq (n : ℕ) :
      (∫ x, ‖Fseq n x - G x‖ ^ 2 ∂stdGaussian (E m)) =
        ∫ x, ‖Fseq n x - H x‖ ^ 2 ∂stdGaussian (E m) := by
    apply integral_congr_ae
    filter_upwards [hGH] with x hx
    rw [hx]
  simpa only [heq] using hHlim

end Submission.Obl.Entropy__linear_transport_limit
