import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientBounds
import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientCriterion
import Submission.Obl.Entropy__smooth_gaussian_transport.LocalizedSchauder

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem quotient_tendstoUniformlyOn_of_global_holder {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {α : ℝ} (hα : 0 < α)
    (hDf : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f))
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (nhds 0)) (v : X) (K : Set X) :
    TendstoUniformlyOn (fun n => directionalQuotient f (h n) v)
      (fun x => fderiv ℝ f x v) atTop K := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hDf
  apply directionalQuotient_tendstoUniformlyOn_of_holder hf hh hlim v hα
  intro n x hx t ht
  have hd : ‖(x + t • (h n • v)) - x‖ ≤ |h n| * ‖v‖ := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (by positivity) ht.2
  exact (hm () _ _).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hd hα.le) hC)

/-- Uniform Schauder estimates for quotients give two derivatives and a Hölder
Hessian for the localized directional derivative. -/
theorem exists_quotient_schauder_threshold (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (f χ : E m → ℝ) (h : ℕ → ℝ) (v : E m)
      (g : ℕ → E m → ℝ) (T : ℕ → E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ),
      ContDiff ℝ 2 f → ContDiff ℝ 3 χ → HasCompactSupport χ →
      (∀ n, h n ≠ 0) → Tendsto h atTop (nhds 0) →
      UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f) →
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 f) →
      UniformBoundedHolder α g → UniformBoundedHolder α T →
      (∀ n x, ‖T n x‖ ≤ ε) →
      (∀ n x, χ x ≠ 0 → laplacian (directionalQuotient f (h n) v) x =
        g n x + T n x (iteratedFDeriv ℝ 2 (directionalQuotient f (h n) v) x)) →
      ContDiff ℝ 2 (fun x => χ x * fderiv ℝ f x v) ∧
        UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun x => χ x * fderiv ℝ f x v)) := by
  obtain ⟨ε, hε, hS⟩ := exists_localized_schauder_threshold m hα hα1
  refine ⟨ε, hε, ?_⟩
  intro f χ h v g T hf hχ hχc hh hlim hD hH hg hT hsmall heq
  have hDD : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ (fderiv ℝ f)) := by
    obtain ⟨M, C, hM, hC, hb, hm⟩ := hH
    refine ⟨M, C, hM, hC, ?_, ?_⟩
    · intro i x; rw [norm_second_fderiv]; exact hb i x
    · intro i x y; rw [norm_second_fderiv_sub]; exact hm i x y
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hu := uniformBoundedHolder_quotients hf1 hD h hh v
  have hDu : UniformBoundedHolder α (fun n => fderiv ℝ (directionalQuotient f (h n) v)) := by
    convert! uniformBoundedHolder_quotients hDf1 hDD h hh v using 1
    funext n x
    exact directionalQuotient_fderiv hf1.differentiable_one (h n) v x
  have hex (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ 2 (fun z => χ z * directionalQuotient f (h n) v z) x -
        iteratedFDeriv ℝ 2 (fun z => χ z * directionalQuotient f (h n) v z) y‖ ≤ C * ‖x - y‖ ^ α := by
    have hqn : UniformBoundedHolder α
        (fun (_ : Unit) => iteratedFDeriv ℝ 2 (directionalQuotient f (h n) v)) := by
      convert! uniformBoundedHolder_fixed_quotient hH (h n) v using 1
      funext i x
      exact directionalQuotient_iteratedFDeriv hf (h n) v x
    obtain ⟨M, C, hM, hC, hb, hm⟩ := uniformBoundedHolder_hessian_mul hχ hχc hα hα1.le
      (fun (_ : Unit) => directionalQuotient_contDiff hf (h n) v)
      (hu.reindex (fun (_ : Unit) => n)) (hDu.reindex (fun (_ : Unit) => n)) hqn
    exact ⟨C, hC, hm ()⟩
  exact cutoff_directionalDerivative_contDiff_two hf (hχ.of_le (by norm_num)) hχc v hα
    (quotient_tendstoUniformlyOn_of_global_holder hf1 hα hD hh hlim v _)
    (quotient_tendstoUniformlyOn_of_global_holder hDf1 hα hDD hh hlim v _)
    (hS χ (fun n => directionalQuotient f (h n) v) g T hχ hχc
      (fun n => directionalQuotient_contDiff hf (h n) v) hu hDu hg hT hsmall heq hex)

end Submission.Obl.Entropy__smooth_gaussian_transport
