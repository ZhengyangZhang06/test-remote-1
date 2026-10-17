import Submission.Obl.Entropy__transport_covariance_completion.Spectral
import Submission.Obl.Entropy__transport_covariance_completion.ChangeVariables
import Submission.Obl.Entropy__transport_covariance_completion.Injective

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

/-- Smooth scalar potentials have smooth gradients. -/
theorem contDiff_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {φ : E → ℝ} {s t : WithTop ENat}
    (hφ : ContDiff ℝ t φ) (hst : s + 1 ≤ t) : ContDiff ℝ s (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.comp (hφ.fderiv_right hst)

/-- The entropy-deficit identity preceding Lemma 3.2 in the supplied paper. -/
theorem entropy_deficit_identity {m : ℕ}
    {A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hA : ∀ x, (A x).IsHermitian)
    (hAc : ∀ i j, Continuous (fun x => A x i j))
    (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f volume) (hfent : Integrable (fun x => f x * Real.log (f x)) volume)
    {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ)
    (hJ : ∀ x i j, cfc hazard (A x) i j =
      (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i)
    (hmap : Measure.map (gradient φ) (stdGaussian (EuclideanSpace ℝ (Fin m))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable (fun x => (cfc tailLog (A x)).trace) (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
    2 * (m : ℝ) + 2 * (∫ x, f x * Real.log (f x)) =
      (∫ x, ∑ i, ∑ j, (A x i j)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin m))) -
        2 * (∫ x, (cfc tailLog (A x)).trace ∂stdGaussian (EuclideanSpace ℝ (Fin m))) + m := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hF : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by exact WithTop.coe_le_coe.mpr le_top)
  have hpos x := cfc_hazard_posDef (hA x)
  have hinj := injective_of_posDef_jacobian (hF.differentiable one_ne_zero)
    (fun x => cfc hazard (A x)) hJ hpos
  have hd x : (fderiv ℝ (gradient φ) x).det = (cfc hazard (A x)).det :=
    derivative_det_eq _ _ hJ x
  have hlog x : Real.log |(fderiv ℝ (gradient φ) x).det| =
      -(∑ i, ∑ j, (A x i j)^2) / 2 -
        (m : ℝ) * Real.log (2 * Real.pi) / 2 + (cfc tailLog (A x)).trace := by
    rw [hd, abs_of_pos (hpos x).det_pos]
    simpa only [Fintype.card_fin] using log_det_hazard (hA x)
  obtain ⟨hlint, hent⟩ := entropy_change_of_variables hF hinj hf hf0 hfent hmap
  have hL2 i j := Submission.Obl.Entropy__centered_slack_transports.field_memLp hAc hAb i j
  have hiA : Integrable (fun x => ∑ i, ∑ j, (A x i j)^2) γ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hL2 i j).integrable_sq
  have ht : Integrable (fun x => (cfc tailLog (A x)).trace) γ := by
    refine (hlint.add (hiA.div_const 2) |>.add (integrable_const
      ((m : ℝ) * Real.log (2 * Real.pi) / 2))).congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply, hlog]
    ring
  refine ⟨ht, ?_⟩
  have hilog : (∫ x, Real.log |(fderiv ℝ (gradient φ) x).det| ∂γ) =
      -(∫ x, ∑ i, ∑ j, (A x i j)^2 ∂γ) / 2 -
        (m : ℝ) * Real.log (2 * Real.pi) / 2 + (∫ x, (cfc tailLog (A x)).trace ∂γ) := by
    simp_rw [hlog]
    have hia : Integrable (fun x => -(∑ i, ∑ j, (A x i j)^2) / 2) γ := hiA.neg.div_const 2
    have hib : Integrable (fun x => -(∑ i, ∑ j, (A x i j)^2) / 2 -
        (m : ℝ) * Real.log (2 * Real.pi) / 2) γ := hia.sub (integrable_const _)
    rw [integral_add hib ht,
      integral_sub hia (integrable_const ((m : ℝ) * Real.log (2 * Real.pi) / 2)),
      integral_div, integral_neg, integral_const]
    simp [γ]
  change (∫ x, f x * Real.log (f x)) = _ - (∫ x, Real.log |(fderiv ℝ (gradient φ) x).det| ∂γ) at hent
  rw [hilog] at hent
  change 2 * (m : ℝ) + 2 * (∫ x, f x * Real.log (f x)) =
    (∫ x, ∑ i, ∑ j, (A x i j)^2 ∂γ) - 2 * (∫ x, (cfc tailLog (A x)).trace ∂γ) + m
  linarith

end Submission.Obl.Entropy__transport_covariance_completion
