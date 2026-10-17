import Submission.Obl.Entropy__transport_covariance_completion.Spectral
import Submission.Obl.Entropy__c1_bounded_matrix_calculus
import Submission.Lib.GaussianTransport.GaussianModel
import Submission.Obl.Entropy__centered_slack_transports.Fields

namespace Submission.Obl.Entropy__transport_covariance_completion

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff

lemma contDiff_hazard : ContDiff ℝ ∞ hazard :=
  Submission.Lib.GaussianTransport.contDiff_gaussianHazard

lemma contDiff_tailLog : ContDiff ℝ ∞ tailLog :=
  Submission.Lib.GaussianTransport.contDiff_exponentialTransport

lemma contDiff_ratioK : ContDiff ℝ ∞ ratioK :=
  contDiff_tailLog.div contDiff_hazard (fun a => (hazard_pos a).ne')

theorem cfc_hazard_mul_ratioK {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (_hA : A.IsHermitian) :
    cfc hazard A * cfc ratioK A = cfc tailLog A := by
  rw [← cfc_mul hazard ratioK A contDiff_hazard.continuous.continuousOn contDiff_ratioK.continuous.continuousOn]
  congr 1
  funext a
  exact mul_div_cancel₀ _ (hazard_pos a).ne'

theorem cfc_ratioK_mul_hazard {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (_hA : A.IsHermitian) :
    cfc ratioK A * cfc hazard A = cfc tailLog A := by
  rw [← cfc_mul ratioK hazard A contDiff_ratioK.continuous.continuousOn contDiff_hazard.continuous.continuousOn]
  congr 1
  funext a
  exact div_mul_cancel₀ _ (hazard_pos a).ne'

theorem cfc_field_memLp {m : ℕ} (hm : 1 ≤ m)
    {A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hA : ∀ x, (A x).IsHermitian)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    (∀ i j, ContDiff ℝ 1 (fun x => cfc g (A x) i j)) ∧
    (∀ i j, MemLp (fun x => cfc g (A x) i j) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
  obtain ⟨hcont, hbound⟩ := Submission.Entropy.c1_bounded_matrix_calculus m hm A hA
    (fun i j => (hs i j).of_le (by exact WithTop.coe_le_coe.mpr le_top)) hb g
    (hg.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  exact ⟨hcont, Submission.Obl.Entropy__centered_slack_transports.field_memLp
    (fun i j => (hcont i j).continuous) hbound⟩

theorem derivative_isHermitian {m : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hF : ∀ x, (F x).IsHermitian) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    (Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x
      (PiLp.single 2 r (1 : ℝ)))).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, of_apply]
  have he : (fun y => F y j i) = (fun y => F y i j) := by
    funext y
    simpa using congrFun (congrFun (hF y).eq i) j
  rw [he]

end Submission.Obl.Entropy__transport_covariance_completion
