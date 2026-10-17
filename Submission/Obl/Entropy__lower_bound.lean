import Mathlib
import ChallengeDeps
import Submission.Lib.EntropyTools
import Submission.Obl.Entropy__normalized_transport
import Submission.Obl.Entropy__normalized_remainder
import Submission.Obl.Entropy__smooth_approximation

/-!
# Entropy lower bound from the three analytic steps

The children isolate Proposition 2.3, Theorem 3.1, and Lemma 5.2 of the
supplied paper. The accepted EntropyTools library supplies covariance
positivity, the scalar remainder sign, and the final passage to the limit.
-/

open MeasureTheory
open Submission.Lib.EntropyTools

theorem Submission.Entropy.lower_bound : ∀ m : ℕ, 1 ≤ m → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → UpperSemicontinuous f → ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖ ^ 2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∀ b : (EuclideanSpace ℝ (Fin m)), b = MeasureTheory.integral MeasureTheory.volume (fun x => f x • x) → ∀ C : Matrix (Fin m) (Fin m) ℝ, C = (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - b i) * (x j - b j))) → ∀ H : ℝ, H = -MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)) → (m : ℝ) + Real.log C.det / 2 ≤ H := by
  intro m hm f hf0 hfupper hfconc hf hmass hf2 hfentropy b hb C hC H hH
  subst b
  subst C
  subst H
  obtain ⟨V, hV, hHlim, hClim, hmeanlim, hL1lim⟩ :=
    Submission.Entropy.smooth_approximation m hm f hf0 hfupper hfconc hf hmass hf2 hfentropy
  apply entropy_lower_bound_of_tendsto hClim hHlim
    (ne_of_gt (densityCovariance_det_pos hf0 hf hmass hf2 _))
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨W, φ, A, L, hW, hnormalized, hsym, hpos, htransform, hgap⟩ :=
    Submission.Entropy.normalized_transport m hm (V n) (hV n)
  obtain ⟨hB, hremainder⟩ :=
    Submission.Entropy.normalized_remainder m hm W hW φ A hnormalized
  have hnonneg : (0 : ℝ) ≤ _ := le_trans (show (0 : ℝ) ≤ _ from ?_) hremainder
  · dsimp only at hgap hnonneg ⊢
    linarith
  · apply add_nonneg
    · apply div_nonneg _ (by norm_num)
      apply integral_nonneg
      intro x
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    · apply div_nonneg _ (by norm_num)
      exact Finset.sum_nonneg fun i _ => rigidityWeight_nonneg (hB.eigenvalues_nonneg i)
