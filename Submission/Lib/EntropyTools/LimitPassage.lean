/-
Adapted from: here:o001

Original proofs by session x0004.
-/

import Submission.Lib.EntropyTools.DensityMoments

/-!
# The passage to the limit at the end of Section 5

These lemmas isolate the exact convergence data needed from the paper's
approximation lemma. The existence of smooth approximations and the entropy
inequality for those approximations are separate inputs.
-/

open MeasureTheory Filter
open scoped Topology

namespace Submission.Lib.EntropyTools

/-- The entropy inequality is closed under entropy and covariance convergence
when the limiting covariance determinant is nonzero. -/
theorem entropy_lower_bound_of_tendsto {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℝ} {H : ℝ}
    {Cn : ℕ → Matrix (Fin m) (Fin m) ℝ} {Hn : ℕ → ℝ}
    (hC : ∀ i j, Tendsto (fun n => Cn n i j) atTop (𝓝 (C i j)))
    (hH : Tendsto Hn atTop (𝓝 H)) (hdet : C.det ≠ 0)
    (hbound : ∀ᶠ n in atTop, (m : ℝ) + Real.log (Cn n).det / 2 ≤ Hn n) :
    (m : ℝ) + Real.log C.det / 2 ≤ H := by
  have hmat : Tendsto Cn atTop (𝓝 C) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (hC i)
  have hdetlim : Tendsto (fun n => (Cn n).det) atTop (𝓝 C.det) :=
    (continuous_id.matrix_det.tendsto C).comp hmat
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.add ((hdetlim.log hdet).div_const 2)) hH hbound

/-- Convergence of the first and raw second moments gives covariance convergence. -/
theorem densityCovariance_tendsto_of_moments {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {fn : ℕ → EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hprob : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hfn : ∀ n, Integrable (fn n) volume)
    (hprobn : ∀ n, ∫ x, fn n x = 1)
    (hfn2 : ∀ n, Integrable (fun x => fn n x * ‖x‖ ^ 2) volume)
    (hfirst : ∀ i, Tendsto (fun n => ∫ x, fn n x * x i) atTop
      (𝓝 (∫ x, f x * x i)))
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, fn n x * x i * x j) atTop
      (𝓝 (∫ x, f x * x i * x j))) (i j : Fin m) :
    Tendsto (fun n => densityCovariance (fn n) (∫ x, fn n x • x) i j) atTop
      (𝓝 (densityCovariance f (∫ x, f x • x) i j)) := by
  simp_rw [densityCovariance_eq_raw_moments hf0 hf hprob hf2 _ rfl,
    densityCovariance_eq_raw_moments (hfn0 _) (hfn _) (hprobn _) (hfn2 _) _ rfl,
    density_mean_apply hf0 hf hf2, density_mean_apply (hfn0 _) (hfn _) (hfn2 _)]
  exact (hsecond i j).sub ((hfirst i).mul (hfirst j))

/-- Section 5's final step, expressed using the raw moments of the approximating
probability densities. -/
theorem density_entropy_lower_bound_of_moment_limits {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {fn : ℕ → EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hprob : ∫ x, f x = 1)
    (hf2 : Integrable (fun x => f x * ‖x‖ ^ 2) volume)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hfn : ∀ n, Integrable (fn n) volume)
    (hprobn : ∀ n, ∫ x, fn n x = 1)
    (hfn2 : ∀ n, Integrable (fun x => fn n x * ‖x‖ ^ 2) volume)
    (hfirst : ∀ i, Tendsto (fun n => ∫ x, fn n x * x i) atTop
      (𝓝 (∫ x, f x * x i)))
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, fn n x * x i * x j) atTop
      (𝓝 (∫ x, f x * x i * x j)))
    (hentropy : Tendsto (fun n => -∫ x, fn n x * Real.log (fn n x)) atTop
      (𝓝 (-∫ x, f x * Real.log (f x))))
    (hbound : ∀ n, (m : ℝ) +
      Real.log (densityCovariance (fn n) (∫ x, fn n x • x)).det / 2 ≤
        -∫ x, fn n x * Real.log (fn n x)) :
    (m : ℝ) + Real.log (densityCovariance f (∫ x, f x • x)).det / 2 ≤
      -∫ x, f x * Real.log (f x) := by
  apply entropy_lower_bound_of_tendsto
    (densityCovariance_tendsto_of_moments hf0 hf hprob hf2 hfn0 hfn hprobn hfn2
      hfirst hsecond) hentropy
    (ne_of_gt (densityCovariance_det_pos hf0 hf hprob hf2 _))
  exact Eventually.of_forall hbound

end Submission.Lib.EntropyTools
