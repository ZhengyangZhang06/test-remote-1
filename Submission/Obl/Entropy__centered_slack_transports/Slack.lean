import Submission.Lib.EntropyTools.Remainder

open Filter
open scoped Topology BigOperators

namespace Submission.Obl.Entropy__centered_slack_transports

open Submission.Lib.EntropyTools

/-- Both nonnegative terms in the strict remainder vanish with its upper bound. -/
theorem vanish_of_slack {m : ℕ} (energy δ : ℕ → ℝ) (ell : ℕ → Fin m → ℝ)
    (henergy : ∀ n, 0 ≤ energy n) (hell : ∀ n i, 0 ≤ ell n i)
    (hδ : Tendsto δ atTop (nhds 0))
    (hbound : ∀ n, energy n / 500 + (∑ i, rigidityWeight (ell n i)) / 1000 ≤ δ n) :
    Tendsto energy atTop (nhds 0) ∧
      Tendsto (fun n => ∑ i, rigidityWeight (ell n i)) atTop (nhds 0) := by
  have hsum (n : ℕ) : 0 ≤ ∑ i, rigidityWeight (ell n i) :=
    Finset.sum_nonneg fun i _ => rigidityWeight_nonneg (hell n i)
  constructor
  · apply squeeze_zero henergy (fun n => ?_) (by simpa using hδ.const_mul 500)
    have hb := hbound n
    have hs := hsum n
    linarith
  · apply squeeze_zero hsum (fun n => ?_) (by simpa using hδ.const_mul 1000)
    have hb := hbound n
    have he := henergy n
    linarith

end Submission.Obl.Entropy__centered_slack_transports
