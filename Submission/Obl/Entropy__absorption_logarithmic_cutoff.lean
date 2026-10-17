import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.absorption_logarithmic_cutoff`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__absorption_logarithmic_cutoff`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__absorption_logarithmic_cutoff/`
belong to this obligation.
-/

theorem Submission.Entropy.absorption_logarithmic_cutoff : ∀ z : ℝ, 0 ≤ z → 40 / (37 + 3*z) - 1 - Real.log (40 / (37 + 3*z)) ≤ (86/125) * ((3 * (z - 1)^2 / (37 + 3*z)) * ((3 : ℝ)/20 + ((49 : ℝ)/100)*(37/(37+3*z))) * (if z = 0 then (13 : ℝ)/100 else min ((13 : ℝ)/100) (32/(25*Real.sqrt z)))) := by
  sorry
