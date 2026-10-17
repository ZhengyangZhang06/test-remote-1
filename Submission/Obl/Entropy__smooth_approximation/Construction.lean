import Submission.Obl.Entropy__smooth_approximation.Normalization
import Submission.Obl.Entropy__log_concave_exponential_tail
import Submission.Obl.Entropy__moreau_envelope_sequence
import Submission.Obl.Entropy__mollified_convex_sequence

open MeasureTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__smooth_approximation

/-- Compose the three analytic steps of Section 5 before normalization. -/
theorem smooth_sequence_of_log_concave {m : ℕ} (hm : 1 ≤ m)
    {f : E m → ℝ} (hf0 : ∀ x, 0 ≤ f x) (husc : UpperSemicontinuous f)
    (hconc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hf : Integrable f volume) (hmass : ∫ x, f x = 1) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧ ∃ U : ℕ → E m → ℝ,
      (∀ n, SmoothPotential (U n)) ∧
      (∀ n x, a * ‖x‖ - B ≤ U n x) ∧
      ∀ x, Tendsto (fun n => density (U n) x) atTop (𝓝 (f x)) := by
  obtain ⟨a, b, ha, hb, htail⟩ :=
    Submission.Entropy.log_concave_exponential_tail m hm f hf0 husc hconc hf hmass
  have hpos : ∃ x, 0 < f x := by
    by_contra h
    have hzero : f = fun _ => 0 := by
      funext x
      exact le_antisymm (le_of_not_gt (fun hx => h ⟨x, hx⟩)) (hf0 x)
    simp [hzero] at hmass
  obtain ⟨Q, hQ, hQlower, hQlim⟩ :=
    Submission.Entropy.moreau_envelope_sequence m hm f hf0 husc hconc hpos
      a b ha hb htail
  obtain ⟨U, hU, hmajorant, hdiff⟩ :=
    Submission.Entropy.mollified_convex_sequence m hm Q hQ
  refine ⟨a, b + a ^ 2 / 2, ha, by positivity, U, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hU n).1, 2 / ((n : ℝ) + 1),
      (n : ℝ) + 1 + 2 / ((n : ℝ) + 1), by positivity, ?_, (hU n).2⟩
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro n x
    exact (hQlower n x).trans (hmajorant n x)
  · intro x
    have he : Tendsto (fun n => Real.exp (-(U n x - Q n x))) atTop (𝓝 1) := by
      simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
        (Real.continuous_exp.tendsto (-(0 : ℝ))).comp (hdiff x).neg
    have heq : (fun n => density (U n) x) =
        fun n => Real.exp (-Q n x) * Real.exp (-(U n x - Q n x)) := by
      funext n
      dsimp [density]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    simpa using (hQlim x).mul he

end Submission.Obl.Entropy__smooth_approximation
