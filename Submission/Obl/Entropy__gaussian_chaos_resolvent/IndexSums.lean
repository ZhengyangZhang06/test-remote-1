import Submission.Obl.Entropy__gaussian_chaos_resolvent.CoordinateDerivative

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

noncomputable def chaosDegree {m : ℕ} (a : Fin m → ℕ) : ℕ := ∑ i, a i

theorem raiseIndex_injective {m : ℕ} (r : Fin m) :
    Function.Injective (fun a : Fin m → ℕ => raiseIndex a r) := by
  intro a b hab
  funext i
  have h := congrFun hab i
  by_cases hi : i = r
  · subst i
    simpa using h
  · simpa [raiseIndex, Function.update_of_ne hi] using h

theorem mem_range_raiseIndex {m : ℕ} (r : Fin m) (a : Fin m → ℕ) :
    a ∈ Set.range (fun b => raiseIndex b r) ↔ 0 < a r := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro ha
    refine ⟨Function.update a r (a r - 1), ?_⟩
    funext i
    by_cases hi : i = r
    · subst i
      simp only [raiseIndex_self, Function.update_self]
      omega
    · simp [raiseIndex, Function.update_of_ne hi]

theorem chaosDegree_raiseIndex {m : ℕ} (a : Fin m → ℕ) (r : Fin m) :
    chaosDegree (raiseIndex a r) = chaosDegree a + 1 := by
  have h : raiseIndex a r = fun i => a i + if i = r then 1 else 0 := by
    funext i
    by_cases hi : i = r <;> simp [raiseIndex, hi]
  simp [chaosDegree, h, Finset.sum_add_distrib]

theorem chaosDegree_eq_zero {m : ℕ} (a : Fin m → ℕ) :
    chaosDegree a = 0 ↔ a = 0 := by
  simp [chaosDegree, funext_iff]

theorem tsum_raiseIndex {m : ℕ} (r : Fin m) (F : (Fin m → ℕ) → ℝ) :
    (∑' b, (b r + 1 : ℝ) * F (raiseIndex b r)) = ∑' a, (a r : ℝ) * F a := by
  have hsupport : Function.support (fun a => (a r : ℝ) * F a) ⊆
      Set.range (fun b => raiseIndex b r) := by
    intro a ha
    apply (mem_range_raiseIndex r a).mpr
    by_contra h
    have h0 : a r = 0 := by omega
    exact ha (by simp [h0])
  simpa using (raiseIndex_injective r).tsum_eq hsupport

theorem summable_raiseIndex_iff {m : ℕ} (r : Fin m) (F : (Fin m → ℕ) → ℝ) :
    Summable (fun b => (b r + 1 : ℝ) * F (raiseIndex b r)) ↔
      Summable (fun a => (a r : ℝ) * F a) := by
  have hzero : ∀ a ∉ Set.range (fun b => raiseIndex b r), (a r : ℝ) * F a = 0 := by
    intro a ha
    have h0 : a r = 0 := by
      rw [mem_range_raiseIndex] at ha
      omega
    simp [h0]
  simpa [Function.comp_def] using (raiseIndex_injective r).summable_iff hzero

end Submission.Obl.Entropy__gaussian_chaos_resolvent
