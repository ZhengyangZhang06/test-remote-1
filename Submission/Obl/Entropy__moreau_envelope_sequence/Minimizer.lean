import Mathlib

noncomputable section
set_option linter.unusedSectionVars false

open Set Filter Topology

namespace Submission.Obl.Entropy__moreau_envelope_sequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def weight (f : E → ℝ) (t : ℝ) (x y : E) : ℝ :=
  f y * Real.exp (-(t / 2 * ‖x - y‖ ^ 2))

lemma upperSemicontinuous_mul_pos {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : UpperSemicontinuous f) (hg : Continuous g)
    (hgp : ∀ x, 0 < g x) : UpperSemicontinuous (fun x => f x * g x) := by
  rw [upperSemicontinuous_iff_IsClosed_hypograph]
  have hc : Continuous (fun p : X × ℝ => (p.1, p.2 / g p.1)) :=
    continuous_fst.prodMk (continuous_snd.div (hg.comp continuous_fst)
      (fun p => ne_of_gt (hgp p.1)))
  convert hf.IsClosed_hypograph.preimage hc using 1
  ext p
  exact (div_le_iff₀ (hgp p.1)).symm

lemma upperSemicontinuous_weight {f : E → ℝ} (hf : UpperSemicontinuous f)
    (t : ℝ) (x : E) : UpperSemicontinuous (weight f t x) := by
  apply upperSemicontinuous_mul_pos hf
  · fun_prop
  · intro y
    exact Real.exp_pos _

lemma weight_le {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t)
    (x y : E) : weight f t x y ≤ f y := by
  have h : Real.exp (-(t / 2 * ‖x - y‖ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity)
  exact mul_le_of_le_one_right (hf y) h

lemma exists_weight_max [ProperSpace E] {f : E → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hu : UpperSemicontinuous f)
    (hne : ∃ x, 0 < f x) {a b t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hb : ∀ y, f y ≤ Real.exp (b - a * ‖y‖)) (x : E) :
    ∃ p, 0 < f p ∧ ∀ y, weight f t x y ≤ weight f t x p := by
  obtain ⟨z, hz⟩ := hne
  have hz' : 0 < weight f t x z := mul_pos hz (Real.exp_pos _)
  let K := {y | weight f t x z ≤ weight f t x y}
  have hKc : IsClosed K := (upperSemicontinuous_weight hu t x).isClosed_preimage _
  have hKb : Bornology.IsBounded K := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(b - Real.log (weight f t x z)) / a, ?_⟩
    intro y hy
    have h : weight f t x z ≤ Real.exp (b - a * ‖y‖) :=
      le_trans hy ((weight_le hf ht x y).trans (hb y))
    have hh := (Real.log_le_iff_le_exp hz').2 h
    apply (le_div_iff₀ ha).2
    nlinarith
  obtain ⟨p, hp, hpm⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (s := K) ⟨z, show weight f t x z ≤ weight f t x z from le_rfl⟩
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKc, hKb⟩)
    ((upperSemicontinuous_weight hu t x).upperSemicontinuousOn K)
  have hpw : 0 < weight f t x p := hz'.trans_le hp
  refine ⟨p, (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 hpw, ?_⟩
  intro y
  by_cases hy : y ∈ K
  · exact hpm hy
  · exact (lt_of_not_ge hy).le.trans hp

def objective (f : E → ℝ) (t : ℝ) (x y : E) : ℝ :=
  -Real.log (f y) + t / 2 * ‖x - y‖ ^ 2

lemma weight_eq_exp_objective {f : E → ℝ} {t : ℝ} {x y : E} (hy : 0 < f y) :
    weight f t x y = Real.exp (-objective f t x y) := by
  rw [weight, objective, neg_add, neg_neg, Real.exp_add, Real.exp_log hy]

lemma objective_le_of_weight_le {f : E → ℝ} {t : ℝ} {x p y : E}
    (hp : 0 < f p) (hy : 0 < f y) (h : weight f t x y ≤ weight f t x p) :
    objective f t x p ≤ objective f t x y := by
  rw [weight_eq_exp_objective hy, weight_eq_exp_objective hp, Real.exp_le_exp] at h
  linarith

lemma exists_minimizer [ProperSpace E] {f : E → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hu : UpperSemicontinuous f)
    (hne : ∃ x, 0 < f x) {a b t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hb : ∀ y, f y ≤ Real.exp (b - a * ‖y‖)) (x : E) :
    ∃ p, 0 < f p ∧ ∀ y, 0 < f y → objective f t x p ≤ objective f t x y := by
  obtain ⟨p, hp, hpm⟩ := exists_weight_max hf hu hne ha ht hb x
  exact ⟨p, hp, fun y hy => objective_le_of_weight_le hp hy (hpm y)⟩

lemma objective_lower_bound {f : E → ℝ} {a b t : ℝ} (ha : 0 < a) (ht : 1 ≤ t)
    (hb : ∀ y, f y ≤ Real.exp (b - a * ‖y‖)) (x y : E) (hy : 0 < f y) :
    a * ‖x‖ - (b + a ^ 2 / 2) ≤ objective f t x y := by
  have hl := (Real.log_le_iff_le_exp hy).2 (hb y)
  have hn : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    simpa only [add_sub_cancel] using norm_add_le y (x - y)
  have hn' := mul_le_mul_of_nonneg_left hn ha.le
  dsimp [objective]
  nlinarith [sq_nonneg (‖x - y‖ - a), mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg ‖x - y‖)]

end Submission.Obl.Entropy__moreau_envelope_sequence
