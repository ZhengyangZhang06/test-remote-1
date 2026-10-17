import Submission.Lib.EntropyTools.Remainder

/-!
# Coercivity of the strict entropy remainder

Section 6 uses that a nonnegative eigenvalue tends to one when its rigidity
weight tends to zero. The quantitative estimates here also control escape
to infinity, including the special cutoff convention at zero.
-/

open Filter Topology
open Submission.Lib.EntropyTools

namespace Submission.Obl.Root

lemma rigidityCutoff_eq_of_le_four {a : ℝ} (ha : 0 ≤ a) (ha4 : a ≤ 4) :
    rigidityCutoff a = 13 / 100 := by
  unfold rigidityCutoff
  split_ifs with h
  · rfl
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 (lt_of_le_of_ne ha (Ne.symm h))
    have hs2 : Real.sqrt a ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
    apply min_eq_left
    apply (le_div_iff₀ (by positivity : 0 < 25 * Real.sqrt a)).2
    nlinarith

/-- On a fixed bounded interval the weight controls the squared distance to one. -/
lemma sq_sub_one_le_rigidityWeight {a : ℝ} (ha : 0 ≤ a) (ha4 : a ≤ 4) :
    (a - 1) ^ 2 / 1000 ≤ rigidityWeight a := by
  have hd : 0 < 37 + 3 * a := by positivity
  have hfirst : 3 * (a - 1) ^ 2 / 49 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) :=
    div_le_div_of_nonneg_left (by positivity) hd (by linarith)
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a))  := by
    exact le_add_of_nonneg_right (by positivity)
  rw [rigidityWeight, rigidityCutoff_eq_of_le_four ha ha4]
  have hprod := mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 3 / 20)
    (by positivity : 0 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a))
  have h := mul_le_mul_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 13 / 100)
  nlinarith [sq_nonneg (a - 1)]

/-- A quantitative coercive bound on the unbounded part of the domain. -/
lemma sqrt_le_rigidityWeight {a : ℝ} (ha : 2 ≤ a) :
    Real.sqrt a / 10000 ≤ rigidityWeight a := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hs1 : 1 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) ha0.le).2 (by nlinarith)
  have hs_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha0.le
  have hd : 0 < 37 + 3 * a := by positivity
  have hfirst : a / 100 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ a - 2 by linarith)]
  have hsecond : (3 : ℝ) / 20 ≤ 3 / 20 + (49 / 100) * (37 / (37 + 3 * a))  := by
    exact le_add_of_nonneg_right (by positivity)
  have hcutoff : 13 / (100 * Real.sqrt a) ≤ rigidityCutoff a := by
    rw [rigidityCutoff, if_neg ha0.ne']
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 100 * Real.sqrt a)).2
      nlinarith
    · apply (div_le_div_iff₀ (by positivity : 0 < 100 * Real.sqrt a)
        (by positivity : 0 < 25 * Real.sqrt a)).2
      nlinarith
  have hprod := mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 3 / 20)
    (by positivity : 0 ≤ 3 * (a - 1) ^ 2 / (37 + 3 * a))
  have h := mul_le_mul hprod hcutoff (by positivity : 0 ≤ 13 / (100 * Real.sqrt a))
    (by positivity : 0 ≤ (3 * (a - 1) ^ 2 / (37 + 3 * a)) *
      (3 / 20 + (49 / 100) * (37 / (37 + 3 * a))))
  change a / 100 * (3 / 20) * (13 / (100 * Real.sqrt a)) ≤ rigidityWeight a at h
  have heq : a / 100 * (3 / 20) * (13 / (100 * Real.sqrt a)) =
      (39 / 200000) * Real.sqrt a := by
    field_simp
    nlinarith
  rw [heq] at h
  nlinarith

/-- A small weight quantitatively forces an eigenvalue close to one. -/
lemma abs_sub_one_lt_of_rigidityWeight_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (h : rigidityWeight a < min (1 / 10000) (ε ^ 2 / 1000)) :
    |a - 1| < ε := by
  have ha2 : a < 2 := by
    by_contra! h2
    have hs1 : 1 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) ha).2 (by linarith)
    have ht := sqrt_le_rigidityWeight h2
    have hw := lt_of_lt_of_le h (min_le_left _ _)
    linarith
  have hb := sq_sub_one_le_rigidityWeight ha (by linarith)
  have hw := lt_of_lt_of_le h (min_le_right _ _)
  nlinarith [sq_abs (a - 1), abs_nonneg (a - 1)]

/-- Vanishing weights force convergence to the unique zero, without any prior boundedness. -/
theorem tendsto_one_of_rigidityWeight_tendsto_zero {α : Type*} {l : Filter α}
    {a : α → ℝ} (ha : ∀ᶠ j in l, 0 ≤ a j)
    (hw : Tendsto (fun j => rigidityWeight (a j)) l (𝓝 0)) :
    Tendsto a l (𝓝 1) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hsmall : 0 < min ((1 : ℝ) / 10000) (ε ^ 2 / 1000) := by positivity
  filter_upwards [ha, hw.eventually (gt_mem_nhds hsmall)] with j hj hjw
  simpa only [Real.dist_eq] using abs_sub_one_lt_of_rigidityWeight_lt hj hε hjw

/-- Every eigenvalue converges to one if the sum of its nonnegative weights vanishes. -/
theorem eigenvalues_tendsto_one_of_weight_sum {α ι : Type*} [Fintype ι]
    {l : Filter α} {a : α → ι → ℝ} (ha : ∀ᶠ j in l, ∀ i, 0 ≤ a j i)
    (hw : Tendsto (fun j => ∑ i, rigidityWeight (a j i)) l (𝓝 0)) (i : ι) :
    Tendsto (fun j => a j i) l (𝓝 1) := by
  classical
  apply tendsto_one_of_rigidityWeight_tendsto_zero (ha.mono fun j hj => hj i)
  apply squeeze_zero' (ha.mono fun j hj => rigidityWeight_nonneg (hj i))
    (ha.mono fun j hj => ?_) hw
  exact Finset.single_le_sum (fun k _ => rigidityWeight_nonneg (hj k)) (Finset.mem_univ i)

/-- The nonlinear energy in the strict estimate vanishes when the entropy gap vanishes. -/
theorem nonlinear_energy_tendsto_zero {α ι : Type*} [Fintype ι]
    {l : Filter α} {a : α → ι → ℝ} {energy gap : α → ℝ}
    (ha : ∀ᶠ j in l, ∀ i, 0 ≤ a j i)
    (he : ∀ᶠ j in l, 0 ≤ energy j)
    (hbound : ∀ᶠ j in l, energy j / 500 +
      (∑ i, rigidityWeight (a j i)) / 1000 ≤ 2 * gap j)
    (hgap : Tendsto gap l (𝓝 0)) : Tendsto energy l (𝓝 0) := by
  apply squeeze_zero' he _ (show Tendsto (fun j => 1000 * gap j) l (𝓝 0) by
    simpa using hgap.const_mul 1000)
  filter_upwards [ha, hbound] with j hj hb
  have hs : 0 ≤ ∑ i, rigidityWeight (a j i) :=
    Finset.sum_nonneg fun i _ => rigidityWeight_nonneg (hj i)
  linarith

/-- The spectral part of the strict estimate vanishes along a sequence of vanishing gaps. -/
theorem weight_sum_tendsto_zero {α ι : Type*} [Fintype ι]
    {l : Filter α} {a : α → ι → ℝ} {energy gap : α → ℝ}
    (ha : ∀ᶠ j in l, ∀ i, 0 ≤ a j i)
    (he : ∀ᶠ j in l, 0 ≤ energy j)
    (hbound : ∀ᶠ j in l, energy j / 500 +
      (∑ i, rigidityWeight (a j i)) / 1000 ≤ 2 * gap j)
    (hgap : Tendsto gap l (𝓝 0)) :
    Tendsto (fun j => ∑ i, rigidityWeight (a j i)) l (𝓝 0) := by
  apply squeeze_zero' (ha.mono fun j hj => Finset.sum_nonneg fun i _ =>
    rigidityWeight_nonneg (hj i)) _
    (show Tendsto (fun j => 2000 * gap j) l (𝓝 0) by simpa using hgap.const_mul 2000)
  filter_upwards [he, hbound] with j hj hb
  linarith

end Submission.Obl.Root
