import Mathlib
import ChallengeDeps

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

/-- The entries of a matrix, with their Euclidean rather than operator norm. -/
def entries {m : ℕ} (A : Mat m) : EuclideanSpace ℝ (Fin m × Fin m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

@[simp] theorem entries_apply {m : ℕ} (A : Mat m) (i j : Fin m) :
    entries A (i, j) = A i j := rfl

@[simp] theorem entries_sub {m : ℕ} (A B : Mat m) :
    entries (A - B) = entries A - entries B := rfl

@[simp] theorem entries_zero {m : ℕ} : entries (0 : Mat m) = 0 := rfl

theorem norm_entries_sq {m : ℕ} (A : Mat m) :
    ‖entries A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem continuous_entries {m : ℕ} : Continuous (@entries m) :=
  (PiLp.continuous_toLp 2 _).comp (by fun_prop)

/-- The assumed functional-calculus estimate in Euclidean matrix coordinates. -/
theorem norm_entries_cfc_sub_le {m : ℕ} {q : ℝ → ℝ}
    (hq : ∀ U V : Mat m, U.IsHermitian → V.IsHermitian →
      (∑ i, ∑ j, (cfc q U i j - cfc q V i j) ^ 2) ≤
        ∑ i, ∑ j, (U i j - V i j) ^ 2)
    {U V : Mat m} (hU : U.IsHermitian) (hV : V.IsHermitian) :
    ‖entries (cfc q U) - entries (cfc q V)‖ ≤ ‖entries U - entries V‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [← entries_sub, norm_entries_sq, Matrix.sub_apply] using hq U V hU hV

/-- A linear symmetric matrix field. -/
def linearField {m : ℕ} (X : Fin m → Mat m) (x : E m) : Mat m :=
  ∑ r, x r • X r

@[simp] theorem linearField_apply {m : ℕ} (X : Fin m → Mat m) (x : E m)
    (i j : Fin m) : linearField X x i j = ∑ r, x r * X r i j := by
  simp [linearField, Matrix.sum_apply]

theorem linearField_hermitian {m : ℕ} {X : Fin m → Mat m}
    (hX : ∀ r, (X r).IsHermitian) (x : E m) : (linearField X x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [linearField_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simpa using congrArg (fun M : Mat m => M i j) (hX r).eq

theorem continuous_linearField {m : ℕ} (X : Fin m → Mat m) :
    Continuous (linearField X) := by
  unfold linearField
  fun_prop

theorem memLp_coord {m : ℕ} (r : Fin m) :
    MemLp (fun x : E m => x r) 2 (stdGaussian (E m)) := by
  exact (IsGaussian.memLp_two_id (μ := stdGaussian (E m))).continuousLinearMap_comp
    (EuclideanSpace.proj (𝕜 := ℝ) r)

theorem memLp_linearField_entry {m : ℕ} (X : Fin m → Mat m) (i j : Fin m) :
    MemLp (fun x : E m => linearField X x i j) 2 (stdGaussian (E m)) := by
  simp only [linearField_apply]
  exact memLp_finsetSum _ (fun r _ => (memLp_coord r).mul_const _)

theorem memLp_entries {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    {A : α → Mat m} (hA : ∀ i j, MemLp (fun x => A x i j) 2 μ) :
    MemLp (fun x => entries (A x)) 2 μ := by
  have h : MemLp (fun x (p : Fin m × Fin m) => A x p.1 p.2) 2 μ :=
    memLp_pi_iff.mpr (fun p => hA p.1 p.2)
  exact h.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m × Fin m => ℝ)).symm.toContinuousLinearMap

theorem memLp_linearField {m : ℕ} (X : Fin m → Mat m) :
    MemLp (fun x : E m => entries (linearField X x)) 2 (stdGaussian (E m)) :=
  memLp_entries (memLp_linearField_entry X)

/-- Coefficient convergence gives Gaussian mean-square convergence of the linear fields. -/
theorem linearField_entry_energy {m : ℕ} (X : Fin m → Mat m) (i j : Fin m) :
    (∫ x : E m, (linearField X x i j) ^ 2 ∂stdGaussian (E m)) ≤
      (∫ x : E m, ‖x‖ ^ 2 ∂stdGaussian (E m)) * ∑ r, (X r i j) ^ 2 := by
  calc
    _ ≤ ∫ x : E m, ‖x‖ ^ 2 * ∑ r, (X r i j) ^ 2 ∂stdGaussian (E m) := by
      apply integral_mono (memLp_linearField_entry X i j).integrable_sq
        ((IsGaussian.memLp_two_id.integrable_norm_pow (by decide : 2 ≠ 0)).mul_const _)
      intro x
      dsimp only [id]
      rw [linearField_apply, EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := integral_mul_const _ _

@[simp] theorem linearField_sub {m : ℕ} (X Y : Fin m → Mat m) (x : E m) :
    linearField (X - Y) x = linearField X x - linearField Y x := by
  ext i j
  simp [linearField_apply, mul_sub, Finset.sum_sub_distrib]

/-- The continuous linear map underlying a linear matrix field. -/
noncomputable def linearFieldCLM {m : ℕ} (X : Fin m → Mat m) :
    E m →L[ℝ] EuclideanSpace ℝ (Fin m × Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => entries (linearField X x)
      map_add' := by
        intro x y
        ext p
        simp [entries, linearField_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext p
        simp [entries, linearField_apply, Finset.mul_sum, mul_assoc] }

@[simp] theorem linearFieldCLM_apply {m : ℕ} (X : Fin m → Mat m) (x : E m) :
    linearFieldCLM X x = entries (linearField X x) := rfl

variable {m : ℕ} {q : ℝ → ℝ}
variable (hq : ∀ U V : Mat m, U.IsHermitian → V.IsHermitian →
  (∑ i, ∑ j, (cfc q U i j - cfc q V i j) ^ 2) ≤
    ∑ i, ∑ j, (U i j - V i j) ^ 2)

include hq

theorem lipschitz_cfc_linearField {X : Fin m → Mat m}
    (hX : ∀ r, (X r).IsHermitian) :
    LipschitzWith ‖linearFieldCLM X‖₊ (fun x => entries (cfc q (linearField X x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ dist (linearFieldCLM X x) (linearFieldCLM X y) := by
      simpa only [dist_eq_norm, linearFieldCLM_apply] using norm_entries_cfc_sub_le hq
        (linearField_hermitian hX x) (linearField_hermitian hX y)
    _ ≤ _ := (linearFieldCLM X).lipschitz.dist_le_mul x y

theorem norm_cfc_entries_le {U : Mat m} (hU : U.IsHermitian) :
    ‖entries (cfc q U)‖ ≤ ‖entries U‖ + ‖entries (cfc q (0 : Mat m))‖ := by
  have h := norm_entries_cfc_sub_le hq hU Matrix.isHermitian_zero
  simpa only [entries_zero, sub_zero] using
    (norm_le_norm_sub_add (entries (cfc q U)) (entries (cfc q (0 : Mat m)))).trans
      (add_le_add_left h _)

theorem memLp_cfc_entries {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {A : α → Mat m}
    (hA : ∀ x, (A x).IsHermitian) (hAmem : MemLp (fun x => entries (A x)) 2 μ)
    (hmeas : AEStronglyMeasurable (fun x => entries (cfc q (A x))) μ) :
    MemLp (fun x => entries (cfc q (A x))) 2 μ := by
  apply (hAmem.norm.add (memLp_const ‖entries (cfc q (0 : Mat m))‖)).mono hmeas
  filter_upwards with x
  simpa only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using
      norm_cfc_entries_le hq (hA x)

theorem memLp_cfc_linearField {X : Fin m → Mat m} (hX : ∀ r, (X r).IsHermitian) :
    MemLp (fun x : E m => entries (cfc q (linearField X x))) 2 (stdGaussian (E m)) :=
  memLp_cfc_entries hq (linearField_hermitian hX) (memLp_linearField X)
    (lipschitz_cfc_linearField hq hX).continuous.aestronglyMeasurable

omit hq in
theorem tendsto_linearField_entry_energy {Xseq : ℕ → Fin m → Mat m} {X : Fin m → Mat m}
    (hX : Tendsto Xseq atTop (𝓝 X)) (i j : Fin m) :
    Tendsto (fun n => ∫ x : E m, (linearField (Xseq n - X) x i j) ^ 2
      ∂stdGaussian (E m)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _))
    (fun n => linearField_entry_energy (Xseq n - X) i j)
  have hcoord : ∀ r, Tendsto (fun n => ((Xseq n r i j - X r i j) ^ 2)) atTop (𝓝 0) := by
    intro r
    have ht := ((hX.apply_nhds r).apply_nhds i).apply_nhds j
    simpa [Function.comp_def] using (ht.sub_const (X r i j)).pow 2
  simpa using (tendsto_finsetSum Finset.univ (fun r _ => hcoord r)).const_mul
    (∫ x : E m, ‖x‖ ^ 2 ∂stdGaussian (E m))

omit hq in
theorem tendsto_linearField_energy {Xseq : ℕ → Fin m → Mat m} {X : Fin m → Mat m}
    (hX : Tendsto Xseq atTop (𝓝 X)) :
    Tendsto (fun n => ∫ x : E m,
      ‖entries (linearField (Xseq n) x) - entries (linearField X x)‖ ^ 2
        ∂stdGaussian (E m)) atTop (𝓝 0) := by
  have hs : ∀ n, (∫ x : E m,
      ‖entries (linearField (Xseq n) x) - entries (linearField X x)‖ ^ 2
        ∂stdGaussian (E m)) =
      ∑ i, ∑ j, ∫ x : E m, (linearField (Xseq n - X) x i j) ^ 2
        ∂stdGaussian (E m) := by
    intro n
    simp only [← entries_sub, ← linearField_sub, norm_entries_sq]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => (memLp_linearField_entry _ i j).integrable_sq)
    · intro i _
      exact integrable_finsetSum _ (fun j _ => (memLp_linearField_entry _ i j).integrable_sq)
  simp_rw [hs]
  simpa using tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => tendsto_linearField_entry_energy hX i j))

end Submission.Obl.Entropy__linear_transport_limit
