import Submission.Obl.Root.CouplingSupport
import Submission.Obl.Root.CyclicPotential
import Submission.Obl.Root.ConvexGradientLaw

/-!
# Convex-gradient transport existence

Combines optimal-plan compactness and cyclic-support optimality with x0118's
finite-path potential and x0014's almost-everywhere gradient-law results.
-/

open MeasureTheory Set
open scoped Topology BigOperators Classical

namespace Submission.Obl.Root.Brenier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open CyclicPotential OptimalCoupling

private lemma snoc_apply_succ {α : Type*} {n : ℕ} (f : Fin (n+1) → α)
    (a : α) (i : Fin (n+1)) :
    Fin.snoc (α := fun _ => α) f a i.succ =
      Fin.snoc (α := fun _ => α) (fun j => f j.succ) a i := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp [← Fin.castSucc_succ]

/-- Finite-path work is the sum over its consecutive edges. -/
lemma chainValue_ofFn {Γ : Set (E × E)} {n : ℕ}
    (p : Γ) (f : Fin n → Γ) (x : E) :
    chainValue p (List.ofFn f) x =
      ∑ i : Fin (n + 1), inner ℝ (Fin.cons (α := fun _ => Γ) p f i).val.2
        (Fin.snoc (α := fun _ => E) (fun j => (f j).val.1) x i -
          (Fin.cons (α := fun _ => Γ) p f i).val.1) := by
  induction n generalizing p with
  | zero => simp [chainValue, Fin.snoc_zero]
  | succ n ih =>
    rw [List.ofFn_succ, chainValue, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he := congrFun (Fin.cons_self_tail f) i
    change Fin.cons (α := fun _ => Γ) (f 0) (fun j => f j.succ) i = f i at he
    simp only [Fin.cons_succ, snoc_apply_succ, he]

/-- Closing the finite path gives the work of a cyclic permutation. -/
lemma chainValue_cycle {Γ : Set (E × E)} {n : ℕ}
    (p : Γ) (f : Fin n → Γ) :
    chainValue p (List.ofFn f) p.val.1 =
      ∑ i : Fin (n+1), inner ℝ (Fin.cons (α := fun _ => Γ) p f i).val.2
        ((Fin.cons (α := fun _ => Γ) p f (finRotate (n+1) i)).val.1 -
          (Fin.cons (α := fun _ => Γ) p f i).val.1) := by
  rw [chainValue_ofFn, Fin.snoc_eq_cons_rotate]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun (Fin.comp_cons (fun q : Γ => q.val.1) p f) (finRotate (n+1) i)
  exact congrArg (fun a => inner ℝ (Fin.cons (α := fun _ => Γ) p f i).val.2
    (a - (Fin.cons (α := fun _ => Γ) p f i).val.1)) he.symm

/-- The indexed-cycle and closed-list formulations agree in the direction
needed for the finite-path construction. -/
lemma cyclicallyMonotone_of_cycles {Γ : Set (E × E)}
    (hcycle : ∀ (n : ℕ) (z : Fin (n+1) → Γ),
      ∑ i, inner ℝ (z i).val.2 ((z (finRotate (n+1) i)).val.1 - (z i).val.1) ≤ 0) :
    IsCyclicallyMonotone Γ := by
  intro p L
  rw [← List.ofFn_get L, chainValue_cycle]
  exact hcycle L.length (Fin.cons (α := fun _ => Γ) p L.get)

section FiniteDimension

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Quadratic optimal couplings have cyclically monotone support in the
finite-path formulation. -/
theorem cyclicallyMonotone_support_of_optimal {μ ν : ProbabilityMeasure E}
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    {π : ProbabilityMeasure (E × E)} (hπ : π ∈ couplings μ ν)
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, ‖z.1 - z.2‖^2 ∂(π : Measure (E × E))) ≤
        ∫ z, ‖z.1 - z.2‖^2 ∂(ρ : Measure (E × E))) :
    IsCyclicallyMonotone (π : Measure (E × E)).support := by
  apply cyclicallyMonotone_of_cycles
  intro n z
  exact sum_inner_sub_le_zero_on_support hμ hν hπ hmin (finRotate (n+1))
    (fun i => (z i).val) (fun i => (z i).property)

/-- Brenier existence for a full-support absolutely continuous source and finite
second moments. The potential is finite and continuous on the whole space. -/
theorem convex_gradient_of_optimal_coupling {μ ν : ProbabilityMeasure E}
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    (habs : (μ : Measure E) ≪ volume)
    (hsupp : (μ : Measure E).support = univ)
    {π : ProbabilityMeasure (E × E)} (hπ : π ∈ couplings μ ν)
    (hmin : ∀ ρ ∈ couplings μ ν,
      (∫ z, ‖z.1 - z.2‖^2 ∂(π : Measure (E × E))) ≤
        ∫ z, ‖z.1 - z.2‖^2 ∂(ρ : Measure (E × E))) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Continuous φ ∧ Measurable (gradient φ) ∧
      (∀ p ∈ (π : Measure (E × E)).support, ∀ x,
        φ p.1 + inner ℝ p.2 (x - p.1) ≤ φ x) ∧
      (π : Measure (E × E)) = Measure.map (fun x => (x, gradient φ x)) (μ : Measure E) ∧
      Measure.map (gradient φ) (μ : Measure E) = (ν : Measure E) := by
  have hcyclic := cyclicallyMonotone_support_of_optimal hμ hν hπ hmin
  obtain ⟨φ, hconv, hcont, hsub⟩ :=
    exists_convex_potential hcyclic (dense_source_projection hπ hsupp)
  have hae : ∀ᵐ p ∂(π : Measure (E × E)), ∀ x,
      φ p.1 + inner ℝ p.2 (x - p.1) ≤ φ x := by
    filter_upwards [Measure.support_mem_ae (μ := (π : Measure (E × E)))] with z hz
    exact hsub z hz
  exact ⟨φ, hconv, hcont, ConvexGradientLaw.measurable_gradient φ, hsub,
    ConvexGradientLaw.coupling_eq_graph_map hconv habs (measurePreserving_fst hπ).map_eq hae,
    ConvexGradientLaw.gradient_map_of_subgradient_coupling hconv habs
      (measurePreserving_fst hπ).map_eq (measurePreserving_snd hπ).map_eq hae⟩

/-- A full-support absolutely continuous source admits a convex-gradient transport
to every law with finite second moment. -/
theorem exists_convex_gradient_transport (μ ν : ProbabilityMeasure E)
    (hμ : MemLp (id : E → E) 2 (μ : Measure E))
    (hν : MemLp (id : E → E) 2 (ν : Measure E))
    (habs : (μ : Measure E) ≪ volume)
    (hsupp : (μ : Measure E).support = univ) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Continuous φ ∧ Measurable (gradient φ) ∧
      Measure.map (gradient φ) (μ : Measure E) = (ν : Measure E) := by
  obtain ⟨π, hπ, _, hmin⟩ := exists_quadratic_optimal_coupling μ ν hμ hν
  obtain ⟨φ, hconv, hcont, hmeas, _, _, hlaw⟩ :=
    convex_gradient_of_optimal_coupling hμ hν habs hsupp hπ hmin
  exact ⟨φ, hconv, hcont, hmeas, hlaw⟩

end FiniteDimension

end Submission.Obl.Root.Brenier
