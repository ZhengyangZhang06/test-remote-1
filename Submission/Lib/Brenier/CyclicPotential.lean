/-
Adapted from: here:root
Original workspace contribution: x0118 CyclicPotential, source b85d115.
The aggregate combines these three root sessions' original proofs.
-/

import Mathlib

/-! The convex-potential construction for cyclically monotone relations. -/

open Set

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.Brenier.CyclicPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Set (E × E)}

/-- The affine value at the end of an anchored finite path in a relation. -/
noncomputable def chainValue : Γ → List Γ → E → ℝ
  | p, [], x => inner ℝ p.val.2 (x - p.val.1)
  | p, q :: L, x => inner ℝ p.val.2 (q.val.1 - p.val.1) + chainValue q L x

/-- Cyclical monotonicity, written as nonpositivity of the work around every
finite closed path. -/
def IsCyclicallyMonotone (Γ : Set (E × E)) : Prop :=
  ∀ p : Γ, ∀ L : List Γ, chainValue p L p.val.1 ≤ 0

theorem chainValue_append (p q : Γ) (L : List Γ) (x : E) :
    chainValue p (L ++ [q]) x = chainValue p L q.val.1 + inner ℝ q.val.2 (x - q.val.1) := by
  induction L generalizing p with
  | nil => rfl
  | cons r L ih => simp only [List.cons_append, chainValue, ih, add_assoc]

theorem chainValue_affine (p : Γ) (L : List Γ) (x y : E) (a b : ℝ) (hab : a+b=1) :
    chainValue p L (a • x + b • y) = a * chainValue p L x + b * chainValue p L y := by
  induction L generalizing p with
  | nil =>
    simp only [chainValue, inner_sub_right, inner_add_right, inner_smul_right]
    linear_combination (inner ℝ p.val.2 p.val.1) * hab
  | cons q L ih =>
    simp only [chainValue, ih]
    linear_combination -(inner ℝ p.val.2 (q.val.1 - p.val.1)) * hab

/-- The points where the path supremum is finite. -/
def chainDomain (p : Γ) : Set E :=
  {x | BddAbove (range (fun L : List Γ => chainValue p L x))}

theorem chainDomain_convex (p : Γ) : Convex ℝ (chainDomain p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨My, hMy⟩ := hy
  refine ⟨a*Mx+b*My, ?_⟩
  rintro z ⟨L, rfl⟩
  dsimp only
  rw [chainValue_affine p L x y a b hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (hMx (mem_range_self L)) ha)
    (mul_le_mul_of_nonneg_left (hMy (mem_range_self L)) hb)

/-- Closing a path through a point of the relation bounds its value there. -/
theorem chainValue_le_at_source (hΓ : IsCyclicallyMonotone Γ) (p q : Γ) (L : List Γ) :
    chainValue p L q.val.1 ≤ inner ℝ q.val.2 (q.val.1-p.val.1) := by
  have h := hΓ p (L ++ [q])
  rw [chainValue_append] at h
  simp only [inner_sub_right] at h ⊢
  linarith

theorem source_mem_chainDomain (hΓ : IsCyclicallyMonotone Γ) (p q : Γ) :
    q.val.1 ∈ chainDomain p := by
  refine ⟨inner ℝ q.val.2 (q.val.1-p.val.1), ?_⟩
  rintro z ⟨L, rfl⟩
  exact chainValue_le_at_source hΓ p q L

section FiniteDimension

variable [FiniteDimensional ℝ E]

/-- In finite dimension a convex dense set is the whole space. -/
theorem convex_dense_eq_univ {D : Set E} (hconv : Convex ℝ D) (hdense : Dense D) : D = univ := by
  have hspan : affineSpan ℝ D = ⊤ := by
    apply SetLike.ext'
    change ((affineSpan ℝ D : AffineSubspace ℝ E) : Set E) = univ
    have hd : Dense ((affineSpan ℝ D : AffineSubspace ℝ E) : Set E) :=
      hdense.mono (subset_affineSpan ℝ D)
    simpa only [(affineSpan ℝ D).closed_of_finiteDimensional.closure_eq]
      using hd.closure_eq
  have hi := hconv.interior_closure_eq_interior_of_nonempty_interior
    (hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan)
  rw [hdense.closure_eq, interior_univ] at hi
  apply univ_subset_iff.mp
  rw [hi]
  exact interior_subset

theorem chainDomain_eq_univ (hΓ : IsCyclicallyMonotone Γ)
    (hdense : Dense (Prod.fst '' Γ)) (p : Γ) : chainDomain p = univ := by
  apply convex_dense_eq_univ (chainDomain_convex p)
  apply hdense.mono
  rintro x ⟨q, hq, rfl⟩
  exact source_mem_chainDomain hΓ p ⟨q,hq⟩

/-- The finite path supremum is a real-valued potential. -/
noncomputable def potential (p : Γ) (x : E) : ℝ :=
  sSup (range (fun L : List Γ => chainValue p L x))

theorem potential_convex (hΓ : IsCyclicallyMonotone Γ)
    (hdense : Dense (Prod.fst '' Γ)) (p : Γ) : ConvexOn ℝ univ (potential p) := by
  have hdom (x : E) : BddAbove (range (fun L : List Γ => chainValue p L x)) := by
    change x ∈ chainDomain p
    rw [chainDomain_eq_univ hΓ hdense p]
    exact mem_univ x
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  apply csSup_le (range_nonempty _)
  rintro z ⟨L, rfl⟩
  dsimp only
  rw [chainValue_affine p L x y a b hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_csSup (hdom x) (mem_range_self L)) ha)
    (mul_le_mul_of_nonneg_left (le_csSup (hdom y) (mem_range_self L)) hb)

theorem potential_subgradient (hΓ : IsCyclicallyMonotone Γ)
    (hdense : Dense (Prod.fst '' Γ)) (p q : Γ) (x : E) :
    potential p q.val.1 + inner ℝ q.val.2 (x-q.val.1) ≤ potential p x := by
  have hdom (y : E) : BddAbove (range (fun L : List Γ => chainValue p L y)) := by
    change y ∈ chainDomain p
    rw [chainDomain_eq_univ hΓ hdense p]
    exact mem_univ y
  have hsup : potential p q.val.1 ≤ potential p x - inner ℝ q.val.2 (x-q.val.1) := by
    apply csSup_le (range_nonempty _)
    rintro z ⟨L, rfl⟩
    have h := le_csSup (hdom x) (mem_range_self (L ++ [q]))
    rw [chainValue_append] at h
    exact le_sub_iff_add_le.mpr h
  linarith

/-- Rockafellar's construction for a relation with dense source projection. -/
theorem exists_convex_potential (hΓ : IsCyclicallyMonotone Γ)
    (hdense : Dense (Prod.fst '' Γ)) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Continuous φ ∧
      ∀ p ∈ Γ, ∀ x : E, φ p.1 + inner ℝ p.2 (x-p.1) ≤ φ x := by
  obtain ⟨_, q, hq, _⟩ := hdense.nonempty
  let p : Γ := ⟨q,hq⟩
  have hc := potential_convex hΓ hdense p
  exact ⟨potential p, hc, hc.locallyLipschitz.continuous,
    fun q hq x => potential_subgradient hΓ hdense p ⟨q,hq⟩ x⟩

end FiniteDimension

/-- Supporting planes imply the finite cycle inequalities. -/
theorem cyclicallyMonotone_of_subgradient {φ : E → ℝ}
    (hφ : ∀ p ∈ Γ, ∀ x : E, φ p.1 + inner ℝ p.2 (x-p.1) ≤ φ x) :
    IsCyclicallyMonotone Γ := by
  have hpath (p : Γ) (L : List Γ) (x : E) : chainValue p L x ≤ φ x - φ p.val.1 := by
    induction L generalizing p with
    | nil => exact (le_sub_iff_add_le').mpr (hφ p.val p.property x)
    | cons q L ih =>
      have he := hφ p.val p.property q.val.1
      have ht := ih q
      simp only [chainValue]
      linarith
  intro p L
  simpa only [sub_self] using hpath p L p.val.1

end Submission.Lib.Brenier.CyclicPotential
