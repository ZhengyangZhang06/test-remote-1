import Mathlib
import ChallengeDeps
import Submission.Lib.ConvexBody

open Set MeasureTheory
open scoped BigOperators Topology

namespace Submission.Obl.Cone__simplex_iff_product

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cone {n : ℕ} (K : Set (E n)) : Set (E (n + 1)) :=
  {z | 0 ≤ z 0 ∧ ∃ x ∈ K, ∀ i : Fin n, z i.succ = z 0 * x i}

noncomputable def lift {n : ℕ} (x : E n) : E (n + 1) :=
  WithLp.toLp 2 (Fin.cons 1 x)

@[simp] theorem lift_zero {n : ℕ} (x : E n) : lift x 0 = 1 := rfl
@[simp] theorem lift_succ {n : ℕ} (x : E n) (i : Fin n) : lift x i.succ = x i := rfl

theorem lift_mem_cone {n : ℕ} {K : Set (E n)} {x : E n} :
    lift x ∈ cone K ↔ x ∈ K := by
  constructor
  · rintro ⟨_, y, hy, he⟩
    have : x = y := by ext i; simpa using he i
    exact this ▸ hy
  · intro hx
    exact ⟨by simp, x, hx, by simp⟩

theorem zero_mem_cone {n : ℕ} {K : Set (E n)} (hK : K.Nonempty) :
    (0 : E (n + 1)) ∈ cone K := by
  obtain ⟨x, hx⟩ := hK
  exact ⟨by simp, x, hx, by simp⟩

theorem cone_smul {n : ℕ} {K : Set (E n)} {z : E (n + 1)}
    (hz : z ∈ cone K) {r : ℝ} (hr : 0 ≤ r) : r • z ∈ cone K := by
  rcases hz with ⟨ht, x, hx, he⟩
  refine ⟨mul_nonneg hr ht, x, hx, ?_⟩
  intro i
  change r * z i.succ = (r * z 0) * x i
  rw [he i, mul_assoc]

theorem cone_height_zero {n : ℕ} {K : Set (E n)} {z : E (n + 1)}
    (hz : z ∈ cone K) (ht : z 0 = 0) : z = 0 := by
  rcases hz with ⟨_, x, _, he⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ht
  · simpa [ht] using he j

theorem cone_add {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K)
    {z w : E (n + 1)} (hz : z ∈ cone K) (hw : w ∈ cone K) : z + w ∈ cone K := by
  by_cases ht : z 0 + w 0 = 0
  · have hz0 := cone_height_zero hz (by linarith [hz.1, hw.1])
    simpa [hz0] using hw
  rcases hz with ⟨hz, x, hx, he⟩
  rcases hw with ⟨hw, y, hy, hf⟩
  have hp : 0 < z 0 + w 0 := lt_of_le_of_ne (add_nonneg hz hw) (Ne.symm ht)
  refine ⟨add_nonneg hz hw, (z 0 / (z 0 + w 0)) • x + (w 0 / (z 0 + w 0)) • y,
    hK hx hy (div_nonneg hz hp.le) (div_nonneg hw hp.le) ?_, ?_⟩
  · rw [← add_div, div_self ht]
  · intro i
    change z i.succ + w i.succ =
      (z 0 + w 0) * ((z 0 / (z 0 + w 0)) * x i + (w 0 / (z 0 + w 0)) * y i)
    rw [he i, hf i]
    field_simp

theorem convex_cone {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K) : Convex ℝ (cone K) := by
  intro x hx y hy a b ha hb hab
  exact cone_add hK (cone_smul hx ha) (cone_smul hy hb)

theorem isClosed_cone {n : ℕ} {K : Set (E n)} (hK : IsCompact K) : IsClosed (cone K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (E (n + 1) × K) :=
    {p | 0 ≤ p.1 0 ∧ ∀ i : Fin n, p.1 i.succ = p.1 0 * (p.2 : E n) i}
  have hS : IsClosed S := by
    simp only [S, setOf_and, setOf_forall]
    apply IsClosed.inter (isClosed_le continuous_const (by fun_prop))
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) (by fun_prop)
  have he : Prod.fst '' S = cone K := by
    ext z
    constructor
    · rintro ⟨⟨w, x⟩, h, rfl⟩
      exact ⟨h.1, x, x.property, h.2⟩
    · rintro ⟨ht, x, hx, he⟩
      exact ⟨(z, ⟨x, hx⟩), ⟨ht, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace S hS

theorem cone_interior_nonempty {n : ℕ} {K : Set (E n)}
    (hK : (interior K).Nonempty) : (interior (cone K)).Nonempty := by
  obtain ⟨x, hx⟩ := hK
  let q : E (n + 1) → E n := fun z => WithLp.toLp 2 (fun i => z i.succ / z 0)
  have hq : ContinuousAt q (lift x) := by
    apply (PiLp.continuous_toLp 2 _).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    exact (by fun_prop : ContinuousAt (fun z : E (n + 1) => z i.succ) (lift x)).div
      (by fun_prop) (by simp)
  have hqx : q (lift x) = x := by ext i; simp [q]
  have hmem : ∀ᶠ z in 𝓝 (lift x), q z ∈ K := by
    apply hq.eventually
    rw [hqx]
    exact mem_interior_iff_mem_nhds.mp hx
  have hpos : ∀ᶠ z : E (n + 1) in 𝓝 (lift x), 0 < z 0 :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun z : E (n + 1) => z 0))).mem_nhds (by simp)
  refine ⟨lift x, mem_interior_iff_mem_nhds.mpr ?_⟩
  filter_upwards [hmem, hpos] with z hz ht
  refine ⟨ht.le, q z, hz, ?_⟩
  intro i
  change z i.succ = z 0 * (z i.succ / z 0)
  field_simp

theorem cone_regular {n : ℕ} {K : Set (E n)} (hK : SimplexIsotropic.IsConvexBody K) :
    closure (interior (cone K)) = cone K := by
  rw [(convex_cone hK.convex).closure_interior_eq_closure_of_nonempty_interior
    (cone_interior_nonempty hK.interior_nonempty), (isClosed_cone hK.isCompact).closure_eq]

/-- Closed sets which are closures of their interiors are determined by their Lebesgue class. -/
theorem regular_set_eq_of_ae {m : ℕ} {S T : Set (E m)}
    (hS : IsClosed S) (hT : IsClosed T)
    (hrS : closure (interior S) = S) (hrT : closure (interior T) = T)
    (he : ∀ᵐ x ∂volume, x ∈ S ↔ x ∈ T) : S = T := by
  have hST : ∀ {A B : Set (E m)}, IsClosed B → closure (interior A) = A →
      (∀ᵐ x ∂volume, x ∈ A → x ∈ B) → A ⊆ B := by
    intro A B hB hr h
    have hi : interior A ⊆ B := by
      have hd := (Measure.dense_of_ae h).open_subset_closure_inter (isOpen_interior (s := A))
      exact hd.trans (closure_minimal (fun x hx => hx.2 (interior_subset hx.1)) hB)
    rw [← hr]
    exact closure_minimal hi hB
  exact subset_antisymm (hST hT hrS (he.mono fun _ h => h.mp))
    (hST hS hrT (he.mono fun _ h => h.mpr))

end Submission.Obl.Cone__simplex_iff_product
