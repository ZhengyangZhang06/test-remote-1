import Submission.Obl.Entropy__smooth_gaussian_transport.NormalizedSections

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

def smallSection {m : ℕ} (u : E m → ℝ) (e : E m) (δ ε : ℝ) : Set (E m) :=
  {z | u z ≤ ε * (δ + inner ℝ e z)}

theorem smallSection_eq_sublevel {m : ℕ} (u : E m → ℝ) (e : E m) (δ ε : ℝ) :
    smallSection u e δ ε = {z | u z - inner ℝ (ε • e) z ≤ ε * δ} := by
  ext z
  simp only [smallSection, mem_ofPred_eq, real_inner_smul_left]
  constructor <;> intro h <;> nlinarith

theorem smallSection_isCompact {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (e : E m) (δ ε : ℝ) :
    IsCompact (smallSection u e δ ε) := by
  rw [smallSection_eq_sublevel]
  exact isCompact_tilted_sublevel_of_finite_conjugate hu hdom _ _

theorem smallSection_subset_fixed {m : ℕ} {u : E m → ℝ} (hnonneg : ∀ z, 0 ≤ u z)
    (e : E m) (δ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    smallSection u e δ ε ⊆ smallSection u e δ 1 := by
  intro z hz
  have hz' : u z ≤ ε * (δ + inner ℝ e z) := hz
  have hq : 0 ≤ δ + inner ℝ e z := by
    exact nonneg_of_mul_nonneg_right ((hnonneg z).trans hz') hε
  change u z ≤ 1 * (δ + inner ℝ e z)
  exact hz'.trans (mul_le_mul_of_nonneg_right hε1 hq)

/-- Small tilted sections remain uniformly close to a supporting half-space
of the zero set of a nonnegative coercive potential. -/
theorem smallSection_support_bound {m : ℕ} {u : E m → ℝ} (hu : Continuous u)
    (hdom : conjugateDomain u = univ) (hnonneg : ∀ z, 0 ≤ u z) (hzero : u 0 = 0)
    (e : E m) (hsupport : ∀ z, u z = 0 → inner ℝ e z ≤ 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ z ∈ smallSection u e δ ε, inner ℝ e z ≤ η := by
  let K := smallSection u e δ 1
  have hK : IsCompact K := smallSection_isCompact hu hdom e δ 1
  have h0 : (0 : E m) ∈ K := by
    change u 0 ≤ 1 * (δ + inner ℝ e 0)
    simpa only [hzero, inner_zero_right, add_zero, one_mul] using hδ.le
  have hq : Continuous (fun z : E m => inner ℝ e z) := continuous_const.inner continuous_id
  obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn ⟨0, h0⟩ hq.continuousOn
  let C := inner ℝ e zmax
  have hC : 0 ≤ C := by
    have h : inner ℝ e 0 ≤ C := hmax h0
    simpa only [inner_zero_right] using h
  have hδC : 0 < δ + C := add_pos_of_pos_of_nonneg hδ hC
  let A : Set (E m) := K ∩ {z | η ≤ inner ℝ e z}
  have hA : IsCompact A := hK.inter_right (isClosed_le continuous_const hq)
  by_cases hne : A.Nonempty
  · obtain ⟨zmin, hzmin, hmin⟩ := hA.exists_isMinOn hne hu.continuousOn
    have hminpos : 0 < u zmin := by
      have hn := hnonneg zmin
      by_contra hnot
      have heq : u zmin = 0 := le_antisymm (le_of_not_gt hnot) hn
      have hs := hsupport zmin heq
      have hz : η ≤ inner ℝ e zmin := hzmin.2
      linarith
    refine ⟨min 1 (u zmin / (δ + C)), lt_min zero_lt_one (div_pos hminpos hδC),
      min_le_left _ _, ?_⟩
    intro ε hε hεsmall z hz
    have hε1 : ε ≤ 1 := (hεsmall.trans_le (min_le_left _ _)).le
    have hzK : z ∈ K := smallSection_subset_fixed hnonneg e δ hε hε1 hz
    by_contra hn
    have hzA : z ∈ A := ⟨hzK, (lt_of_not_ge hn).le⟩
    have huLower : u zmin ≤ u z := hmin hzA
    have hqUpper : inner ℝ e z ≤ C := hmax hzK
    have huUpper : u z ≤ ε * (δ + inner ℝ e z) := hz
    have hprod : ε * (δ + C) < u zmin :=
      (lt_div_iff₀ hδC).mp (hεsmall.trans_le (min_le_right _ _))
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add_right hqUpper δ) hε.le]
  · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro ε hε hε1 z hz
    by_contra hn
    exact hne ⟨z, smallSection_subset_fixed hnonneg e δ hε hε1.le hz, (lt_of_not_ge hn).le⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
