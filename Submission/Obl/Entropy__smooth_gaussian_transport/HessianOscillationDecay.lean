import Submission.Obl.Entropy__smooth_gaussian_transport.BrenierOscillationStep
import Submission.Obl.Entropy__smooth_gaussian_transport.GeometricOscillation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- Iterating the oscillation step gives geometrically shrinking essential
intervals for the directional Hessians, uniformly over interior centers. -/
theorem brenier_hessian_oscillation_decay {m : ℕ} (hm : 1 ≤ m)
    {V φ : E m → ℝ} {a : ℝ} (hV : ContDiff ℝ 2 V) (ha : 0 < a)
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {K : Set (E m)} (hK : IsCompact K) :
    ∃ F : Finset (E m), F.Nonempty ∧ (∀ v ∈ F, ‖v‖ = 1) ∧
      ∃ β M A : ℝ, 0 < β ∧ β < 1 ∧ 0 < M ∧ 0 < A ∧
        (∀ᵐ x ∂volume, ∀ᵐ y ∂volume, x ∈ K → y ∈ K →
          ‖fderiv ℝ (gradient φ) y - fderiv ℝ (gradient φ) x‖ ≤
            A * ((∑ v ∈ F, max 0
              (inner ℝ ((fderiv ℝ (gradient φ) y) v) v -
                inner ℝ ((fderiv ℝ (gradient φ) x) v) v)) + ‖y - x‖)) ∧
        ∀ c : E m, Metric.closedBall c 1 ⊆ K →
          ∃ l U : ℕ → E m → ℝ,
            (∀ n, ∀ v ∈ F, l n v ≤ U n v) ∧
            (∀ n, ∀ᵐ x ∂volume, x ∈ Metric.ball c (((m : ℝ) + 6)⁻¹ ^ n) →
              ∀ v ∈ F, l n v ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
                inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ U n v) ∧
            ∀ n, (∑ v ∈ F, (U n v - l n v)) ≤ M * β ^ n := by
  classical
  obtain ⟨F, hF, hFunit, θ, B, A, hθ, hθ1, hB, hA, hcomparison, hstep⟩ :=
    brenier_hessian_oscillation_step hm hV ha hH hφ hlaw hK
  let q : ℝ := ((m : ℝ) + 6)⁻¹
  have hden : 0 < (m : ℝ) + 6 := by positivity
  have hden1 : 1 < (m : ℝ) + 6 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hq : 0 < q := inv_pos.mpr hden
  have hq1 : q < 1 := by exact (inv_lt_one₀ hden).mpr hden1
  have hqpow (n : ℕ) : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1.le
  have hradius (n : ℕ) : q ^ (n + 1) * ((m : ℝ) + 6) = q ^ n := by
    rw [pow_succ, mul_assoc]
    dsimp [q]
    rw [inv_mul_cancel₀ hden.ne', mul_one]
  let L : ℝ := 10 * (1 / Real.sqrt a)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLip := brenier_gradient_lipschitz hm hV ha hH hφ hlaw
  have hnorm (x : E m) : ‖fderiv ℝ (gradient φ) x‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hLip
  have hbase : ∀ᵐ x ∂volume, ∀ v ∈ F,
      0 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
        inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ L := by
    filter_upwards [brenier_ae_hessian_structure hm hV.continuous hφ hlaw] with x hx
    intro v hv
    refine ⟨hx.2.2.1 v, ?_⟩
    calc
      _ ≤ ‖(fderiv ℝ (gradient φ) x) v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ (gradient φ) x‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (gradient φ) x).le_opNorm v) (norm_nonneg v)
      _ = ‖fderiv ℝ (gradient φ) x‖ := by rw [hFunit v hv]; ring
      _ ≤ L := hnorm x
  obtain ⟨β, M, hβ, hβ1, hM, hbound⟩ := geometric_recursion_bound hθ.le hθ1 hq.le hq1
    hB.le (show 0 ≤ (F.card : ℝ) * L by positivity)
  refine ⟨F, hF, hFunit, β, M, A, hβ, hβ1, hM, hA, hcomparison, ?_⟩
  intro c hcK
  let Valid (n : ℕ) (p : (E m → ℝ) × (E m → ℝ)) : Prop :=
    (∀ v ∈ F, p.1 v ≤ p.2 v) ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball c (q ^ n) → ∀ v ∈ F,
        p.1 v ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
          inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ p.2 v
  let State (n : ℕ) := {p : (E m → ℝ) × (E m → ℝ) // Valid n p}
  have hinit : Valid 0 ((fun _ => 0), fun _ => L) := by
    refine ⟨fun _ _ => hL.le, ?_⟩
    filter_upwards [hbase] with x hx
    exact fun _ => hx
  let init : State 0 := ⟨((fun _ => 0), fun _ => L), hinit⟩
  have hnext (n : ℕ) (p : State n) : ∃ p' : State (n + 1),
      (∑ v ∈ F, (p'.1.2 v - p'.1.1 v)) ≤
        θ * (∑ v ∈ F, (p.1.2 v - p.1.1 v)) + B * q ^ (n + 1) := by
    have hinside : Metric.closedBall c (q ^ (n + 1) * (m + 6)) ⊆ K := by
      rw [hradius]
      exact (Metric.closedBall_subset_closedBall (hqpow n)).trans hcK
    have hp : ∀ᵐ x ∂volume, x ∈ Metric.ball c (q ^ (n + 1) * (m + 6)) → ∀ v ∈ F,
        p.1.1 v ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v ∧
          inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ p.1.2 v := by
      rw [hradius]
      exact p.2.2
    obtain ⟨l', U', hnested, hnew, hwidth⟩ := hstep c (q ^ (n + 1))
      (pow_pos hq _) (hqpow _) hinside p.1.1 p.1.2 p.2.1 hp
    refine ⟨⟨(l', U'), ?_⟩, hwidth⟩
    exact ⟨fun v hv => (hnested v hv).2.1, hnew⟩
  choose next hnext using hnext
  let p : (n : ℕ) → State n := fun n => Nat.rec (motive := fun n => State n) init
    (fun n s => next n s) n
  let l : ℕ → E m → ℝ := fun n => (p n).1.1
  let U : ℕ → E m → ℝ := fun n => (p n).1.2
  refine ⟨l, U, fun n => (p n).2.1, fun n => (p n).2.2, ?_⟩
  apply hbound (fun n => ∑ v ∈ F, (U n v - l n v))
  · simp only [U, l, p, init, Nat.rec_zero, sub_zero, Finset.sum_const, nsmul_eq_mul, le_refl]
  · intro n
    have hh := hnext n (p n)
    have he : (∑ v ∈ F, (U (n + 1) v - l (n + 1) v)) =
        ∑ v ∈ F, ((next n (p n)).1.2 v - (next n (p n)).1.1 v) := rfl
    rw [he]
    apply hh.trans
    have hpow : q ^ (n + 1) ≤ q ^ n := by
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_left hq1.le (pow_nonneg hq.le n)).trans_eq (mul_one _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hB.le)

end Submission.Obl.Entropy__smooth_gaussian_transport
