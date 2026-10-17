import Submission.Obl.Entropy__transport_integrated_multiplier.WeakTest
import Submission.Obl.Entropy__transport_integrated_multiplier.MatrixLp
import Submission.Obl.Entropy__transport_integrated_multiplier.MatrixCalc

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators ENNReal

namespace Submission.Obl.Entropy__transport_integrated_multiplier

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] [Fintype ι] [DecidableEq ι]

/-- The bounded matrix multiplier estimate, with curvature and derivative data separated. -/
theorem abstract_multiplier_bound
    (v : ι → E) (Q W T M : E → Matrix ι ι ℝ) (H K : ι → E → Matrix ι ι ℝ)
    (hQsym : ∀ x, (Q x).IsHermitian) (hMsym : ∀ x, (M x).IsHermitian)
    (hHsym : ∀ r x, (H r x).IsHermitian) (hWpos : ∀ x, (W x).PosSemidef)
    (hQ : ∀ i j, ContDiff ℝ 1 (fun x => Q x i j))
    (hPbound : ∀ i j, ∃ C : ℝ, ∀ x, ‖(Q x * Q x) i j‖ ≤ C)
    (hQtop : EntryLp ∞ Q μ) (hMtop : EntryLp ∞ M μ) (hWtop : EntryLp ∞ W μ)
    (hT : EntryLp 1 T μ) (hH : ∀ r, EntryLp 2 (H r) μ)
    (hK : ∀ r, EntryLp 2 (K r) μ)
    (hKd : ∀ r x i j, K r x i j = fderiv ℝ (fun y => Q y i j) x (v r))
    (hweak : ∀ i j (z : E → ℝ), ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, z x * (-(if i = j then 1 else 0) + W x i j + T x i j) ∂μ) =
        -∑ r, ∑ s, ∫ x, fderiv ℝ z x (v s) * M x s r * H r x i j ∂μ) :
    (∫ x, (∑ i, ∑ j, (Q x * Q x) i j * T x i j) +
      ∑ r, ∑ s, M x r s * Matrix.trace ((K s x * Q x + Q x * K s x) * H r x) ∂μ) ≤
        ∫ x, ∑ i, ∑ j, (Q x i j)^2 ∂μ := by
  let P : E → Matrix ι ι ℝ := fun x => Q x * Q x
  let D : ι → E → Matrix ι ι ℝ := fun s x => K s x * Q x + Q x * K s x
  have hPtop : EntryLp ∞ P μ := hQtop.mul hQtop
  have hD (s : ι) : EntryLp 2 (D s) μ :=
    ((hK s).mul (r := 2) hQtop).add (hQtop.mul (r := 2) (hK s))
  have hPd (s : ι) (x : E) (i j : ι) :
      fderiv ℝ (fun y => P y i j) x (v s) = D s x i j := by
    have he : (Matrix.of fun a b => fderiv ℝ (fun y => Q y a b) x (v s)) = K s x := by
      ext a b
      exact (hKd s x a b).symm
    simpa only [he] using fderiv_matrix_square
      (fun i j => (hQ i j).differentiable (by simp)) x (v s) i j
  have hPT (i j : ι) : Integrable (fun x => P x i j * T x i j) μ :=
    memLp_one_iff_integrable.mp ((hT i j).mul' (hPtop i j))
  have hPW (i j : ι) : Integrable (fun x => P x i j * W x i j) μ :=
    (((hWtop i j).mul' (r := ∞) (hPtop i j))).integrable (by simp)
  have hPi (i j : ι) : Integrable (fun x => P x i j) μ := (hPtop i j).integrable (by simp)
  have hDMH (i j r s : ι) :
      Integrable (fun x => D s x i j * M x s r * H r x i j) μ := by
    have hDM : MemLp (fun x => D s x i j * M x s r) 2 μ :=
      (hMtop s r).mul' (hD s i j)
    exact hDM.integrable_mul (hH r i j)
  have hL (i j : ι) : Integrable
      (fun x => P x i j * (-(if i = j then 1 else 0) + W x i j + T x i j)) μ := by
    simpa only [Pi.add_def, mul_add] using ((hPi i j).mul_const (-(if i = j then 1 else 0))).add
      (hPW i j) |>.add (hPT i j)
  have hE (i j : ι) :
      (∫ x, P x i j * (-(if i = j then 1 else 0) + W x i j + T x i j) ∂μ) =
        -∑ r, ∑ s, ∫ x, D s x i j * M x s r * H r x i j ∂μ := by
    have hf : Integrable (fun x => -(if i = j then 1 else 0) + W x i j + T x i j) μ :=
      ((integrable_const _).add ((hWtop i j).integrable (by simp))).add (hT.integrable i j)
    have hb (a : ι × ι) : Integrable (fun x => M x a.2 a.1 * H a.1 x i j) μ :=
      ((hH a.1 i j).mul' (r := 2) (hMtop a.2 a.1)).integrable (by norm_num)
    have hd (a : ι × ι) : Integrable
        (fun x => fderiv ℝ (fun y => P y i j) x (v a.2) *
          (M x a.2 a.1 * H a.1 x i j)) μ := by
      simpa only [hPd, mul_assoc] using hDMH i j a.1 a.2
    have he := integral_mul_eq_neg_sum_of_weak (p := fun x => P x i j) (fun a : ι × ι => v a.2)
      hf hb (contDiff_matrix_square hQ i j) (hPbound i j) hd
      (fun z hz hzc => by simpa only [Fintype.sum_prod_type, mul_assoc] using hweak i j z hz hzc)
    simpa only [Fintype.sum_prod_type, hPd, mul_assoc] using he
  have hsum :
      (∫ x, ∑ i, ∑ j, P x i j * (-(if i = j then 1 else 0) + W x i j + T x i j) ∂μ) =
        -(∫ x, ∑ i, ∑ j, ∑ r, ∑ s, D s x i j * M x s r * H r x i j ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hL i j))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => hL _ j), hE]
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ (fun s _ => hDMH i j r s))))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun r _ =>
      integrable_finsetSum Finset.univ (fun s _ => hDMH _ j r s))),
      integral_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ (fun s _ => hDMH _ _ r s)),
      integral_finsetSum Finset.univ (fun s _ => hDMH _ _ _ s), Finset.sum_neg_distrib]
  let a : E → ℝ := fun x => ∑ i, ∑ j, P x i j * T x i j
  let b : E → ℝ := fun x => ∑ i, ∑ j, P x i j * W x i j
  let c : E → ℝ := fun x => ∑ i, ∑ j, ∑ r, ∑ s, D s x i j * M x s r * H r x i j
  let n : E → ℝ := fun x => ∑ i, ∑ j, (Q x i j)^2
  have ha : Integrable a μ := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hPT i j
  have hb : Integrable b μ := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hPW i j
  have hc : Integrable c μ := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun r _ =>
      integrable_finsetSum Finset.univ fun s _ => hDMH i j r s
  have hn : Integrable n μ := by
    have ht := (hPtop.trace).integrable (by simp : (1 : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞))
    simpa only [P, square_trace_entries (hQsym _)] using ht
  have hleft (x : E) :
      (∑ i, ∑ j, P x i j * (-(if i = j then 1 else 0) + W x i j + T x i j)) =
        -n x + b x + a x := by
    simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have hd : (∑ i, ∑ j, P x i j * (if i = j then 1 else 0)) = n x := by
      simp only [mul_ite, mul_one, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact square_trace_entries (hQsym x)
    rw [hd]
  have hright (x : E) : c x =
      ∑ r, ∑ s, M x r s * Matrix.trace (D s x * H r x) := by
    simp only [c, trace_mul_entries_right (hHsym _ _), Finset.mul_sum]
    calc
      _ = ∑ rs : ι × ι, ∑ ij : ι × ι,
          D rs.2 x ij.1 ij.2 * M x rs.2 rs.1 * H rs.1 x ij.1 ij.2 := by
        simpa only [Fintype.sum_prod_type] using
          (Finset.sum_comm (s := (Finset.univ : Finset (ι × ι)))
            (t := (Finset.univ : Finset (ι × ι)))
            (f := fun ij rs => D rs.2 x ij.1 ij.2 * M x rs.2 rs.1 * H rs.1 x ij.1 ij.2))
      _ = _ := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hm : M x s r = M x r s := (hMsym x).apply r s
        erw [hm]
        ring
  simp_rw [hleft] at hsum
  change (∫ x, (-n + b) x + a x ∂μ) = -(∫ x, c x ∂μ) at hsum
  rw [integral_add (hn.neg.add hb) ha] at hsum
  change (∫ x, -n x + b x ∂μ) + (∫ x, a x ∂μ) = -(∫ x, c x ∂μ) at hsum
  erw [integral_add hn.neg hb, integral_neg] at hsum
  have hnonneg : 0 ≤ ∫ x, b x ∂μ := integral_nonneg fun x =>
    square_curvature_nonneg (hQsym x) (hWpos x)
  have heq : (fun x => (∑ i, ∑ j, (Q x * Q x) i j * T x i j) +
      ∑ r, ∑ s, M x r s * Matrix.trace ((K s x * Q x + Q x * K s x) * H r x)) =
      fun x => a x + c x := by
    funext x
    rw [hright]
  rw [heq, integral_add ha hc]
  linarith

end Submission.Obl.Entropy__transport_integrated_multiplier
