import Submission.Obl.Entropy__gaussian_exact_remainder_expansion.Data
import Submission.Obl.Entropy__centered_slack_transports.Fields
import Submission.Obl.Entropy__linear_transport_limit.Fields

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff ENNReal

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

variable {m : ℕ} {A : E m → Mat m}

lemma X_hermitian (hA : ∀ x, (A x).IsHermitian) (r : Fin m) : (X A r).IsHermitian :=
  Submission.Obl.Entropy__centered_slack_transports.coefficient_isHermitian A hA r

lemma d_hermitian {Q : E m → Mat m} (hQ : ∀ x, (Q x).IsHermitian)
    (r : Fin m) (x : E m) : (d Q r x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, d, Matrix.of_apply]
  have hh : (fun y => Q y j i) = (fun y => Q y i j) := by
    funext y
    have h := congrArg (fun M : Mat m => M i j) (hQ y).eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  rw [hh]

lemma B_posSemidef (hA : ∀ x, (A x).IsHermitian) : (B A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r _
  simpa only [(X_hermitian hA r).eq] using Matrix.posSemidef_conjTranspose_mul_self (X A r)

lemma resolvent_relations (hA : ∀ x, (A x).IsHermitian) :
    (S A).IsHermitian ∧ (T A).IsHermitian ∧
    S A*(B A-1) = -(40/3:ℝ) • T A ∧
    (B A-1)*S A*(B A-1) = (40/3:ℝ) • H A := by
  let C : Mat m := (37/40:ℝ) • 1+(3/40:ℝ) • B A
  have hC : C.PosDef :=
    (Matrix.PosDef.one.smul (by norm_num : (0:ℝ)<37/40)).add_posSemidef
      ((B_posSemidef hA).smul (by norm_num : (0:ℝ)≤3/40))
  have hS : (S A).IsHermitian := hC.inv.isHermitian
  have hT : (T A).IsHermitian := hS.sub Matrix.isHermitian_one
  have hleft : S A*C = 1 := Matrix.nonsing_inv_mul C (Matrix.isUnit_iff_isUnit_det C |>.mp hC.isUnit)
  have hright : C*S A = 1 := Matrix.mul_nonsing_inv C (Matrix.isUnit_iff_isUnit_det C |>.mp hC.isUnit)
  have hSC : S A*(B A-1) = -(40/3:ℝ) • T A := by
    have hh := congrArg ((40/3:ℝ) • ·) hleft
    dsimp only [C] at hh
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      smul_add, smul_smul] at hh
    norm_num at hh
    rw [Matrix.mul_sub, Matrix.mul_one]
    have hx : S A*B A = (40/3:ℝ) • 1-(37/3:ℝ) • S A := by
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)
    rw [hx]
    dsimp only [T]
    module
  have hCS : (B A-1)*S A = -(40/3:ℝ) • T A := by
    have hh := congrArg ((40/3:ℝ) • ·) hright
    dsimp only [C] at hh
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      smul_add, smul_smul] at hh
    norm_num at hh
    rw [Matrix.sub_mul, Matrix.one_mul]
    have hx : B A*S A = (40/3:ℝ) • 1-(37/3:ℝ) • S A := by
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)
    rw [hx]
    dsimp only [T]
    module
  refine ⟨hS,hT,hSC,?_⟩
  rw [hCS]
  simp only [H, Matrix.smul_mul, Matrix.neg_mul, smul_neg, neg_smul]

lemma FCRegular.lp (hr : FCRegular A) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (q : ℝ≥0∞) : MatrixLp (γ m) q (c A f) := by
  obtain ⟨hc,⟨R,hR0,hR⟩,hd⟩ := hr f hf
  exact MatrixLp.of_bound (fun i j => (hc i j).continuous) ⟨R,hR⟩

lemma FCRegular.A_lp (hr : FCRegular A) (hA : ∀ x, (A x).IsHermitian) :
    MatrixLp (γ m) 2 A := by
  have hh := hr.lp (f:=id) contDiff_id 2
  have he : c A id = A := funext fun x => cfc_id ℝ (A x) (hA x)
  rw [he] at hh
  exact hh

lemma FCRegular.Y_lp (hr : FCRegular A) (hA : ∀ x, (A x).IsHermitian) :
    MatrixLp (γ m) 2 (Y A) := by
  apply (hr.A_lp hA).sub
  intro i j
  exact Submission.Obl.Entropy__linear_transport_limit.memLp_linearField_entry (X A) i j

lemma FCRegular.K_lp (hr : FCRegular A) (r : Fin m) : MatrixLp (γ m) 2 (K A r) :=
  (hr k smooth_k).2.2 r

lemma FCRegular.D_lp (hr : FCRegular A) (r : Fin m) : MatrixLp (γ m) 2 (D A r) :=
  (hr.K_lp r).sub ((hr.lp smooth_b 2).const_mul (X A r))

lemma FCRegular.L_lp (hr : FCRegular A) (r : Fin m) : MatrixLp (γ m) 2 (L A r) :=
  ((hr b smooth_b).2.2 r).sub ((hr.lp smooth_l 2).const_mul (X A r))

lemma FCRegular.F_lp (hr : FCRegular A) (hA : ∀ x, (A x).IsHermitian) :
    MatrixLp (γ m) 2 (F A) :=
  ((hr.Y_lp hA).mul ((hr.lp smooth_b ⊤).sub (MatrixLp.const _))).add
    (MatrixLp.sum fun r => (hr.L_lp r).const_mul (X A r))

lemma FCRegular.u_lp (hr : FCRegular A) (hA : ∀ x, (A x).IsHermitian) :
    MatrixLp (γ m) 2 (u A) :=
  (hr.F_lp hA).add ((hr.lp smooth_l 2).const_mul (B A-1))

lemma FCRegular.v_lp (hr : FCRegular A) {g : Fin m → E m → Mat m}
    (hg : ∀ r, MatrixLp (γ m) 2 (g r)) (r : Fin m) : MatrixLp (γ m) 2 (v A g r) :=
  (hr.D_lp r).sub ((hg r).smul _)

lemma FCRegular.E2_lp (hr : FCRegular A) : MatrixLp (γ m) 1 (E2 A) := by
  have ht := (hr.lp (f:=t) Submission.Lib.GaussianTransport.contDiff_exponentialTransport 1).smul 2
  have hk : MatrixLp (γ m) 1 (fun x => c A k x*c A k x) :=
    (hr.lp smooth_k 2).mul (hr.lp smooth_k 2)
  have hsum : MatrixLp (γ m) 1 (fun x => ∑ r, K A r x*K A r x) :=
    MatrixLp.sum fun r => (hr.K_lp r).mul (hr.K_lp r)
  convert (ht.sub hk).sub hsum using 1
  funext x
  simp only [E2, two_smul]

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
