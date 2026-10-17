import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.Algebra
import Submission.Obl.Entropy__two_eigenvalue_secant_deduction.MeanDistance

open Set MeasureTheory
open scoped ContDiff

namespace Submission.Obl.Entropy__two_eigenvalue_secant_deduction
open Submission.Lib.GaussianTransport Submission.Lib.PairEstimate

noncomputable def baseX (j : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![Real.sqrt (82/37), 0, 0,
    ((82/37)*b j-eta/2)/Real.sqrt (ell j), -eta/Real.sqrt (3/4)]
noncomputable def baseY (j : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![0, Real.sqrt (40/3), 0, L j/Real.sqrt (ell j), 0]
noncomputable def baseW (j : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![0, 0, Real.sqrt (D j),
    D j*E j/Real.sqrt (ell j), D j*(3/2)*b j/Real.sqrt (3/4)]
noncomputable def incVec (j x y w : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  x • baseX j + y • baseY j + w • baseW j

lemma incVec_add (j x y w x' y' w' : ℝ) :
    incVec j (x+x') (y+y') (w+w') = incVec j x y w + incVec j x' y' w' := by
  unfold incVec; module
lemma incVec_sub (j x y w x' y' w' : ℝ) :
    incVec j (x-x') (y-y') (w-w') = incVec j x y w - incVec j x' y' w' := by
  unfold incVec; module
lemma incVec_smul (j r x y w : ℝ) :
    incVec j (r*x) (r*y) (r*w) = r • incVec j x y w := by
  unfold incVec; module

lemma norm_incVec_sq (j x y w : ℝ) (hp : 0 < p j) :
    ‖incVec j x y w‖^2 = incrementCost (b j) (l j) (e j) (p j) (ell j) x y w := by
  have hd : 0 ≤ D j := div_nonneg (by norm_num) hp.le
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [incVec, baseX, baseY, baseW, Fin.sum_univ_succ, mul_pow, add_div,
    div_pow, Real.sq_sqrt hd, Real.sq_sqrt (ell_pos j).le,
    incrementCost, D, E, L, eta]
  <;> ring_nf
  simp only [inv_pow, Real.sq_sqrt (ell_pos j).le,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),
    Real.sq_sqrt (by positivity : 0 ≤ (p j)⁻¹*(5/17))]
  ring

noncomputable def W (j a : ℝ) := hstar a - 2*b j - 2*L j*z a
noncomputable def V (j a : ℝ) := incVec j (chi a) (chi a*z a) (chi a*W j a)
noncomputable def J (j a : ℝ) :=
  incVec j (b a) (l a) (deriv f a-2*b j*b a-(80/3)*l j*l a)
noncomputable def Fcost (j a : ℝ) :=
  incrementCost (b j) (l j) (e j) (p j) (ell j) (chi a) (chi a*z a) (chi a*W j a)

lemma norm_V_sq (j a : ℝ) (hp : 0 < p j) : ‖V j a‖^2 = Fcost j a :=
  norm_incVec_sq j _ _ _ hp

lemma hasDerivAt_incVec {x y w : ℝ → ℝ} {x' y' w' a : ℝ} (j : ℝ)
    (hx : HasDerivAt x x' a) (hy : HasDerivAt y y' a) (hw : HasDerivAt w w' a) :
    HasDerivAt (fun a => incVec j (x a) (y a) (w a)) (incVec j x' y' w') a := by
  exact ((hx.smul_const (baseX j)).add (hy.smul_const (baseY j))).add
    (hw.smul_const (baseW j))

lemma hasDerivAt_J (j a : ℝ) (hl : l a ≠ 0) :
    HasDerivAt (J j) (gaussianGap a • V j a) a := by
  have hd := hasDerivAt_incVec j (hasDerivAt_b a)
    ((smooth_l.differentiable (by simp) a).hasDerivAt)
    (((((contDiff_infty_iff_deriv.mp smooth_f).2.differentiable (by simp) a).hasDerivAt).sub
      ((hasDerivAt_b a).const_mul (2*b j))).sub
      (((smooth_l.differentiable (by simp) a).hasDerivAt).const_mul ((80/3)*l j)))
  change HasDerivAt (J j) _ a at hd
  have hg : gaussianHazard a-a ≠ 0 := (gaussianGap_pos a).ne'
  convert! hd using 1
  rw [V, ← incVec_smul, deriv2_f a hl]
  congr 1
  · unfold chi gaussianGap
    field_simp [hg]
  · unfold chi z gaussianGap
    field_simp [hg]
  · unfold chi W hstar z L gaussianGap
    field_simp [hg]
    <;> ring

lemma continuous_J (j : ℝ) : Continuous (J j) := by
  unfold J incVec
  have hf := (contDiff_infty_iff_deriv.mp smooth_f).2.continuous
  have hb := smooth_b.continuous
  have hl := smooth_l.continuous
  fun_prop

/-- A pointwise derivative-cost bound controls each partial interval. -/
lemma J_sub_le_open {j a c P : ℝ} (hac : a ≤ c) (hP : 0 ≤ P) (hp : 0 < p j)
    (hl : ∀ x ∈ Ioo a c, 0 < l x)
    (hF : ∀ x ∈ Ioo a c, Fcost j x ≤ P) :
    ‖J j c-J j a‖ ≤ Real.sqrt P * (logq c-logq a) := by
  have hder (x : ℝ) (hx : x ∈ Ioo a c) :
      ‖deriv (J j) x‖ ≤ Real.sqrt P * gaussianGap x := by
    rw [(hasDerivAt_J j x (hl x hx).ne').deriv, norm_smul,
      Real.norm_of_nonneg (gaussianGap_pos x).le]
    have hv : ‖V j x‖ ≤ Real.sqrt P := by
      apply (Real.le_sqrt (norm_nonneg _) hP).2
      rw [norm_V_sq j x hp]
      exact hF x hx
    nlinarith [mul_le_mul_of_nonneg_left hv (gaussianGap_pos x).le]
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (B := fun x => Real.sqrt P*gaussianGap x) hac
    (continuous_J j).continuousOn
    (fun x hx => (hasDerivAt_J j x (hl x hx).ne').differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun x hx => hder x hx)
    ((continuous_const.mul (contDiff_gaussianHazard.continuous.sub continuous_id)).intervalIntegrable a c)
  have he : (∫ x in a..c, Real.sqrt P*gaussianGap x) =
      Real.sqrt P*(logq c-logq a) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_logq x)
        ((contDiff_gaussianHazard.continuous.sub continuous_id).intervalIntegrable a c)]
  exact h.trans_eq he

lemma J_sub_le {j a c P : ℝ} (hac : a ≤ c) (hP : 0 ≤ P) (hp : 0 < p j)
    (hl : ∀ x ∈ Icc a c, 0 < l x)
    (hF : ∀ x ∈ Icc a c, Fcost j x ≤ P) :
    ‖J j c-J j a‖ ≤ Real.sqrt P * (logq c-logq a) :=
  J_sub_le_open hac hP hp (fun x hx => hl x ⟨hx.1.le,hx.2.le⟩)
    (fun x hx => hF x ⟨hx.1.le,hx.2.le⟩)

end Submission.Obl.Entropy__two_eigenvalue_secant_deduction
