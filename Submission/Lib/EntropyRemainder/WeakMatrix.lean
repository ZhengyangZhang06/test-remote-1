/-
Adapted from: here:o006
Original proofs by session x0062.
-/

import Submission.Lib.EntropyRemainder.GaussianIBP
import Submission.Lib.EntropyRemainder.WeakDivergenceC1

/-! # Matrix weak Gaussian identities -/

set_option backward.isDefEq.respectTransparency false

namespace Submission.Lib.EntropyRemainder

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The classical coordinate adjoint gives the frozen weak matrix divergence. -/
theorem weakDivergence_of_contDiff {m : ℕ} {v : Fin m → E m → Mat m}
    (hv : ∀ r i j, ContDiff ℝ 1 (fun x => v r x i j)) :
    WeakDivergence (fun x => ∑ r, (x r • v r x - coordinateDerivative (v r) r x)) v := by
  intro i j z hz hzc
  have hz1 : ContDiff ℝ 1 z := hz.of_le (by simp)
  have hi (r : Fin m) : Integrable (fun x =>
      (x r * v r x i j - coordinateDerivative (v r) r x i j) * z x)
        (stdGaussian (E m)) := by
    apply Continuous.integrable_of_hasCompactSupport _ hzc.mul_left
    exact (((EuclideanSpace.proj r).continuous.mul (hv r i j).continuous).sub
      (((hv r i j).continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hz.continuous
  simp only [expectation, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  erw [integral_finsetSum _ (fun r _ => hi r)]
  apply Finset.sum_congr rfl
  intro r _
  exact (gaussian_coordinate_adjoint_compact r (hv r i j) hz1 hzc).symm

lemma squareIntegrable_const_mul {m : ℕ} (C : Mat m) {F : E m → Mat m}
    (hF : SquareIntegrable F) : SquareIntegrable (fun x => C * F x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun k _ => (hF k j).const_mul _

lemma coordinateDerivative_const_mul {m : ℕ} (C : Mat m) {F : E m → Mat m}
    (hF : ∀ i j, Differentiable ℝ (fun x => F x i j)) (r : Fin m) (x : E m) :
    coordinateDerivative (fun y => C * F y) r x = C * coordinateDerivative F r x := by
  ext i j
  have hd : HasFDerivAt (fun y => (C * F y) i j)
      (∑ k, C i k • fderiv ℝ (fun y => F y k j) x) x := by
    simpa only [Matrix.mul_apply] using!
      HasFDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
        ((hF k j x).hasFDerivAt).const_mul (C i k))
  change fderiv ℝ (fun y => (C * F y) i j) x _ = _
  rw [hd.fderiv]
  simp [Matrix.mul_apply, coordinateDerivative]

/-- Product-rule divergence for a constant matrix times a C1 matrix field. -/
theorem weakDivergence_const_mul {m : ℕ} (X : Fin m → Mat m) {b : E m → Mat m}
    (hb : ∀ i j, ContDiff ℝ 1 (fun x => b x i j)) :
    WeakDivergence
      (fun x => ∑ r, (x r • (X r * b x) - X r * coordinateDerivative b r x))
      (fun r x => X r * b x) := by
  have hsm : ∀ r i j, ContDiff ℝ 1 (fun x => (X r * b x) i j) := by
    intro r i j
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => contDiff_const.mul (hb k j)
  simpa only [coordinateDerivative_const_mul _ (fun i j => (hb i j).differentiable_one)]
    using weakDivergence_of_contDiff hsm

/-- Integrate a matrix product entry by entry; only L2 is needed. -/
lemma expectation_trace_mul {m : ℕ} {F H : E m → Mat m}
    (hF : SquareIntegrable F) (hH : SquareIntegrable H) :
    expectation (fun x => Matrix.trace (F x * H x)) =
      ∑ i, ∑ j, expectation (fun x => F x i j * H x j i) := by
  simp only [expectation, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  erw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hF i j).integrable_mul (hH j i)))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => (hF i j).integrable_mul (hH j i))

/-- The scalar H1 identity summed against all entries of a matrix test. -/
theorem WeakDivergence.trace_test {m : ℕ} {F H : E m → Mat m}
    {v : Fin m → E m → Mat m} (h : WeakDivergence F v)
    (hF : SquareIntegrable F) (hv : ∀ r, SquareIntegrable (v r))
    (hH : ∀ i j, ContDiff ℝ 1 (fun x => H x i j)) (hHL : SquareIntegrable H)
    (hHD : ∀ r, SquareIntegrable (coordinateDerivative H r)) :
    expectation (fun x => Matrix.trace (F x * H x)) =
      ∑ r, expectation (fun x => Matrix.trace (v r x * coordinateDerivative H r x)) := by
  rw [expectation_trace_mul hF hHL]
  simp_rw [expectation_trace_mul (hv _) (hHD _)]
  calc
    _ = ∑ i, ∑ j, ∑ r, expectation (fun x => v r x i j *
        coordinateDerivative H r x j i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact h.c1_test hF hv (hH j i) (hHL j i) (fun r => hHD r j i) i j
    _ = ∑ i, ∑ r, ∑ j, expectation (fun x => v r x i j *
        coordinateDerivative H r x j i) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Constant left weights commute with weak divergence. -/
theorem WeakDivergence.const_mul {m : ℕ} {F : E m → Mat m}
    {v : Fin m → E m → Mat m} (h : WeakDivergence F v)
    (hF : SquareIntegrable F) (hv : ∀ r, SquareIntegrable (v r)) (C : Mat m) :
    WeakDivergence (fun x => C * F x) (fun r x => C * v r x) := by
  intro i j z hz hzc
  have hzL : MemLp z 2 (stdGaussian (E m)) := hz.continuous.memLp_of_hasCompactSupport hzc
  have hzD (r : Fin m) : MemLp
      (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 (stdGaussian (E m)) :=
    ((hz.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hzc.fderiv_apply ℝ _)
  simp only [expectation, Matrix.mul_apply, Finset.sum_mul]
  erw [integral_finsetSum _ (fun k _ => ((hF k j).const_mul _).integrable_mul hzL)]
  simp only [Pi.mul_apply, mul_assoc, integral_const_mul]
  have he (k : Fin m) : (∫ x, F x k j * z x ∂stdGaussian (E m)) =
      ∑ r, expectation (fun x => v r x k j *
        fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) := h k j z hz hzc
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  erw [integral_finsetSum _ (fun k _ => ((hv r k j).integrable_mul (hzD r)).const_mul (C i k))]
  simp only [Pi.mul_apply, integral_const_mul, expectation]

/-- The weighted trace identity does not require commuting matrices. -/
theorem WeakDivergence.weighted_trace_test {m : ℕ} {F H : E m → Mat m}
    {v : Fin m → E m → Mat m} (h : WeakDivergence F v)
    (hF : SquareIntegrable F) (hv : ∀ r, SquareIntegrable (v r))
    (hH : ∀ i j, ContDiff ℝ 1 (fun x => H x i j)) (hHL : SquareIntegrable H)
    (hHD : ∀ r, SquareIntegrable (coordinateDerivative H r)) (T : Mat m) :
    expectation (fun x => Matrix.trace (T * F x * H x)) =
      ∑ r, expectation (fun x => Matrix.trace (T * v r x * coordinateDerivative H r x)) :=
  (h.const_mul hF hv T).trace_test (squareIntegrable_const_mul T hF)
    (fun r => squareIntegrable_const_mul T (hv r)) hH hHL hHD

theorem WeakDivergence.sub_smul {m : ℕ} {F G : E m → Mat m}
    {v w : Fin m → E m → Mat m} (h : WeakDivergence F v) (h' : WeakDivergence G w)
    (hF : SquareIntegrable F) (hG : SquareIntegrable G)
    (hv : ∀ r, SquareIntegrable (v r)) (hw : ∀ r, SquareIntegrable (w r)) (c : ℝ) :
    WeakDivergence (fun x => F x - c • G x) (fun r x => v r x - c • w r x) := by
  intro i j z hz hzc
  have hzL : MemLp z 2 (stdGaussian (E m)) := hz.continuous.memLp_of_hasCompactSupport hzc
  have hzD (r : Fin m) : MemLp
      (fun x => fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) 2 (stdGaussian (E m)) :=
    ((hz.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hzc.fderiv_apply ℝ _)
  simp only [expectation, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul]
  erw [integral_sub ((hF i j).integrable_mul hzL)
    (((hG i j).const_mul c).integrable_mul hzL)]
  simp only [Pi.mul_apply, mul_assoc, integral_const_mul]
  have h0 := h i j z hz hzc
  have h1 := h' i j z hz hzc
  simp only [expectation] at h0 h1
  rw [h0, h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  erw [integral_sub ((hv r i j).integrable_mul (hzD r))
    (((hw r i j).integrable_mul (hzD r)).const_mul c), integral_const_mul]
  rfl

theorem WeakDivergence.neg {m : ℕ} {F : E m → Mat m}
    {v : Fin m → E m → Mat m} (h : WeakDivergence F v) :
    WeakDivergence (fun x => -F x) (fun r x => -v r x) := by
  intro i j z hz hzc
  simp only [expectation, Matrix.neg_apply, neg_mul, integral_neg, Finset.sum_neg_distrib]
  exact congrArg Neg.neg (h i j z hz hzc)

lemma squareIntegrable_mul_top {m : ℕ} {F H : E m → Mat m}
    (hF : SquareIntegrable F)
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ (stdGaussian (E m))) :
    SquareIntegrable (fun x => F x * H x) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun k _ => (hH k j).mul (hF i k)

lemma squareIntegrable_gaussian_adjoint_const_mul {m : ℕ}
    (X : Fin m → Mat m) {b : E m → Mat m}
    (hb : ∀ i j, MemLp (fun x => b x i j) ∞ (stdGaussian (E m)))
    (hdb : ∀ r, SquareIntegrable (coordinateDerivative b r)) :
    SquareIntegrable
      (fun x => ∑ r, (x r • (X r * b x) - X r * coordinateDerivative b r x)) := by
  intro i j
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  apply memLp_finsetSum
  intro r _
  apply MemLp.sub _ (squareIntegrable_const_mul (X r) (hdb r) i j)
  have hXb : MemLp (fun x => (X r * b x) i j) ∞ (stdGaussian (E m)) := by
    simp only [Matrix.mul_apply]
    exact memLp_finsetSum _ fun k _ => (hb k j).const_mul _
  exact hXb.mul (gaussian_coord_memLp r)

end Submission.Lib.EntropyRemainder
