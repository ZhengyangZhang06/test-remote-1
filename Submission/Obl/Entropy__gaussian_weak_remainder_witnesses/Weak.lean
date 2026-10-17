import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.GaussianIBP
import Submission.Obl.Entropy__gaussian_weak_remainder_witnesses.Integrability

open MeasureTheory
open scoped ContDiff ENNReal

namespace Submission.Obl.Entropy__gaussian_weak_remainder_witnesses

variable {m : ℕ}
local notation "E" => Space m

lemma test_memLp {z : E → ℝ} (hz : Continuous z) (hzc : HasCompactSupport z) :
    MemLp z 2 (gaussian m) :=
  (hz.memLp_top_of_hasCompactSupport hzc _).mono_exponent le_top

lemma WeakDiv.smul {F : Field m} {V : Fin m → Field m} (h : WeakDiv F V) (c : ℝ) :
    WeakDiv (fun x => c • F x) (fun r x => c • V r x) := by
  intro i j z hz hzc
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, ← Finset.mul_sum]
  rw [h i j z hz hzc]

lemma WeakDiv.sub {F G : Field m} {V W : Fin m → Field m}
    (hF : WeakDiv F V) (hG : WeakDiv G W)
    (hFl : MatrixLp (gaussian m) 2 F) (hGl : MatrixLp (gaussian m) 2 G)
    (hVl : ∀ r, MatrixLp (gaussian m) 2 (V r))
    (hWl : ∀ r, MatrixLp (gaussian m) 2 (W r)) :
    WeakDiv (fun x => F x - G x) (fun r x => V r x - W r x) := by
  intro i j z hz hzc
  have hzlp := test_memLp hz.continuous hzc
  have hdz (r : Fin m) := test_memLp
    ((hz.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hzc.fderiv_apply ℝ (PiLp.single 2 r (1 : ℝ)))
  simp only [Matrix.sub_apply, sub_mul]
  erw [integral_sub ((hFl i j).integrable_mul hzlp) ((hGl i j).integrable_mul hzlp),
    hF i j z hz hzc, hG i j z hz hzc, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  exact (integral_sub ((hVl r i j).integrable_mul (hdz r))
    ((hWl r i j).integrable_mul (hdz r))).symm

lemma coordDeriv_const_mul {C : Field m}
    (hC : ∀ i j, ContDiff ℝ 1 (fun x => C x i j))
    (X : Mat m) (r : Fin m) (x : E) :
    coordDeriv (fun y => X * C y) r x = X * coordDeriv C r x := by
  ext i j
  unfold coordDeriv
  simp only [Matrix.of_apply, Matrix.mul_apply]
  rw [fderiv_fun_sum (fun k _ => ((hC k j).differentiable (by norm_num) x).const_mul (X i k))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_const_mul (hC k j |>.differentiable (by norm_num) x)]
  rfl

/-- The adjoint coordinate derivative gives the Gaussian weak divergence. -/
lemma weakDiv_adjoint {V : Fin m → Field m}
    (hV : ∀ r i j, ContDiff ℝ 1 (fun x => V r x i j)) :
    WeakDiv (fun x => ∑ r, (x r • V r x - coordDeriv (V r) r x)) V := by
  intro i j z hz hzc
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    coordDeriv, Matrix.of_apply, Finset.sum_mul]
  have ht (r : Fin m) : Integrable (fun x : E =>
      (x r * V r x i j - fderiv ℝ (fun y => V r y i j) x (PiLp.single 2 r (1 : ℝ))) * z x)
      (gaussian m) := by
    apply Continuous.integrable_of_hasCompactSupport _ hzc.mul_left
    exact (((EuclideanSpace.proj (𝕜 := ℝ) r).continuous.mul (hV r i j).continuous).sub
      (((hV r i j).continuous_fderiv (by norm_num)).clm_apply continuous_const)).mul hz.continuous
  rw [integral_finsetSum _ (fun r _ => ht r)]
  exact Finset.sum_congr rfl fun r _ =>
    gaussian_product_ibp (hV r i j) (hz.of_le (by simp)) hzc r

lemma witness_source_identity {A : Field m} (hA : ∀ x, (A x).IsHermitian) (x : E) :
    witnessU A x - (calcField A Submission.Lib.GaussianTransport.gaussianHazard x -
      calcField A scalarK x) =
    -(∑ r, (x r • (matX A r * calcField A scalarB x) -
      matX A r * coordDeriv (calcField A scalarB) r x)) - (7/25 : ℝ) • matY A x := by
  rw [show calcField A Submission.Lib.GaussianTransport.gaussianHazard x - calcField A scalarK x =
      A x * calcField A scalarB x - calcField A scalarL x from cfc_hazard_identity (hA x)]
  unfold witnessU witnessF residualL matB matY
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, Finset.sum_sub_distrib,
    Matrix.mul_assoc]
  module

lemma weak_witnesses {A : Field m} {g : Fin m → Field m}
    (hA : ∀ x, (A x).IsHermitian) (hAl : MatrixLp (gaussian m) 2 A)
    (hreg : Regularity A) (hg : ∀ r, MatrixLp (gaussian m) 2 (g r))
    (hdiv : WeakDiv (matY A) g) :
    WeakDiv (fun x => witnessU A x -
      (calcField A Submission.Lib.GaussianTransport.gaussianHazard x - calcField A scalarK x))
      (fun r x => witnessV A g r x - matK A r x) := by
  let V : Fin m → Field m := fun r x => matX A r * calcField A scalarB x
  let D : Field m := fun x => ∑ r, (x r • V r x - coordDeriv (V r) r x)
  have hC := (hreg scalarB smooth_scalarB).1
  have hV (r i j) : ContDiff ℝ 1 (fun x => V r x i j) := by
    change ContDiff ℝ 1 (fun x => ∑ k, matX A r i k * calcField A scalarB x k j)
    exact ContDiff.sum (fun k _ => contDiff_const.mul (hC k j))
  have hD : WeakDiv D V := weakDiv_adjoint hV
  have hVl (r : Fin m) : MatrixLp (gaussian m) 2 (V r) :=
    ((hreg.top smooth_scalarB).const_mul _).of_le le_top
  have hDl : MatrixLp (gaussian m) 2 D := by
    apply MatrixLp.sum
    intro r
    have h1 : MatrixLp (gaussian m) 2 (fun x => x r • V r x) := by
      intro i j
      exact (((hreg.top smooth_scalarB).const_mul (matX A r)) i j).mul'
        (Submission.Obl.Entropy__linear_transport_limit.memLp_coord r)
    have h2 : MatrixLp (gaussian m) 2 (coordDeriv (V r) r) := by
      have hh := ((hreg scalarB smooth_scalarB).2.2 r).const_mul (matX A r)
      intro i j
      change MemLp (fun x => coordDeriv (fun y => matX A r * calcField A scalarB y) r x i j) 2 _
      simp_rw [coordDeriv_const_mul hC]
      exact hh i j
    exact h1.sub h2
  have hh := (hD.smul (-1)).sub (hdiv.smul (7/25)) (hDl.smul (-1))
    ((matY_memLp hAl).smul (7/25)) (fun r => (hVl r).smul (-1))
    (fun r => (hg r).smul (7/25))
  have hs : (fun x => (-1 : ℝ) • D x - (7/25 : ℝ) • matY A x) =
      (fun x => witnessU A x - (calcField A Submission.Lib.GaussianTransport.gaussianHazard x -
        calcField A scalarK x)) := by
    funext x
    rw [witness_source_identity hA]
    simp only [D, V, coordDeriv_const_mul hC, neg_one_smul]
  have hv : (fun r x => (-1 : ℝ) • V r x - (7/25 : ℝ) • g r x) =
      (fun r x => witnessV A g r x - matK A r x) := by
    funext r x
    dsimp [V, witnessV, residualD]
    module
  rw [hs, hv] at hh
  exact hh

end Submission.Obl.Entropy__gaussian_weak_remainder_witnesses
