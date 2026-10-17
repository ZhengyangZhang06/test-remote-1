/- Adapted from session x0073, commit 42bad91, on this obligation. -/
import Submission.Lib.PairEstimate.Integration
import Submission.Lib.PairEstimate.MatrixAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev M (m : ℕ) := Matrix (Fin m) (Fin m) ℝ
noncomputable abbrev gaussian (m : ℕ) := ProbabilityTheory.stdGaussian (E m)
noncomputable def coordDeriv {m : ℕ} (f : E m → ℝ) (r : Fin m) (x : E m) : ℝ :=
  fderiv ℝ f x (PiLp.single 2 r (1 : ℝ))
noncomputable def matrixDeriv {m : ℕ} (F : E m → M m) (r : Fin m) (x : E m) : M m :=
  Matrix.of (fun i j => coordDeriv (fun y => F y i j) r x)
def MatrixL2 {m : ℕ} (F : E m → M m) : Prop :=
  ∀ i j, MemLp (fun x => F x i j) 2 (gaussian m)
noncomputable def energy {m : ℕ} (F : E m → M m) : ℝ :=
  ∫ x, ∑ i, ∑ j, (F x i j)^2 ∂gaussian m
noncomputable def quadratic (a b : ℝ) : ℝ :=
  (43/100)*a^2 + (26/100)*a*b + (68/25)*b^2

lemma quadratic_expand (a b : ℝ) :
    quadratic a (b-a/2) = (49/50)*a^2 - (123/50)*(b*a) + (68/25)*b^2 := by
  simpa [quadratic, mul_comm, mul_left_comm, mul_assoc, Submission.Lib.EntropyTools.chaosQuadratic] using
    (Submission.Lib.PairEstimate.chaosQuadratic_shift a b)

lemma integrable_quadratic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G v : α → ℝ} (hG : MemLp G 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => quadratic (G x) (v x-G x/2)) μ := by
  exact Submission.Lib.PairEstimate.integrable_chaosQuadratic hG hv

lemma integral_quadratic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G v : α → ℝ} (hG : MemLp G 2 μ) (hv : MemLp v 2 μ) :
    (∫ x, quadratic (G x) (v x-G x/2) ∂μ) =
      (49/50)*(∫ x, (G x)^2 ∂μ) - (123/50)*(∫ x, v x*G x ∂μ) +
      (68/25)*(∫ x, (v x)^2 ∂μ) := by
  simp_rw [quadratic_expand]
  have h1 : Integrable (fun x => (49/50 : ℝ)*(G x)^2) μ :=
    hG.integrable_sq.const_mul _
  have h2 : Integrable (fun x => (123/50 : ℝ)*(v x*G x)) μ :=
    (hv.integrable_mul hG).const_mul _
  have h3 : Integrable (fun x => (68/25 : ℝ)*(v x)^2) μ :=
    hv.integrable_sq.const_mul _
  have h12 : Integrable (fun x => (49/50 : ℝ)*(G x)^2 - (123/50)*(v x*G x)) μ :=
    h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2]
  simp only [integral_const_mul]

lemma scalar_closing {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {G v : ι → α → ℝ} {V : ℝ}
    (hG : ∀ r, MemLp (G r) 2 μ) (hv : ∀ r, MemLp (v r) 2 μ)
    (hgap : 2*V ≤ ∑ r, ∫ x, (G r x)^2 ∂μ)
    (hcross : (∑ r, ∫ x, v r x*G r x ∂μ) = V)
    (hnorm : (∑ r, ∫ x, (v r x)^2 ∂μ) ≤ V/2) :
    V - (∑ r, ∫ x, (G r x)^2 ∂μ) +
      (∑ r, ∫ x, quadratic (G r x) (v r x-G r x/2) ∂μ) ≤ -(7/50)*V := by
  have hQ : (∑ r, ∫ x, quadratic (G r x) (v r x-G r x/2) ∂μ) =
      (49/50)*(∑ r, ∫ x, (G r x)^2 ∂μ) -
      (123/50)*(∑ r, ∫ x, v r x*G r x ∂μ) +
      (68/25)*(∑ r, ∫ x, (v r x)^2 ∂μ) := by
    simp_rw [integral_quadratic (hG _) (hv _)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hQ, hcross]
  linarith

lemma energy_eq_sum {m : ℕ} {F : E m → M m} (hF : MatrixL2 F) :
    energy F = ∑ i, ∑ j, ∫ x, (F x i j)^2 ∂gaussian m := by
  unfold energy
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hF i j).integrable_sq))]
  congr 1
  funext i
  exact integral_finsetSum _ (fun j _ => (hF i j).integrable_sq)

lemma quadratic_energy_eq_sum {m : ℕ} {G g : Fin m → E m → M m}
    (hG : ∀ r, MatrixL2 (G r)) (hg : ∀ r, MatrixL2 (g r)) :
    (∫ x, ∑ r, ∑ i, ∑ j,
      quadratic (G r x i j) (g r x i j-G r x i j/2) ∂gaussian m) =
      ∑ i, ∑ j, ∑ r, ∫ x,
        quadratic (G r x i j) (g r x i j-G r x i j/2) ∂gaussian m := by
  have hint (r i j) := integrable_quadratic (hG r i j) (hg r i j)
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hint r i j)))]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => hint _ i j)), integral_finsetSum _ (fun j _ => hint _ _ j)]
  rw [Finset.sum_comm]
  congr 1
  funext i
  exact Finset.sum_comm

end Submission.Obl.Entropy__gaussian_chaos_resolvent
