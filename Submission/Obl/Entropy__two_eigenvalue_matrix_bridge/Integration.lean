import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.FieldBudget

open scoped BigOperators Topology
open Matrix MeasureTheory

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate Submission.Lib.EntropyTools

variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

lemma integrated_bridge_of_cfc (μ : Measure (EuclideanSpace ℝ (Fin m))) [IsFiniteMeasure μ]
    (k q : ℝ → ℝ) (hk : ContDiff ℝ (⊤ : ENat) k)
    (hq : Continuous q) (hqpos : ∀ a, 0 < q a) (hp : ∀ a, 0 < scalarP k a)
    (hs : ∀ a c G g Z,
      (endpointCost (deriv k) (deriv (deriv k)) (scalarP k) (scalarE k)
          (deltaK k) (deltaB k) (psi k) a c G g Z +
       endpointCost (deriv k) (deriv (deriv k)) (scalarP k) (scalarE k)
          (deltaK k) (deltaB k) (psi k) c a G g Z)/2 ≤
        chaosQuadratic G (g-G/2) + gapWeight (fun a => Real.log (q a)) a c*Z^2)
    (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hAc : ∀ i j, ContDiff ℝ (⊤ : ENat) (fun x => A x i j))
    (hAb : ∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R)
    (X : Fin m → Matrix n n ℝ) (hX : ∀ r, (X r).IsHermitian)
    (hZ : ∀ r i j, MemLp (fun x => entryPartial A r x i j) 2 μ)
    (hK : ∀ r i j, MemLp (fun x => entryPartial (fun y => cfc k (A y)) r x i j) 2 μ)
    (g : Fin m → EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (hg : ∀ r x, (g r x).IsHermitian)
    (hgL2 : ∀ r i j, MemLp (fun x => g r x i j) 2 μ)
    (hC : ∀ (v : ℝ → ℝ), Differentiable ℝ v → ∀ r x i j,
      rotate (hA x).eigenvectorUnitary (entryPartial (fun y => cfc v (A y)) r x) i j =
        dividedDiff v ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
          rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j)
    (hCL2 : ∀ (v : ℝ → ℝ), ContDiff ℝ 1 v → ∀ r i j,
      MemLp (fun x => entryPartial (fun y => cfc v (A y)) r x i j) 2 μ) :
    let N := fun F : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ =>
      ∫ x, squareEnergy (F x) ∂μ
    (∑ r, ((40/37)*N (fun x => firstResidual k A X r x - (7/25 : ℝ) • g r x) +
      (42/37)*N (fun x => firstResidual k A X r x - (3/4 : ℝ) • g r x) +
      (27/592)*N (g r) + (40/3)*N (secondResidual k A X r) +
      (5/17)*N (fun x => thirdResidual k A X g r x *
        cfc (fun a => (Real.sqrt (scalarP k a))⁻¹) (A x)))) ≤
      (∫ x, ∑ r, ∑ i, ∑ j,
        chaosQuadratic (entryPartial (fun y => A y - ∑ s, y s • X s) r x i j)
          (g r x i j - entryPartial (fun y => A y - ∑ s, y s • X s) r x i j / 2) ∂μ) +
      ∫ x, ∑ r, ∑ i, ∑ j,
        gapWeight (fun a => Real.log (q a)) ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
          (rotate (hA x).eigenvectorUnitary (entryPartial A r x) i j)^2 ∂μ := by
  dsimp only
  have hAb' : ∃ R : ℝ, 0 ≤ R ∧ ∀ x i j, |A x i j| ≤ R := by
    obtain ⟨R, hR, hb⟩ := hAb
    exact ⟨R, hR.le, hb⟩
  have hAc' : Continuous A := continuous_pi fun i => continuous_pi fun j => (hAc i j).continuous
  have hAd (i j : n) := (hAc i j).differentiable (by norm_num)
  have hb := (contDiff_infty_iff_deriv.mp hk).2
  have hl := (contDiff_infty_iff_deriv.mp hb).2
  have hf := scalarF_smooth hk
  have hfp := (contDiff_infty_iff_deriv.mp hf).2
  have hmult (F : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
      (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ)
      (v : ℝ → ℝ) (hv : Continuous v) (i j : n) :
      MemLp (fun x => (F x * cfc v (A x)) i j) 2 μ :=
    l2_mul_bounded_right hF
      (fun i j => (continuous_cfc_entries A hA hAc' v hv i j).aestronglyMeasurable)
      (bounded_cfc_entries A hA hAb' v hv) i j
  have hXl2 (r : Fin m) (i j : n) : MemLp (fun _ : EuclideanSpace ℝ (Fin m) => X r i j) 2 μ :=
    memLp_const _
  have hD (r : Fin m) (i j : n) : MemLp (fun x => firstResidual k A X r x i j) 2 μ :=
    (hK r i j).sub (hmult (fun _ => X r) (hXl2 r) (deriv k) hb.continuous i j)
  have hL (r : Fin m) (i j : n) : MemLp (fun x => secondResidual k A X r x i j) 2 μ :=
    (hCL2 (deriv k) (hb.of_le (by norm_num)) r i j).sub
      (hmult (fun _ => X r) (hXl2 r) (deriv (deriv k)) hl.continuous i j)
  have hM (r : Fin m) (i j : n) : MemLp (fun x => thirdResidual k A X g r x i j) 2 μ := by
    have hh := (((hCL2 (scalarF k) (hf.of_le (by norm_num)) r i j).sub
      (hmult (fun _ => X r) (hXl2 r) (deriv (scalarF k)) hfp.continuous i j)).sub
      ((hmult (firstResidual k A X r) (hD r) (deriv k) hb.continuous i j).const_mul 2)).sub
      ((hmult (secondResidual k A X r) (hL r) (deriv (deriv k)) hl.continuous i j).const_mul (80/3))
    convert hh.add ((hmult (g r) (hgL2 r) (deriv k) hb.continuous i j).const_mul (3/2)) using 1
    ext x
    simp only [thirdResidual, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have hweight : Continuous (fun a => (Real.sqrt (scalarP k a))⁻¹) :=
    ((scalarP_continuous hk).sqrt).inv₀ (fun a => (Real.sqrt_pos.mpr (hp a)).ne')
  have hW (r : Fin m) := hmult (thirdResidual k A X g r) (hM r)
    (fun a => (Real.sqrt (scalarP k a))⁻¹) hweight
  have h₁ (r : Fin m) (i j : n) : MemLp
      (fun x => (firstResidual k A X r x - (7/25 : ℝ) • g r x) i j) 2 μ :=
    (hD r i j).sub ((hgL2 r i j).const_mul (7/25))
  have h₂ (r : Fin m) (i j : n) : MemLp
      (fun x => (firstResidual k A X r x - (3/4 : ℝ) • g r x) i j) 2 μ :=
    (hD r i j).sub ((hgL2 r i j).const_mul (3/4))
  have hG (r : Fin m) (i j : n) : MemLp
      (fun x => entryPartial (fun y => A y - ∑ s, y s • X s) r x i j) 2 μ := by
    simpa only [entryPartial_remainder A hAd X, Matrix.sub_apply, Pi.sub_apply] using!
      (hZ r i j).sub (hXl2 r i j)
  simp only [squareEnergy]
  erw [integral_budget _ _ _ _ _ h₁ h₂ hgL2 hL hW]
  apply integrated_bound_of_pointwise
  · intro x
    exact Finset.sum_nonneg fun r _ => matrixBudget_nonneg _ _ _ _ _ _
  · exact integrable_chaosSum hG hgL2
  · exact integrable_finsetSum _ fun r _ =>
      integrable_separation_spectral A (entryPartial A r) hA hAc' hAb' (hZ r)
        (fun a => Real.log (q a)) (hq.log (fun a => (hqpos a).ne'))
  · intro x
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    simpa only [entryPartial_remainder A hAd X, matrixBudget, squareEnergy] using!
      fieldBudget_le k hk (gapWeight (fun a => Real.log (q a))) hp hs A hA X hX g hg hC r x

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
