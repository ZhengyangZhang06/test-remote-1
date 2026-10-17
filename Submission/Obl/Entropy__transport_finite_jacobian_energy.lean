import Submission.Obl.Entropy__transport_finite_jacobian_energy.MatrixEnergy
import Submission.Obl.Entropy__transport_finite_jacobian_energy.InverseBounds
import ChallengeDeps

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open Submission.Obl.Entropy__transport_finite_jacobian_energy
open Submission.Obl.Entropy__c1_bounded_matrix_calculus
open Submission.Lib.GaussianTransport
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.transport_finite_jacobian_energy`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__transport_finite_jacobian_energy`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__transport_finite_jacobian_energy/`
belong to this obligation.
-/

theorem Submission.Entropy.transport_finite_jacobian_energy : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) => (fun (L2 : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Prop) => (fun (d : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (J : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (ka : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (H : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (Z : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (K : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (I : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (N : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → ℝ) => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ V φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V → (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖^2) → ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → ConvexOn ℝ Set.univ φ → (∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) → MeasureTheory.Measure.map (gradient φ) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (Real.exp (-V x))) → (∀ i j : Fin m, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => z x * (-(if i = j then 1 else 0) + (J x * Matrix.of (fun u v => (fderiv ℝ (fderiv ℝ V) (gradient φ x) (PiLp.single 2 u (1 : ℝ))) (PiLp.single 2 v (1 : ℝ))) * J x) i j + Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) = -Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => I (fun x => fderiv ℝ z x (PiLp.single 2 s (1 : ℝ)) * (J x)⁻¹ s r * H r x i j)))) ∧ (∀ r, L2 (H r)) ∧ (∀ r, L2 (Z r)) ∧ (∀ r, L2 (K r))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (MeasureTheory.integral γ)) (d ka)) (d A)) (d J)) (fun x => cfc k (A x))) (fun x => cfc q (A x))) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) := by
  intro m hm A hA
  dsimp only
  intro hAs hAb V φ hV hVbounds hφ _hconv hJ hmap
  let J : space m → Matrix (Fin m) (Fin m) ℝ := fun x => cfc gaussianHazard (A x)
  have hJ' : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i := hJ
  have hpos (x : space m) : (J x).PosDef := posDef_cfc_gaussianHazard (hA x)
  have hJc := contDiff_jacobian hφ hJ'
  have hHentry (r : Fin m) (x : space m) (i j : Fin m) :
      fderiv ℝ (fun y => J y i j) x (basisVector r) =
        directional (basisVector r) J x i j :=
    directional_matrix_entry (hJc.differentiable (by simp) x) i j (basisVector r)
  have hHmatrix (r : Fin m) (x : space m) :
      (Matrix.of fun i j => fderiv ℝ (fun y => J y i j) x (basisVector r)) =
        directional (basisVector r) J x := by
    ext i j
    exact hHentry r x i j
  obtain ⟨ε, M, hε, _hM, hlower, hbound⟩ := gaussian_inverse_jacobian_bounds A hA hAb
  have hVpos (x v : space m) : 0 ≤ fderiv ℝ (fderiv ℝ V) x v v := by
    obtain ⟨cmin, cmax, hcmin, _, hb⟩ := hVbounds
    exact (mul_nonneg hcmin.le (sq_nonneg ‖v‖)).trans (hb x v).1
  have hHLp := jacobian_energy_memLp hφ hV hVpos hJ' hpos hmap hε hlower hbound
  have hALp (r : Fin m) : ∀ i j, MemLp (fun x =>
      entryDirectionalDerivative A x (basisVector r) i j) 2 (stdGaussian (space m)) := by
    apply memLp_entryDirectionalDerivative_of_cfc_of_bounded A
      (fun i j => (hAs i j).continuous) hA hAb
      (contDiff_gaussianHazard.of_le (by exact WithTop.coe_le_coe.mpr le_top))
      deriv_gaussianHazard_pos (fun x i j => (hAs i j).differentiable (by simp) x)
      (basisVector r)
    intro i j
    change MemLp (fun x => fderiv ℝ (fun y => J y i j) x (basisVector r)) 2 _
    simp_rw [hHentry]
    exact hHLp r i j
  have hk : ContDiff ℝ 1 transportRatio :=
    (contDiff_exponentialTransport.div contDiff_gaussianHazard
      (fun a => (gaussianHazard_pos a).ne')).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hKLp (r : Fin m) := memLp_entryDirectionalDerivative_cfc_of_bounded A
    (fun i j => (hAs i j).continuous) hA hAb hk
    (fun x i j => (hAs i j).differentiable (by simp) x) (basisVector r) (hALp r)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j z hz hzK
    have hw := weak_jacobian_equation hφ hV hJ' hpos hmap i j hz hzK
    simp_rw [← hHmatrix] at hw
    exact hw
  · intro r i j
    change MemLp (fun x => fderiv ℝ (fun y => J y i j) x (basisVector r)) 2 _
    simp_rw [hHentry]
    exact hHLp r i j
  · intro r i j
    exact hALp r i j
  · intro r i j
    exact hKLp r i j
