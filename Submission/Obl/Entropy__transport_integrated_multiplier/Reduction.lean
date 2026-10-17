import Submission.Obl.Entropy__transport_integrated_multiplier.Assembly

namespace Submission.Obl.Entropy__transport_integrated_multiplier

/-- The frozen multiplier statement follows from the frozen C1 calculus statement o043. -/
theorem transport_multiplier_of_bounded_c1_calculus
    (hCfc : ∀ m : ℕ, 1 ≤ m →
      ∀ A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ,
      (∀ x, (A x).IsHermitian) →
      (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) →
      ∀ g : ℝ → ℝ, ContDiff ℝ 1 g →
        (∀ i j, ContDiff ℝ 1 (fun x => cfc g (A x) i j)) ∧
        (∃ S : ℝ, 0 < S ∧ ∀ x i j, |cfc g (A x) i j| ≤ S)) :
∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun (q : ℝ → ℝ) => (fun (k : ℝ → ℝ) => (fun (γ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))) => (fun (L2 : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Prop) => (fun (d : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (J : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (ka : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => (fun (H : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (Z : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (K : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => (fun (I : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ) => (fun (N : ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) → ℝ) => (fun (R : (EuclideanSpace ℝ (Fin m)) → ℝ) => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → ∀ V φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V → (∃ cmin cmax : ℝ, 0 < cmin ∧ cmin ≤ cmax ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), cmin * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v ∧ (fderiv ℝ (fderiv ℝ V) x v) v ≤ cmax * ‖v‖^2) → ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → (∀ i j : Fin m, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => z x * (-(if i = j then 1 else 0) + (J x * Matrix.of (fun u v => (fderiv ℝ (fderiv ℝ V) (gradient φ x) (PiLp.single 2 u (1 : ℝ))) (PiLp.single 2 v (1 : ℝ))) * J x) i j + Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) = -Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => I (fun x => fderiv ℝ z x (PiLp.single 2 s (1 : ℝ)) * (J x)⁻¹ s r * H r x i j)))) → (∀ r, L2 (H r)) → (∀ r, L2 (K r)) → MeasureTheory.Integrable R γ ∧ I R ≤ N ka) (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (ka x * ka x) i j * Matrix.trace ((J x)⁻¹ * H i x * (J x)⁻¹ * H j x))) + Finset.sum Finset.univ (fun r : Fin m => Finset.sum Finset.univ (fun s : Fin m => (J x)⁻¹ r s * Matrix.trace ((K s x * ka x + ka x * K s x) * H r x))))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (MeasureTheory.integral γ)) (d ka)) (d A)) (d J)) (fun x => cfc k (A x))) (fun x => cfc q (A x))) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) / q a)) (fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) := by
  intro m hm A hA hAc hAb V φ hV hVb hφ hweak hH hK
  have hone : (1 : WithTop ENat) ≤ (⊤ : ENat) :=
    WithTop.coe_le_coe.mpr (le_top : (1 : ENat) ≤ ⊤)
  have hk : ContDiff ℝ 1 Submission.Lib.GaussianTransport.transportRatio :=
    contDiff_transportRatio.of_le hone
  have hAc1 : ∀ i j, ContDiff ℝ 1 (fun x => A x i j) :=
    fun i j => (hAc i j).of_le hone
  have hQc := (hCfc m hm A hA hAc1 hAb _ hk).1
  exact transport_multiplier_of_c1
    A hA (fun i j => (hAc i j).continuous) hAb hQc V φ hV hVb hφ hweak hH hK

end Submission.Obl.Entropy__transport_integrated_multiplier
