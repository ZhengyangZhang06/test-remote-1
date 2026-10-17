import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__smooth_gaussian_transport.OneDimensional
import Submission.Obl.Entropy__smooth_gaussian_transport.BrenierSmooth

theorem Submission.Entropy.smooth_gaussian_transport : ∀ m : ℕ, 1 ≤ m → (fun (H : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ → ℝ → Prop) => (fun (regular : ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => (fun (T : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ((EuclideanSpace ℝ (Fin m)) → ℝ) → Prop) => ∀ V : ((EuclideanSpace ℝ (Fin m)) → ℝ), regular V → ∃ φ : ((EuclideanSpace ℝ (Fin m)) → ℝ), T V φ) (fun U φ : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧ ConvexOn ℝ Set.univ φ ∧ MeasureTheory.Measure.map (gradient φ) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (Real.exp (-U x))))) (fun V : ((EuclideanSpace ℝ (Fin m)) → ℝ) => ContDiff ℝ ((⊤ : ENat) : WithTop ENat) V ∧ (∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ H V a b) ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x)) MeasureTheory.volume ∧ MeasureTheory.integral MeasureTheory.volume (fun x => Real.exp (-V x)) = 1 ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * ‖x‖ ^ 2) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun x => Real.exp (-V x) * Real.log (Real.exp (-V x))) MeasureTheory.volume)) (fun (F : ((EuclideanSpace ℝ (Fin m)) → ℝ)) (a b : ℝ) => ∀ x v : (EuclideanSpace ℝ (Fin m)), a * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v ∧ (fderiv ℝ (fderiv ℝ F) x v) v ≤ b * ‖v‖ ^ 2) := by
  intro m hm V hV
  rcases hV with ⟨hVs, hH, hVi, hVm, hV2, hVent⟩
  by_cases hdim : m = 1
  · subst m
    exact Submission.Obl.Entropy__smooth_gaussian_transport.exists_smooth_convex_gradient_transport_one
      hVs hVi hVm
  obtain ⟨φ, hconv, hcont, hmeas, hL2, hlaw⟩ :=
    Submission.Obl.Entropy__smooth_gaussian_transport.exists_continuous_convex_gradient_transport
      hVi hVm hV2
  rcases hH with ⟨a, b, ha, hab, hH⟩
  exact ⟨φ, Submission.Obl.Entropy__smooth_gaussian_transport.brenier_contDiff_infty
    hm hVs ha (fun x v => (hH x v).1) hconv hlaw, hconv, hlaw⟩
