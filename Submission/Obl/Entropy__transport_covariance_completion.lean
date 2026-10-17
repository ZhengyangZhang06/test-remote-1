import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__transport_covariance_completion.Entropy
import Submission.Obl.Entropy__transport_covariance_completion.Regularity
import Submission.Obl.Entropy__transport_covariance_completion.Completion
import Submission.Obl.Entropy__gaussian_covariance_variational

open Submission.Obl.Entropy__transport_covariance_completion
open scoped BigOperators
set_option linter.unusedVariables false

/-!
# `Submission.Entropy.transport_covariance_completion`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.Entropy__transport_covariance_completion`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/Entropy__transport_covariance_completion/`
belong to this obligation.
-/

theorem Submission.Entropy.transport_covariance_completion : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun q => (fun J => (fun t => (fun k => (fun ka => (fun γ => (fun L2 => (fun d => (fun K => (fun I => (fun Div => (fun N => (fun ta => (fun E2 => (fun W => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ r, L2 (K r)) → ∀ f : (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ x, 0 ≤ f x) → MeasureTheory.Integrable f MeasureTheory.volume → MeasureTheory.integral MeasureTheory.volume f = 1 → MeasureTheory.Integrable (fun x => f x * ‖x‖^2) MeasureTheory.volume → MeasureTheory.Integrable (fun x => f x * Real.log (f x)) MeasureTheory.volume → ∀ φ : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → ConvexOn ℝ Set.univ φ → (∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (PiLp.single 2 j (1 : ℝ))) i) → MeasureTheory.Measure.map (gradient φ) γ = MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => ENNReal.ofReal (f x)) → ∀ P : Matrix (Fin m) (Fin m) ℝ, P.PosDef → ∀ u : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ v : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), L2 u → (∀ r, L2 (v r)) → Div (fun x => u x - (J x - ka x)) (fun r x => v r x - K r x) → (fun C => 2*(m : ℝ) + Real.log C.det + 2*MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)) ≤ N A - N ka - Finset.sum Finset.univ (fun r : Fin m => N (K r)) + I (fun x => Matrix.trace ((P - 1) * E2 x)) + W P u + Finset.sum Finset.univ (fun r : Fin m => W P (v r)) - Real.log P.det) (Matrix.of (fun i j => MeasureTheory.integral MeasureTheory.volume (fun x => f x * (x i - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) i) * (x j - (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y)) j))))) (fun P F => I (fun x => Matrix.trace ((F x).transpose * P * F x)))) (fun x => 2 • ta x - ka x * ka x - Finset.sum Finset.univ (fun r : Fin m => K r x * K r x))) (fun x => cfc t (A x))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (fun F v => ∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => F x i j * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => v r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))))) (MeasureTheory.integral γ)) (d (fun x => cfc k (A x)))) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) (fun x => cfc k (A x))) (fun a => t a / q a)) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (fun x => cfc q (A x))) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)) := by
  intro m hm A hA hAs hAb hK f hf0 hf hf1 hf2 hfent φ hφ hconv hJac hmap P hP u v hu hv hDiv
  let γ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))
  let J := fun x => cfc hazard (A x)
  let ka := fun x => cfc ratioK (A x)
  let T := fun x => cfc tailLog (A x)
  let K := fun (r : Fin m) x => Matrix.of (fun i j =>
    fderiv ℝ (fun y => ka y i j) x (PiLp.single 2 r (1 : ℝ)))
  let I : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ := MeasureTheory.integral γ
  let N := fun (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) => I (fun x => ∑ i : Fin m, ∑ j : Fin m, (F x i j)^2)
  let W := fun (P : Matrix (Fin m) (Fin m) ℝ) (F : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) => I (fun x => Matrix.trace ((F x).transpose * P * F x))
  let E2 := fun x => 2 • T x - ka x * ka x - ∑ r, K r x * K r x
  let C := Submission.Lib.EntropyTools.densityCovariance f
    (MeasureTheory.integral MeasureTheory.volume (fun y => f y • y))
  change 2 * (m : ℝ) + Real.log C.det + 2 * MeasureTheory.integral MeasureTheory.volume
    (fun x => f x * Real.log (f x)) ≤ N A - N ka - ∑ r, N (K r) +
      I (fun x => Matrix.trace ((P - 1) * E2 x)) + W P u + ∑ r, W P (v r) - Real.log P.det
  have hK2 : ∀ r i j, MeasureTheory.MemLp (fun x => K r x i j) 2 γ := hK
  have hu2 : ∀ i j, MeasureTheory.MemLp (fun x => u x i j) 2 γ := hu
  have hv2 : ∀ r i j, MeasureTheory.MemLp (fun x => v r x i j) 2 γ := hv
  obtain ⟨hJsmooth, hJ2⟩ := cfc_field_memLp hm hA hAs hAb contDiff_hazard
  obtain ⟨hksmooth, hk2⟩ := cfc_field_memLp hm hA hAs hAb contDiff_ratioK
  have hJs : ∀ x, (J x).IsHermitian := fun x => cfc_predicate hazard (A x)
  have hks : ∀ x, (ka x).IsHermitian := fun x => cfc_predicate ratioK (A x)
  have hKs : ∀ r x, (K r x).IsHermitian := fun r x => derivative_isHermitian hks r x
  have hkJ : ∀ x, ka x * J x = T x := fun x => cfc_ratioK_mul_hazard (hA x)
  have hT : ∀ i j, MeasureTheory.Integrable (fun x => T x i j) γ := by
    intro i j
    have h : MeasureTheory.Integrable (fun x => (ka x * J x) i j) γ :=
      integrable_matrix_mul hk2 hJ2 i j
    simpa only [hkJ] using h
  have hE : ∀ i j, MeasureTheory.Integrable (fun x => E2 x i j) γ :=
    integrable_completion hT hk2 hK2
  have hU : ∀ i j, MeasureTheory.MemLp (fun x => (u x - (J x - ka x)) i j) 2 γ :=
    fun i j => (hu2 i j).sub ((hJ2 i j).sub (hk2 i j))
  have hV : ∀ r i j, MeasureTheory.MemLp (fun x => (v r x - K r x) i j) 2 γ :=
    fun r i j => (hv2 r i j).sub (hK2 r i j)
  have hku : ∀ i j, MeasureTheory.MemLp (fun x => (ka x + u x) i j) 2 γ :=
    fun i j => (hk2 i j).add (hu2 i j)
  have hc := pairing_weak_testing P hU hV hk2 hK2 hksmooth
    (show ∀ r x i j, K r x i j = fderiv ℝ (fun y => ka y i j) x
      (PiLp.single 2 r (1 : ℝ)) from fun _ _ _ _ => rfl) hDiv
  have hcomplete := completed_energy hP.isHermitian hJ2 hk2 hu2 hK2 hv2 hT
    hJs hks hKs hkJ hc
  have hF : ContDiff ℝ 1 (gradient φ) :=
    contDiff_gradient hφ (by exact WithTop.coe_le_coe.mpr le_top)
  have hrepr : ∀ i j, ∀ z : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z →
      I (fun x => ((ka x + u x) i j - J x i j) * z x) =
        ∑ r, I (fun x => (v r x - K r x) i j *
          fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))) := by
    intro i j z hz hzc
    have he : (fun x => ((ka x + u x) i j - J x i j) * z x) =
        (fun x => (u x - (J x - ka x)) i j * z x) := by
      funext x
      simp only [Matrix.add_apply, Matrix.sub_apply]
      ring
    rw [he]
    exact hDiv i j z hz hzc
  have hvar := Submission.Entropy.gaussian_covariance_variational m hm f hf0 hf hf1 hf2
    (gradient φ) hF hmap J hJ2 hJac (fun x => ka x + u x)
    (fun r x => v r x - K r x) hku hV hrepr P hP
  have hcov : Matrix.trace (P * C) ≤ I (fun x => Matrix.trace (P * E2 x)) +
      (W P u + ∑ r, W P (v r)) := by
    change Matrix.trace (P * C) ≤ W P (fun x => ka x + u x) +
      ∑ r, W P (fun x => v r x - K r x) at hvar
    change W P (fun x => ka x + u x) + ∑ r, W P (fun x => v r x - K r x) =
      I (fun x => Matrix.trace (P * E2 x)) + W P u + ∑ r, W P (v r) at hcomplete
    linarith
  have hent := (entropy_deficit_identity hA (fun i j => (hAs i j).continuous)
    hAb hf0 hf hfent hφ hJac hmap).2
  have htrace := integral_trace_completion hT hk2 hK2 hks hKs
  have hC : C.PosDef := Submission.Lib.EntropyTools.densityCovariance_posDef hf0 hf hf1 hf2 _
  have hfinal := completion_from_entropy_and_covariance hC hP hE
    (H := MeasureTheory.integral MeasureTheory.volume (fun x => f x * Real.log (f x)))
    (a := N A) (b := N ka) (c := ∑ r, N (K r))
    (t := I (fun x => Matrix.trace (T x))) (w := W P u + ∑ r, W P (v r))
    (by simpa only [Fintype.card_fin] using hent) htrace hcov
  simpa only [Fintype.card_fin, add_assoc] using hfinal
