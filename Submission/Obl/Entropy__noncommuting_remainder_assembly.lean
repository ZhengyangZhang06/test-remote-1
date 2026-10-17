import Mathlib
import ChallengeDeps
import Submission.Obl.Entropy__gaussian_weak_remainder_expansion
import Submission.Obl.Entropy__pointwise_weighted_remainder
import Submission.Obl.Entropy__noncommuting_remainder_assembly.CommutatorInvariant

set_option linter.unusedVariables false

/-!
# Assembly from the Gaussian expansion and pointwise matrix estimates

The compensated commutator estimate is proved in the owned helper modules.
The two proposed children supply the exact analytic expansion and the
independent weighted bound. The glue integrates their sum.
-/

theorem Submission.Entropy.noncommuting_remainder_assembly : ∀ m : ℕ, 1 ≤ m → ∀ A : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∀ hA : ∀ x, (A x).IsHermitian, (fun γ => (fun L2 => (fun d => (fun Z => (fun t => (fun q => (fun k => (fun K => (fun I => (fun Div => (fun X => (fun Y => (fun B => (fun S => (fun b => (fun l => (fun p => (fun h => (fun cost => (fun R => (fun W => (fun ta => (fun ka => (fun E2 => (fun J => (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → (∀ a, 0 < p a) → ∀ g : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), (∀ r x, (g r x).IsHermitian) → (∀ r, L2 (g r)) → Div Y g → (fun N => (fun Dr => (fun Lr => (fun f0 => (fun Mr => (fun PB => ∃ u : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∃ v : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), L2 u ∧ (∀ r, L2 (v r)) ∧ Div (fun x => u x - (J x - ka x)) (fun r x => v r x - K r x) ∧ I (fun x => Matrix.trace ((S - 1) * E2 x)) + W S u + Finset.sum Finset.univ (fun r : Fin m => W S (v r)) - Real.log S.det ≤ R + PB) (Finset.sum Finset.univ (fun r : Fin m => (40/37)*N (fun x => Dr r x - (7/25 : ℝ) • g r x) + (42/37)*N (fun x => Dr r x - (3/4 : ℝ) • g r x) + (27/592)*N (g r) + (40/3)*N (Lr r) + (5/17)*N (fun x => Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x))))) (fun r x => d (fun y => cfc f0 (A y)) r x - X r * cfc (deriv f0) (A x) - 2 • (Dr r x * cfc b (A x)) - (80/3 : ℝ) • (Lr r x * cfc l (A x)) + (3/2 : ℝ) • (g r x * cfc b (A x)))) (fun a => k a * (1 + b a))) (fun r x => d (fun y => cfc b (A y)) r x - X r * cfc l (A x))) (fun r x => K r x - X r * cfc b (A x))) (fun F => I (fun x => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (F x i j)^2))))) (fun x => cfc q (A x))) (fun x => 2 • ta x - ka x * ka x - Finset.sum Finset.univ (fun r : Fin m => K r x * K r x))) (fun x => cfc k (A x))) (fun x => cfc t (A x))) (fun P F => I (fun x => Matrix.trace ((F x).transpose * P * F x)))) (Matrix.trace (S - 1) - Real.log S.det - I (fun x => Matrix.trace ((-(S - 1) * (B - 1)) * ((3/20 : ℝ) • 1 + (1813/4000 : ℝ) • S) * cfc p (A x))) + I (fun x => Matrix.trace (Y x * Y x * cfc cost (A x))))) (fun a => (40/37) * ((b a - 7/25)^2 + (5/96) * (h a)^2 / p a))) (fun a => k a * (1 + b a) - (3/2) * k a - (80/3) * (b a - 7/25) * l a)) (fun a => deriv (fun z => k z * (1 + b z)) a - (b a)^2 - (40/3) * (l a)^2)) (deriv b)) (deriv k)) (((37/40 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) + (3/40 : ℝ) • B)⁻¹)) (Finset.sum Finset.univ (fun r : Fin m => X r * X r))) (fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r))) (fun r => Matrix.of (fun i j => I (fun x => x r * A x i j)))) (fun F v => ∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => F x i j * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => v r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ)))))) (MeasureTheory.integral γ)) (d (fun x => cfc k (A x)))) (fun a => t a / q a)) (fun a => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))) (fun a => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)))) (d A)) (fun F r x => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ))))) (fun F => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ)) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  classical
  intro m hm A hA
  let γ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))
  let I := (MeasureTheory.integral γ : ((EuclideanSpace ℝ (Fin m)) → ℝ) → ℝ)
  let L2 := fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => ∀ i j, MeasureTheory.MemLp (fun x => F x i j) 2 γ
  let d := fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) => Matrix.of (fun i j => fderiv ℝ (fun y => F y i j) x (PiLp.single 2 r (1 : ℝ)))
  let Z := d A
  let t := fun a : ℝ => -Real.log (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))
  let q := fun a : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 a / ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a)
  let k := fun a => t a / q a
  let b := deriv k
  let l := deriv b
  let f0 := fun a => k a * (1 + b a)
  let p := fun a => deriv f0 a - (b a)^2 - (40/3) * (l a)^2
  let h := fun a => k a * (1 + b a) - (3/2) * k a - (80/3) * (b a - 7/25) * l a
  let cost := fun a => (40/37) * ((b a - 7/25)^2 + (5/96) * (h a)^2 / p a)
  let K := d (fun x => cfc k (A x))
  let X := fun r : Fin m => Matrix.of (fun i j => I (fun x => x r * A x i j))
  let Y := fun x => A x - Finset.sum Finset.univ (fun r : Fin m => x r • X r)
  let B := Finset.sum Finset.univ (fun r : Fin m => X r * X r)
  let S := (((37/40 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) + (3/40 : ℝ) • B)⁻¹)
  let T := S - 1
  let H := -T * (B - 1)
  let ρ := (3/20 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) + (1813/4000 : ℝ) • S
  let ss := fun (Q : Matrix (Fin m) (Fin m) ℝ) => Finset.sum Finset.univ (fun i : Fin m => Finset.sum Finset.univ (fun j : Fin m => (Q i j)^2))
  let N := fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => I (fun x => ss (F x))
  let W := fun (P : Matrix (Fin m) (Fin m) ℝ) (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) => I (fun x => Matrix.trace ((F x).transpose * P * F x))
  let Div := fun (F : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ)) => ∀ i j, ∀ z : (EuclideanSpace ℝ (Fin m)) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) z → HasCompactSupport z → I (fun x => F x i j * z x) = Finset.sum Finset.univ (fun r : Fin m => I (fun x => v r x i j * fderiv ℝ z x (PiLp.single 2 r (1 : ℝ))))
  let ka := fun x => cfc k (A x)
  let J := fun x => cfc q (A x)
  let E2 := fun x => 2 • cfc t (A x) - ka x * ka x - Finset.sum Finset.univ (fun r : Fin m => K r x * K r x)
  change (∀ i j, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => A x i j)) → (∃ R : ℝ, 0 < R ∧ ∀ x i j, |A x i j| ≤ R) → (∀ i j, I (fun x => A x i j) = 0) → (∀ r, L2 (Z r)) → (∀ r, L2 (K r)) → (∀ a, 0 < p a) → _
  intro hsm hbnd hmean hZ hK hp g hg hgL hdiv
  let Dr := fun r x => K r x - X r * cfc b (A x)
  let Lr := fun r x => d (fun y => cfc b (A y)) r x - X r * cfc l (A x)
  let Mr := fun r x => d (fun y => cfc f0 (A y)) r x - X r * cfc (deriv f0) (A x) - 2 • (Dr r x * cfc b (A x)) - (80/3 : ℝ) • (Lr r x * cfc l (A x)) + (3/2 : ℝ) • (g r x * cfc b (A x))
  let v := fun r x => Dr r x - (7/25 : ℝ) • g r x
  let w := fun r x => Dr r x - (3/4 : ℝ) • g r x
  let F := fun x => Y x * (cfc b (A x) - (7/25 : ℝ) • 1) + Finset.sum Finset.univ (fun r : Fin m => X r * Lr r x)
  let u := fun x => F x + (B - 1) * cfc l (A x)
  let Core := fun x => -Matrix.trace (H * cfc p (A x)) + Matrix.trace (T * (Y x * cfc h (A x) + Finset.sum Finset.univ (fun r : Fin m => X r * Mr r x))) + Matrix.trace ((F x).transpose * S * F x) + Finset.sum Finset.univ (fun r : Fin m => Matrix.trace ((v r x).transpose * S * v r x)) + (9/16 : ℝ) * Matrix.trace (T * Finset.sum Finset.univ (fun r : Fin m => g r x * g r x))
  let Comm := fun x => -Matrix.trace (T * cfc b (A x) * B * cfc b (A x) - T * B * cfc b (A x) * cfc b (A x)) - 2 * Matrix.trace ((T * cfc b (A x) - cfc b (A x) * T) * Finset.sum Finset.univ (fun r : Fin m => X r * w r x)) - Matrix.trace (T * Finset.sum Finset.univ (fun r : Fin m => (w r x).transpose * w r x))
  let Right := fun x => -Matrix.trace (H * ρ * cfc p (A x)) + Matrix.trace (Y x * Y x * cfc cost (A x)) + Finset.sum Finset.univ (fun r : Fin m => (40/37 : ℝ) * ss (v r x) + (42/37 : ℝ) * ss (w r x) + (27/592 : ℝ) * ss (g r x) + (40/3 : ℝ) * ss (Lr r x) + (5/17 : ℝ) * ss (Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x)))
  let PB := Finset.sum Finset.univ (fun r : Fin m => (40/37)*N (v r) + (42/37)*N (w r) + (27/592)*N (g r) + (40/3)*N (Lr r) + (5/17)*N (fun x => Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x)))
  have hexp := Submission.Entropy.gaussian_weak_remainder_expansion m hm A hA
    hsm hbnd hmean hZ hK hp g hg hgL hdiv
  change (∀ r, (X r).IsHermitian) ∧ (∀ x, (Y x).IsHermitian) ∧ L2 u ∧ (∀ r, L2 (v r)) ∧ Div (fun x => u x - (J x - ka x)) (fun r x => v r x - K r x) ∧ MeasureTheory.Integrable (fun x => Core x + Comm x) γ ∧ MeasureTheory.Integrable Right γ ∧ I (fun x => Matrix.trace (T * E2 x)) + W S u + Finset.sum Finset.univ (fun r : Fin m => W S (v r)) = Matrix.trace T + I (fun x => Core x + Comm x) ∧ I Right = -I (fun x => Matrix.trace (H * ρ * cfc p (A x))) + I (fun x => Matrix.trace (Y x * Y x * cfc cost (A x))) + PB at hexp
  rcases hexp with ⟨hX, hY, hu, hv, hDiv, hleft, hright, hexact, hbudget⟩
  change ∃ u : (EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ, ∃ v : Fin m → ((EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ), L2 u ∧ (∀ r, L2 (v r)) ∧
    Div (fun x => u x - (J x - ka x)) (fun r x => v r x - K r x) ∧
    I (fun x => Matrix.trace (T * E2 x)) + W S u +
      Finset.sum Finset.univ (fun r : Fin m => W S (v r)) - Real.log S.det ≤
    Matrix.trace T - Real.log S.det - I (fun x => Matrix.trace (H * ρ * cfc p (A x))) +
      I (fun x => Matrix.trace (Y x * Y x * cfc cost (A x))) + PB
  refine ⟨u, v, hu, hv, hDiv, ?_⟩
  have hpoint (x : EuclideanSpace ℝ (Fin m)) : Core x + Comm x ≤ Right x := by
    have hc := Submission.Obl.Entropy__noncommuting_remainder_assembly.commutator_bound_constants
      X (fun r => w r x) (cfc b (A x)) hX (cfc_predicate b (A x))
    change Comm x ≤ (42/37 : ℝ) * Finset.sum Finset.univ (fun r : Fin m => ss (w r x)) at hc
    have hw := Submission.Entropy.pointwise_weighted_remainder m X hX (A x) (Y x)
      (hA x) (hY x) b h p hp (fun r => Dr r x) (fun r => Lr r x)
      (fun r => Mr r x) (fun r => g r x) (fun r => hg r x)
    change Core x ≤ -Matrix.trace (H * ρ * cfc p (A x)) + Matrix.trace (Y x * Y x * cfc cost (A x)) + Finset.sum Finset.univ (fun r : Fin m => (40/37 : ℝ) * ss (v r x) + (27/592 : ℝ) * ss (g r x) + (40/3 : ℝ) * ss (Lr r x) + (5/17 : ℝ) * ss (Mr r x * cfc (fun a => (Real.sqrt (p a))⁻¹) (A x))) at hw
    simp only [Finset.sum_add_distrib, Finset.mul_sum] at hc hw
    simp only [Right, Finset.sum_add_distrib]
    linarith only [hw, hc]
  have hint := MeasureTheory.integral_mono hleft hright hpoint
  change I (fun x => Core x + Comm x) ≤ I Right at hint
  linarith only [hexact, hbudget, hint]
