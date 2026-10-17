/- Adapted from: here:o022. Original proofs by session x0047. -/
import Submission.Lib.GaussianHermite.Hermite
import Submission.Lib.GaussianHermite.MomentDetermination

open MeasureTheory ProbabilityTheory Polynomial Filter Set
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Lib.GaussianHermite

private noncomputable abbrev γ : Measure ℝ := gaussianReal 0 1

/-- Exponentials of linear functions have finite Gaussian second moments. -/
theorem memLp_exp_mul_gaussianReal (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 γ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2 * t) using 1
  ext x
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Nonnegative Gaussian L2 densities with the same moments coincide. -/
theorem ae_eq_of_gaussian_moments {f g : ℝ → ℝ}
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hmom : ∀ n : ℕ, (∫ x, f x * x ^ n ∂γ) = ∫ x, g x * x ^ n ∂γ) :
    f =ᵐ[γ] g := by
  have hfmeas := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hgmeas := hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let μ := γ.withDensity (fun x => ENNReal.ofReal (f x))
  let ν := γ.withDensity (fun x => ENNReal.ofReal (g x))
  have hfin {u : ℝ → ℝ} (hu : MemLp u 2 γ) (hu0 : ∀ x, 0 ≤ u x) :
      IsFiniteMeasure (γ.withDensity (fun x => ENNReal.ofReal (u x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hu.integrable (by norm_num))
      (Eventually.of_forall hu0)]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure μ := hfin hf hf0
  letI : IsFiniteMeasure ν := hfin hg hg0
  have hexp {u : ℝ → ℝ} (hu : MemLp u 2 γ) (hu0 : ∀ x, 0 ≤ u x) :
      integrableExpSet id (γ.withDensity (fun x => ENNReal.ofReal (u x))) = univ := by
    apply Set.eq_univ_of_forall
    intro t
    change Integrable (fun x : ℝ => Real.exp (t * x)) _
    rw [integrable_withDensity_iff_integrable_smul₀'
      hu.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hu0 _), smul_eq_mul]
    exact hu.integrable_mul (memLp_exp_mul_gaussianReal t)
  have he : μ = ν := by
    apply measure_eq_of_moments (hexp hf hf0) (hexp hg hg0)
    intro n
    rw [integral_withDensity_eq_integral_toReal_smul₀ hfmeas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hgmeas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hf0 _), ENNReal.toReal_ofReal (hg0 _),
      smul_eq_mul] using hmom n
  have hae := (withDensity_eq_iff_of_sigmaFinite hfmeas hgmeas).mp he
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf0 x) (hg0 x)).mp hx

/-- Orthogonality to all monomials forces a Gaussian L2 function to vanish. -/
theorem ae_eq_zero_of_gaussian_moments {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (hmom : ∀ n : ℕ, (∫ x, f x * x ^ n ∂γ) = 0) : f =ᵐ[γ] 0 := by
  have h := ae_eq_of_gaussian_moments (hf.norm.add hf) (hf.norm.sub hf)
    (fun x => by change 0 ≤ ‖f x‖ + f x; rw [Real.norm_eq_abs]; have := neg_abs_le (f x); linarith)
    (fun x => sub_nonneg.mpr (le_abs_self (f x))) ?_
  · filter_upwards [h] with x hx
    change ‖f x‖ + f x = ‖f x‖ - f x at hx
    change f x = 0
    linarith
  · intro n
    have hp : MemLp (fun x : ℝ => x ^ n) 2 γ := by
      convert memLp_polynomial_gaussianReal (X ^ n) using 1
      ext x
      simp
    have h1 : Integrable (fun x => ‖f x‖ * x ^ n) γ := hf.norm.integrable_mul hp
    have h2 : Integrable (fun x => f x * x ^ n) γ := hf.integrable_mul hp
    simp only [Pi.add_apply, Pi.sub_apply, add_mul, sub_mul]
    rw [integral_add h1 h2, integral_sub h1 h2, hmom]
    ring

noncomputable def hermiteSequence : Polynomial.Sequence ℝ where
  elems' := hermitePoly
  degree_eq' n := by
    rw [hermitePoly, (Polynomial.hermite_monic n).degree_map, Polynomial.degree_hermite]

theorem span_hermitePoly : Submodule.span ℝ (Set.range hermitePoly) = ⊤ := by
  apply hermiteSequence.span
  intro n
  have h : (hermitePoly n).Monic := (Polynomial.hermite_monic n).map (Int.castRingHom ℝ)
  simpa only [show hermiteSequence n = hermitePoly n from rfl, h.leadingCoeff] using
    (isUnit_one : IsUnit (1 : ℝ))

/-- The Hermite polynomials form a complete system in Gaussian L2. -/
theorem ae_eq_zero_of_integral_hermitePoly {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (horth : ∀ n, (∫ x, f x * (hermitePoly n).eval x ∂γ) = 0) : f =ᵐ[γ] 0 := by
  have hpoly (p : Polynomial ℝ) : (∫ x, f x * p.eval x ∂γ) = 0 := by
    have hp : p ∈ Submodule.span ℝ (range hermitePoly) := by rw [span_hermitePoly]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp => rcases hp with ⟨n, rfl⟩; exact horth n
    | zero => simp
    | add p q hp hq ihp ihq =>
      simp only [Polynomial.eval_add, mul_add]
      have hp' : Integrable (fun x => f x * p.eval x) γ :=
        hf.integrable_mul (memLp_polynomial_gaussianReal p)
      have hq' : Integrable (fun x => f x * q.eval x) γ :=
        hf.integrable_mul (memLp_polynomial_gaussianReal q)
      rw [integral_add hp' hq', ihp, ihq, add_zero]
    | smul a p hp ih =>
      simp only [Polynomial.eval_smul, smul_eq_mul]
      have he : (fun x => f x * (a * p.eval x)) = fun x => a * (f x * p.eval x) := by
        ext x; ring
      rw [he, integral_const_mul, ih, mul_zero]
  apply ae_eq_zero_of_gaussian_moments hf
  intro n
  simpa using hpoly (X ^ n)

theorem ae_eq_zero_of_integral_hermiteFunction {f : ℝ → ℝ} (hf : MemLp f 2 γ)
    (horth : ∀ n, (∫ x, f x * hermiteFunction n x ∂γ) = 0) : f =ᵐ[γ] 0 := by
  apply ae_eq_zero_of_integral_hermitePoly hf
  intro n
  have h := horth n
  simp only [hermiteFunction, ← mul_div_assoc, integral_div] at h
  exact (div_eq_zero_iff).mp h |>.resolve_right (by positivity)

end Submission.Lib.GaussianHermite
