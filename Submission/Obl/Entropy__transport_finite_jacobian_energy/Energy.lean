import Submission.Obl.Entropy__transport_finite_jacobian_energy.Cutoff

set_option autoImplicit false
set_option maxHeartbeats 200000

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma integrable_of_cutoff_bounds {E : space m → ℝ} (hE : Continuous E)
    (hE0 : ∀ x, 0 ≤ E x) {χ : ℕ → space m → ℝ}
    (hχ : ∀ n, Continuous (χ n) ∧ HasCompactSupport (χ n))
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    {C : ℝ} (hbound : ∀ n, (∫ x, (χ n x)^2 * E x ∂stdGaussian (space m)) ≤ C) :
    Integrable E (stdGaussian (space m)) := by
  let f (n : ℕ) (x : space m) := (χ n x)^2 * E x
  have hfi (n : ℕ) : Integrable (f n) (stdGaussian (space m)) := by
    apply ((hχ n).1.pow 2 |>.mul hE).integrable_of_hasCompactSupport
    apply (hχ n).2.mono
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro hz
    exact hx (by simp [hz])
  have hf0 (n : ℕ) (x : space m) : 0 ≤ f n x := mul_nonneg (sq_nonneg _) (hE0 x)
  have hLp : eLpNorm E 1 (stdGaussian (space m)) ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto (f := f) (u := (atTop : Filter ℕ))
    · apply Eventually.of_forall
      intro n
      rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hfi n)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 n _)] using hbound n
    · exact fun n => (hfi n).aestronglyMeasurable
    · apply ae_of_all
      intro x
      simpa [f] using ((hlim x).pow 2).mul_const (E x)
  exact memLp_one_iff_integrable.mp
    ⟨hE.aestronglyMeasurable, hLp.trans_lt ENNReal.ofReal_lt_top⟩

lemma compact_energy_bound {E S : space m → ℝ} {b : Fin m → space m → ℝ}
    (hE : Continuous E) (hS : Continuous S) (hb : ∀ s, Continuous (b s))
    {c B a D : ℝ} (hc : 0 < c) (hB : 0 < B) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hsource : ∀ x, c * E x - a ≤ S x)
    (hflux : ∀ x, (∑ s, (b s x)^2) ≤ B * E x)
    {χ : space m → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχD : ∀ x s, |directional (basisVector s) χ x| ≤ D)
    (hweak : (∫ x, (χ x)^2 * S x ∂stdGaussian (space m)) =
      -(∑ s, ∫ x, 2 * χ x * directional (basisVector s) χ x * b s x
        ∂stdGaussian (space m))) :
    (∫ x, (χ x)^2 * E x ∂stdGaussian (space m)) ≤
      (2 / c) * (a + (c / (2 * B))⁻¹ * ((m : ℝ) * D^2)) := by
  let t := c / (2 * B)
  have ht : 0 < t := div_pos hc (mul_pos (by norm_num) hB)
  let C := t⁻¹ * ((m : ℝ) * D^2)
  let f (s : Fin m) (x : space m) :=
    2 * χ x * directional (basisVector s) χ x * b s x
  have hfi (s : Fin m) : Integrable (f s) (stdGaussian (space m)) :=
    (((continuous_const.mul hχ.continuous).mul
      (contDiff_directional hχ _).continuous).mul (hb s)).integrable_of_hasCompactSupport
      ((hχK.mul_left.mul_right).mul_right)
  have hχ2 : HasCompactSupport (fun x => (χ x)^2) := by
    apply hχK.mono
    intro x hx
    simpa only [Function.mem_support, ne_eq, pow_eq_zero_iff (by omega : 2 ≠ 0)] using hx
  have hEI : Integrable (fun x => (χ x)^2 * E x) (stdGaussian (space m)) :=
    ((hχ.continuous.pow 2).mul hE).integrable_of_hasCompactSupport hχ2.mul_right
  have hSI : Integrable (fun x => (χ x)^2 * S x) (stdGaussian (space m)) :=
    ((hχ.continuous.pow 2).mul hS).integrable_of_hasCompactSupport
      hχ2.mul_right
  have hp (x : space m) :
      (c / 2) * ((χ x)^2 * E x) ≤ a + C + (χ x)^2 * S x + ∑ s, f s x := by
    have hy (s : Fin m) : -f s x ≤
        t * (χ x)^2 * (b s x)^2 + t⁻¹ * (directional (basisVector s) χ x)^2 := by
      have hy := two_mul_le_add_mul_sq (a := χ x * b s x)
        (b := -directional (basisVector s) χ x) ht
      dsimp [f]
      nlinarith
    have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hy s)
    have hg : (∑ s, (directional (basisVector s) χ x)^2) ≤ (m : ℝ) * D^2 := by
      calc
        _ ≤ ∑ _s : Fin m, D^2 := Finset.sum_le_sum fun s _ => by
          nlinarith [sq_nonneg (D - |directional (basisVector s) χ x|),
            sq_abs (directional (basisVector s) χ x), hχD x s,
            abs_nonneg (directional (basisVector s) χ x)]
        _ = _ := by simp
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hsum
    have hflux' := mul_le_mul_of_nonneg_left (hflux x) (mul_nonneg ht.le (sq_nonneg (χ x)))
    have hg' := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr ht.le)
    have hsrc := mul_le_mul_of_nonneg_left (hsource x) (sq_nonneg (χ x))
    have hχsq : (χ x)^2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
    have ha' := mul_le_mul_of_nonneg_left hχsq ha
    have htB : t * B = c / 2 := by dsimp [t]; field_simp
    have hrewrite : t * (χ x)^2 * (B * E x) = (c / 2) * ((χ x)^2 * E x) := by
      calc
        _ = (t * B) * ((χ x)^2 * E x) := by ring
        _ = _ := by rw [htB]
    rw [hrewrite] at hflux'
    dsimp [C]
    nlinarith
  have hright : Integrable (fun x => a + C + (χ x)^2 * S x + ∑ s, f s x)
      (stdGaussian (space m)) :=
    ((integrable_const (a + C)).add hSI).add (integrable_finsetSum _ (fun s _ => hfi s))
  have hi := integral_mono (hEI.const_mul (c / 2)) hright hp
  erw [integral_const_mul, integral_add ((integrable_const _).add hSI)
    (integrable_finsetSum _ (fun s _ => hfi s)),
    integral_add (integrable_const _) hSI, integral_finsetSum _ (fun s _ => hfi s)] at hi
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hi
  change (c / 2) * (∫ x, (χ x)^2 * E x ∂stdGaussian (space m)) ≤
    a + C + (∫ x, (χ x)^2 * S x ∂stdGaussian (space m)) + ∑ s, ∫ x, f s x ∂stdGaussian (space m) at hi
  rw [hweak] at hi
  have hcancel : (2 / c) * (c / 2) = (1 : ℝ) := by field_simp
  have hi0 : (c / 2) * (∫ x, (χ x)^2 * E x ∂stdGaussian (space m)) ≤ a + C := by
    simpa only [f, add_assoc, neg_add_cancel, add_zero] using hi
  calc
    _ = (2 / c) * ((c / 2) * (∫ x, (χ x)^2 * E x ∂stdGaussian (space m))) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi0 (le_of_lt (div_pos (by norm_num) hc))

/-- A coercive compact-test equation forces finite energy, without any prior
integrability assumption on the energy or the flux. -/
lemma energy_integrable_of_weak {E S : space m → ℝ} {b : Fin m → space m → ℝ}
    (hE : Continuous E) (hE0 : ∀ x, 0 ≤ E x)
    (hS : Continuous S) (hb : ∀ s, Continuous (b s))
    {c B a : ℝ} (hc : 0 < c) (hB : 0 < B) (ha : 0 ≤ a)
    (hsource : ∀ x, c * E x - a ≤ S x)
    (hflux : ∀ x, (∑ s, (b s x)^2) ≤ B * E x)
    (hweak : ∀ z : space m → ℝ, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∫ x, z x * S x ∂stdGaussian (space m)) =
        -(∑ s, ∫ x, directional (basisVector s) z x * b s x ∂stdGaussian (space m))) :
    Integrable E (stdGaussian (space m)) := by
  obtain ⟨χ, D, hD, hχ, hχ01, hχD, hχlim⟩ := exists_energy_cutoffs (m := m)
  apply integrable_of_cutoff_bounds hE hE0
    (fun n => ⟨(hχ n).1.continuous, (hχ n).2⟩) hχlim
  intro n
  apply compact_energy_bound hE hS hb hc hB ha hD hsource hflux
    (hχ n).1 (hχ n).2 (fun x => (hχ01 n x).1) (fun x => (hχ01 n x).2) (hχD n)
  have hK : HasCompactSupport (fun x => (χ n x)^2) := by
    apply (hχ n).2.mono
    intro x hx
    simpa only [Function.mem_support, ne_eq, pow_eq_zero_iff (by omega : 2 ≠ 0)] using hx
  have hw := hweak (fun x => (χ n x)^2) ((hχ n).1.pow 2) hK
  rw [hw]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hd : directional (basisVector s) (fun y => (χ n y)^2) x =
      2 * χ n x * directional (basisVector s) (χ n) x := by
    rw [show (fun y => (χ n y)^2) = (fun y => χ n y * χ n y) by funext y; ring]
    rw [directional_mul ((hχ n).1.differentiable (by simp) x)
      ((hχ n).1.differentiable (by simp) x)]
    ring
  dsimp only
  rw [hd]

end Submission.Obl.Entropy__transport_finite_jacobian_energy
