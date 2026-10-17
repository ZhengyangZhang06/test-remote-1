import Submission.Obl.Entropy__smooth_gaussian_transport.LocalizedEquation
import Submission.Obl.Entropy__smooth_gaussian_transport.UniformBoundedHolder
import Submission.Obl.Entropy__smooth_gaussian_transport.SmallHolderScale

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem uniformBoundedHolder_localizedRhs {ι : Type*} {m : ℕ}
    {χ : E m → ℝ} {u f : ι → E m → ℝ}
    {T : ι → E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ} {α : ℝ}
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hu : UniformBoundedHolder α u)
    (hDu : UniformBoundedHolder α (fun i => fderiv ℝ (u i)))
    (hf : UniformBoundedHolder α f) (hT : UniformBoundedHolder α T) :
    UniformBoundedHolder α (fun i => localizedRhs χ (u i) (f i) (T i)) := by
  have h0 : UniformBoundedHolder α (fun (_ : ι) => χ) :=
    UniformBoundedHolder.of_compact_c1 (hχ.of_le (by norm_num)) hχc hα hα1
  have h1 : UniformBoundedHolder α (fun (_ : ι) => fderiv ℝ χ) :=
    UniformBoundedHolder.of_compact_c1 (hχ.fderiv_right (by norm_num)) (hχc.fderiv ℝ) hα hα1
  have h2 : UniformBoundedHolder α (fun (_ : ι) => iteratedFDeriv ℝ 2 χ) :=
    UniformBoundedHolder.of_compact_c1 (hχ.iteratedFDeriv_right (by norm_num)) (hχc.iteratedFDeriv 2) hα hα1
  have hcross : UniformBoundedHolder α (fun i x => productHessianCross (fderiv ℝ χ x) (fderiv ℝ (u i) x)) := by
    exact ((h1.smulRight hDu).add (hDu.smulRight h1)).mapLIE (hessianCurry (E m) ℝ).symm
  have hlap : UniformBoundedHolder α (fun (_ : ι) => laplacian χ) := by
    convert! h2.mapCLM (hessianTrace m) using 1
    funext i x
    exact laplacian_eq_hessianTrace (hχ.of_le (by norm_num)) x
  exact ((h0.smul hf).add (hu.smul (hlap.sub (hT.clm_apply h2)))).add
    (((UniformBoundedHolder.constant α (hessianTrace m)).sub hT).clm_apply hcross)

/-- A single smallness threshold for the principal coefficient yields uniform
interior Schauder bounds for an arbitrary family of solutions. -/
theorem exists_localized_schauder_threshold (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {ι : Type*} (χ : E m → ℝ) (u f : ι → E m → ℝ)
      (T : ι → E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ),
      ContDiff ℝ 3 χ → HasCompactSupport χ → (∀ i, ContDiff ℝ 2 (u i)) →
      UniformBoundedHolder α u → UniformBoundedHolder α (fun i => fderiv ℝ (u i)) →
      UniformBoundedHolder α f → UniformBoundedHolder α T →
      (∀ i x, ‖T i x‖ ≤ ε) →
      (∀ i x, χ x ≠ 0 → laplacian (u i) x = f i x + T i x (iteratedFDeriv ℝ 2 (u i) x)) →
      (∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
        ‖iteratedFDeriv ℝ 2 (fun z => χ z * u i z) x - iteratedFDeriv ℝ 2 (fun z => χ z * u i z) y‖ ≤
          C * ‖x - y‖ ^ α) →
      UniformBoundedHolder α (fun i => iteratedFDeriv ℝ 2 (fun z => χ z * u i z)) := by
  obtain ⟨K, hK, hS⟩ := exists_laplacian_schauder_constant m hα hα1
  refine ⟨1 / (4 * K), by positivity, ?_⟩
  intro ι χ u f T hχ hχc hureg hu hDu hf hT hsmall heq hex
  have hχ0 : UniformBoundedHolder α (fun (_ : ι) => χ) :=
    UniformBoundedHolder.of_compact_c1 (hχ.of_le (by norm_num)) hχc hα hα1.le
  have hχ1 : UniformBoundedHolder α (fun (_ : ι) => fderiv ℝ χ) :=
    UniformBoundedHolder.of_compact_c1 (hχ.fderiv_right (by norm_num)) (hχc.fderiv ℝ) hα hα1.le
  have hF : UniformBoundedHolder α (fun i x => χ x * u i x) := hχ0.smul hu
  have hDF : UniformBoundedHolder α (fun i => fderiv ℝ (fun x => χ x * u i x)) := by
    convert! (hχ0.smul hDu).add (hu.smul hχ1) using 1
    funext i x
    exact fderiv_fun_mul (hχ.differentiable (by norm_num) x) ((hureg i).differentiable (by norm_num) x)
  obtain ⟨M, CM, hM, hCM, hb, hm⟩ := hF
  obtain ⟨N, CN, hN, hCN, hdb, hdm⟩ := hDF
  obtain ⟨G₀, G, hG₀, hG, hgb, hgm⟩ := uniformBoundedHolder_localizedRhs hχ hχc hα hα1.le hu hDu hf hT
  obtain ⟨MT, L, hMT, hL, htb, htm⟩ := hT
  obtain ⟨t, ht, hst⟩ := exists_small_holder_scale hα (by norm_num : (0 : ℝ) < 1 / 4) (K * L)
  have hsmall' : K * (1 / (4 * K) + L * t ^ α) ≤ 1 / 2 := by
    have he : K * (1 / (4 * K)) = 1 / 4 := by field_simp
    rw [mul_add, he]
    nlinarith
  let C : ℝ := 2 * K * (M + G + 2 * L * N / t)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmod (i : ι) : ∀ x y,
      ‖iteratedFDeriv ℝ 2 (fun z => χ z * u i z) x - iteratedFDeriv ℝ 2 (fun z => χ z * u i z) y‖ ≤
        C * ‖x - y‖ ^ α :=
    perturbed_laplacian_schauder hα hα1 hK hS ((hχ.of_le (by norm_num)).mul (hureg i))
      hχc.mul_right hM hN hG (by positivity) hL ht hsmall' (hb i) (hdb i)
      (hsmall i) (htm i) (fun x y => by simpa only [Real.norm_eq_abs] using hgm i x y)
      (localized_laplacian_equation (hχ.of_le (by norm_num)) (hureg i) (heq i)) (hex i)
  refine ⟨2 * N + C, C, by positivity, hC, ?_, hmod⟩
  intro i x
  have hd : Differentiable ℝ (fderiv ℝ (fun z => χ z * u i z)) :=
    (((hχ.of_le (by norm_num : (2 : WithTop ENat) ≤ 3)).mul (hureg i)).fderiv_right
      (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)).differentiable_one
  have hh := derivative_holder_interpolation hd hN hC hα.le (by norm_num : (0 : ℝ) < 1) (hdb i)
    (fun x y => by rw [norm_second_fderiv_sub]; exact hmod i x y) x
  simpa only [norm_second_fderiv, div_one, Real.one_rpow, mul_one] using hh

end Submission.Obl.Entropy__smooth_gaussian_transport
