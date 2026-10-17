import Submission.Obl.Entropy__affine_limit_density.MatrixCompact
import Submission.Obl.Entropy__affine_limit_density.L2Limits
import Submission.Obl.Entropy__affine_limit_density.WeakLaw

open MeasureTheory Filter
open scoped Topology Matrix

namespace Submission.Obl.Entropy__affine_limit_density

open Submission.Lib.EntropyTools

/-- Convert a nonsingular coordinate matrix into an equivalence of Euclidean spaces. -/
theorem exists_equiv_of_matrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.det ≠ 0) :
    ∃ P : E m ≃ₗ[ℝ] E m, linMatrix P.toLinearMap = A := by
  have hd : LinearMap.det (Matrix.toEuclideanLin A) ≠ 0 := by
    change LinearMap.det ((Matrix.toLpLin 2 2) A) ≠ 0
    rwa [Matrix.toLpLin_eq_toLin, LinearMap.det_toLin]
  refine ⟨(Matrix.toEuclideanLin A).equivOfDetNeZero hd, ?_⟩
  exact Matrix.toEuclideanLin.symm_apply_apply A

/-- Matrix convergence and convergence of the centers give pointwise affine convergence. -/
theorem tendsto_affine_of_matrix {m : ℕ} {Pn : ℕ → E m ≃ₗ[ℝ] E m}
    {P : E m ≃ₗ[ℝ] E m} {bn : ℕ → E m} {b : E m}
    (hP : Tendsto (fun n => linMatrix (Pn n).toLinearMap) atTop
      (𝓝 (linMatrix P.toLinearMap))) (hb : Tendsto bn atTop (𝓝 b)) (x : E m) :
    Tendsto (fun n => Pn n (x - bn n)) atTop (𝓝 (P (x - b))) := by
  have hc : Continuous (fun z : Matrix (Fin m) (Fin m) ℝ × E m =>
      Matrix.toEuclideanLin z.1 (x - z.2)) := by
    change Continuous (fun z : Matrix (Fin m) (Fin m) ℝ × E m =>
      WithLp.toLp 2 (z.1 *ᵥ (x - z.2).ofLp))
    apply (PiLp.continuous_toLp 2 _).comp
    apply Continuous.matrix_mulVec continuous_fst
    exact (PiLp.continuous_ofLp 2 _).comp (continuous_const.sub continuous_snd)
  have h := hc.tendsto (linMatrix P.toLinearMap, b) |>.comp (hP.prodMk_nhds hb)
  simpa only [Function.comp_def, linMatrix, LinearEquiv.apply_symm_apply,
    LinearEquiv.coe_coe] using h

/-- Compactness and the moment identity recover an invertible limiting affine law. -/
theorem exists_affine_limit_law {m : ℕ} [Nonempty (Fin m)]
    {μ : Measure (E m)} [IsFiniteMeasure μ]
    {f : E m → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {fn : ℕ → E m → ℝ} (hn0 : ∀ n x, 0 ≤ fn n x)
    (hn : ∀ n, Integrable (fn n) volume)
    (hn2 : ∀ n, Integrable (fun x => fn n x * ‖x‖ ^ 2) volume)
    {bn : ℕ → E m} {b : E m} (hb : Tendsto bn atTop (𝓝 b))
    {Cn : ℕ → Matrix (Fin m) (Fin m) ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hcovn : ∀ n, Cn n = densityCovariance (fn n) (bn n))
    (hC : C.PosDef) (hCn : Tendsto Cn atTop (𝓝 C))
    {Pn : ℕ → E m ≃ₗ[ℝ] E m} {Fn : ℕ → E m → E m} {F : E m → E m}
    (hFn : ∀ n, MemLp (Fn n) 2 μ) (hF : MemLp F 2 μ)
    (hL2 : Tendsto (fun n => ∫ x, ‖Fn n x - F x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ x, |fn n x - f x|) atTop (𝓝 0))
    (hlaw : ∀ n, Measure.map (Fn n) μ = Measure.map (fun x => Pn n (x - bn n))
      (volume.withDensity (fun x => ENNReal.ofReal (fn n x))))
    (hcov : (fun i j => ∫ x, F x i * F x j ∂μ) = (1 : Matrix (Fin m) (Fin m) ℝ)) :
    ∃ P : E m ≃ₗ[ℝ] E m, Measure.map F μ = Measure.map (fun x => P (x - b))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  let An := fun n => linMatrix (Pn n).toLinearMap
  have he (n : ℕ) (i j : Fin m) : (∫ x, Fn n x i * Fn n x j ∂μ) =
      (An n * Cn n * (An n).transpose) i j := by
    rw [hcovn n]
    exact covariance_of_map_eq (hn0 n) (hn n) (hn2 n) (bn n) (Pn n).toLinearMap
      (hFn n).aemeasurable (hlaw n) i j
  have hD : Tendsto (fun n => An n * Cn n * (An n).transpose) atTop
      (𝓝 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := tendsto_integral_observation_mul hFn hF hL2
      (EuclideanSpace.proj i) (EuclideanSpace.proj j)
    change Tendsto (fun n => ∫ x, Fn n x i * Fn n x j ∂μ) atTop
      (𝓝 (∫ x, F x i * F x j ∂μ)) at h
    simpa only [he, congrFun (congrFun hcov i) j] using h
  obtain ⟨A, hA, τ, hτ, hAlim⟩ := matrix_subsequence_nonsingular hC hCn hD
  obtain ⟨P, hP⟩ := exists_equiv_of_matrix A hA
  have hTlim (x : E m) : Tendsto (fun n => Pn (τ n) (x - bn (τ n))) atTop
      (𝓝 (P (x - b))) := by
    apply tendsto_affine_of_matrix _ (hb.comp hτ.tendsto_atTop)
    simpa only [hP, An, Function.comp_def] using hAlim
  obtain ⟨ρ, hρ, hae⟩ := exists_ae_subsequence_of_integral_sq (fun n => hFn (τ n)) hF
    (hL2.comp hτ.tendsto_atTop)
  refine ⟨P, map_eq_of_density_limits (fun n => hn0 (τ (ρ n))) (fun n => hn (τ (ρ n)))
    hf0 hf (hL1.comp (hτ.comp hρ).tendsto_atTop) ?_ ?_ ?_
    (fun n => (hFn (τ (ρ n))).aemeasurable) hF.aemeasurable hae (fun n => hlaw (τ (ρ n)))⟩
  · intro n
    exact (Pn (τ (ρ n))).toContinuousLinearEquiv.continuous.comp
      (continuous_id.sub continuous_const)
  · exact P.toContinuousLinearEquiv.continuous.comp (continuous_id.sub continuous_const)
  · intro x
    exact (hTlim x).comp hρ.tendsto_atTop

end Submission.Obl.Entropy__affine_limit_density
