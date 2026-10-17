import Submission.Obl.Entropy__linear_transport_limit.Fields

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Submission.Obl.Entropy__linear_transport_limit

section Normed
variable {α B : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup B]

theorem norm_sub_sq_triangle (x y z : B) :
    ‖x - z‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
  have ht : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    simpa only [dist_eq_norm] using dist_triangle x y z
  have hs : ‖x - z‖ ^ 2 ≤ (‖x - y‖ + ‖y - z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
  nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖)]

theorem integral_norm_sub_sq_triangle {f g h : α → B}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    (∫ x, ‖f x - h x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x - g x‖ ^ 2 ∂μ) + 2 * ∫ x, ‖g x - h x‖ ^ 2 ∂μ := by
  have hfg : Integrable (fun x => ‖f x - g x‖ ^ 2) μ := (hf.sub hg).norm.integrable_sq
  have hgh : Integrable (fun x => ‖g x - h x‖ ^ 2) μ := (hg.sub hh).norm.integrable_sq
  calc
    _ ≤ ∫ x, 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x - h x‖ ^ 2 ∂μ := by
      apply integral_mono (hf.sub hh).norm.integrable_sq
        ((hfg.const_mul 2).add (hgh.const_mul 2))
      exact fun x => norm_sub_sq_triangle _ _ _
    _ = _ := by
      rw [integral_add (hfg.const_mul 2) (hgh.const_mul 2),
        integral_const_mul, integral_const_mul]

theorem tendsto_energy_triangle {f g : ℕ → α → B} {h : α → B}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ) (hh : MemLp h 2 μ)
    (hfg : Tendsto (fun n => ∫ x, ‖f n x - g n x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hgh : Tendsto (fun n => ∫ x, ‖g n x - h x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x - h x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => integral_norm_sub_sq_triangle (hf n) (hg n) hh)
  simpa using (hfg.const_mul 2).add (hgh.const_mul 2)

end Normed

/-- Reassemble matrix coordinates as a continuous linear endomorphism. -/
noncomputable def entriesCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m) →L[ℝ] (E m →L[ℝ] E m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun (a : EuclideanSpace ℝ (Fin m × Fin m)) =>
        Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (fun i j => a (i, j))
      map_add' := by
        intro a b
        exact map_add (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) _ _
      map_smul' := by
        intro c a
        exact map_smul (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).toAlgEquiv.toLinearMap c _ }

@[simp] theorem entriesCLM_apply {m : ℕ} (A : Mat m) (v : E m) (i : Fin m) :
    entriesCLM m (entries A) v i = ∑ j, A i j * v j := rfl

/-- The Jacobian entries are continuous even when no continuity of the input matrix field
is assumed: they are coordinates of the derivative of a C1 map. -/
theorem continuous_jacobian_entries {m : ℕ} {q : ℝ → ℝ} {F : E m → E m}
    {A : E m → Mat m} (hF : ContDiff ℝ 1 F)
    (hderiv : ∀ x v i, (fderiv ℝ F x v) i = ∑ j, cfc q (A x) i j * v j) :
    Continuous (fun x => entries (cfc q (A x))) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  have heq : (fun x => cfc q (A x) p.1 p.2) =
      (fun x => (fderiv ℝ F x (PiLp.single 2 p.2 (1 : ℝ))) p.1) := by
    funext x
    rw [hderiv]
    simp
  change Continuous (fun x => cfc q (A x) p.1 p.2)
  rw [heq]
  exact (EuclideanSpace.proj (𝕜 := ℝ) p.1).continuous.comp
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- Passing a Gaussian L2 limit through a fixed continuous linear map. -/
theorem tendsto_energy_clm {α B C : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : B →L[ℝ] C) {f : ℕ → α → B} {g : α → B}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hfg : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖L (f n x) - L (g x)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (g := fun n => ‖L‖ ^ 2 * ∫ x, ‖f n x - g x‖ ^ 2 ∂μ)
  · intro n
    rw [← integral_const_mul]
    apply integral_mono
      (((hf n).continuousLinearMap_comp L).sub (hg.continuousLinearMap_comp L)).norm.integrable_sq
      (((hf n).sub hg).norm.integrable_sq.const_mul _)
    intro x
    simp only [Pi.sub_apply]
    rw [← map_sub, ← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (L.le_opNorm _)
  · simpa using hfg.const_mul (‖L‖ ^ 2)

variable {m : ℕ} {q : ℝ → ℝ}
variable (hq : ∀ U V : Mat m, U.IsHermitian → V.IsHermitian →
  (∑ i, ∑ j, (cfc q U i j - cfc q V i j) ^ 2) ≤
    ∑ i, ∑ j, (U i j - V i j) ^ 2)

include hq

theorem integral_cfc_energy_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : α → Mat m} (hA : ∀ x, (A x).IsHermitian) (hB : ∀ x, (B x).IsHermitian)
    (hAmem : MemLp (fun x => entries (A x)) 2 μ)
    (hBmem : MemLp (fun x => entries (B x)) 2 μ)
    (hJAmem : MemLp (fun x => entries (cfc q (A x))) 2 μ)
    (hJBmem : MemLp (fun x => entries (cfc q (B x))) 2 μ) :
    (∫ x, ‖entries (cfc q (A x)) - entries (cfc q (B x))‖ ^ 2 ∂μ) ≤
      ∫ x, ‖entries (A x) - entries (B x)‖ ^ 2 ∂μ := by
  apply integral_mono (hJAmem.sub hJBmem).norm.integrable_sq
    (hAmem.sub hBmem).norm.integrable_sq
  intro x
  simp only [Pi.sub_apply, ← entries_sub, norm_entries_sq, Matrix.sub_apply]
  exact hq _ _ (hA x) (hB x)

/-- From coefficient convergence and the vanishing remainder to convergence of the actual
Jacobians. This is the field-to-derivative part of Section 6. -/
theorem jacobian_entries_limit
    {Fseq : ℕ → E m → E m} {Aseq : ℕ → E m → Mat m}
    {Xseq : ℕ → Fin m → Mat m} {X : Fin m → Mat m}
    (hF : ∀ n, ContDiff ℝ 1 (Fseq n))
    (hA : ∀ n, (∀ x, (Aseq n x).IsHermitian) ∧
      (∀ i j, MemLp (fun x => Aseq n x i j) 2 (stdGaussian (E m))))
    (hderiv : ∀ n x v i, (fderiv ℝ (Fseq n) x v) i =
      ∑ j, cfc q (Aseq n x) i j * v j)
    (hrem : Tendsto (fun n => ∫ x : E m,
      ∑ i, ∑ j, (Aseq n x i j - ∑ r, x r * Xseq n r i j) ^ 2
        ∂stdGaussian (E m)) atTop (𝓝 0))
    (hX : Tendsto Xseq atTop (𝓝 X)) (hXherm : ∀ r, (X r).IsHermitian) :
    let Jseq := fun n (x : E m) => entries (cfc q (Aseq n x))
    let J := fun x : E m => entries (cfc q (linearField X x))
    (∀ n, MemLp (Jseq n) 2 (stdGaussian (E m))) ∧
      Continuous J ∧ MemLp J 2 (stdGaussian (E m)) ∧
      Tendsto (fun n => ∫ x : E m, ‖Jseq n x - J x‖ ^ 2
        ∂stdGaussian (E m)) atTop (𝓝 0) := by
  dsimp only
  have hAlp : ∀ n, MemLp (fun x => entries (Aseq n x)) 2 (stdGaussian (E m)) :=
    fun n => memLp_entries (hA n).2
  have hJlp : ∀ n, MemLp (fun x => entries (cfc q (Aseq n x))) 2
      (stdGaussian (E m)) := fun n =>
    memLp_cfc_entries hq (hA n).1 (hAlp n)
      (continuous_jacobian_entries (hF n) (hderiv n)).aestronglyMeasurable
  have hJlim := memLp_cfc_linearField hq hXherm
  have hfield : Tendsto (fun n => ∫ x : E m,
      ‖entries (Aseq n x) - entries (linearField X x)‖ ^ 2
        ∂stdGaussian (E m)) atTop (𝓝 0) := by
    apply tendsto_energy_triangle hAlp (fun n => memLp_linearField (Xseq n))
      (memLp_linearField X) _ (tendsto_linearField_energy hX)
    simpa only [← entries_sub, norm_entries_sq, Matrix.sub_apply, linearField_apply] using hrem
  have hJfield : Tendsto (fun n => ∫ x : E m,
      ‖entries (cfc q (Aseq n x)) - entries (cfc q (linearField X x))‖ ^ 2
        ∂stdGaussian (E m)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) _ hfield
    exact fun n => integral_cfc_energy_le hq (hA n).1 (linearField_hermitian hXherm)
      (hAlp n) (memLp_linearField X) (hJlp n) hJlim
  exact ⟨hJlp, (lipschitz_cfc_linearField hq hXherm).continuous, hJlim, hJfield⟩

end Submission.Obl.Entropy__linear_transport_limit
