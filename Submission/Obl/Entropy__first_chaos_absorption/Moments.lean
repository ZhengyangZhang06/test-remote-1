import Submission.Obl.Entropy__centered_slack_transports.Fields

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

lemma coord_memLp (r : Fin m) :
    MemLp (fun x : EuclideanSpace ℝ (Fin m) => x r) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) r).comp_memLp' IsGaussian.memLp_two_id

lemma coord_second_moment (r s : Fin m) :
    (∫ x : EuclideanSpace ℝ (Fin m), x r * x s
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = if r = s then 1 else 0 := by
  have hc := congrArg
    (fun C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ =>
      C (EuclideanSpace.basisFun (Fin m) ℝ r) (EuclideanSpace.basisFun (Fin m) ℝ s))
    (covarianceBilin_stdGaussian (E := EuclideanSpace ℝ (Fin m)))
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at hc
  change (∫ z : EuclideanSpace ℝ (Fin m),
    inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ r) (z - ∫ y, y ∂stdGaussian (EuclideanSpace ℝ (Fin m))) *
      inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ s) (z - ∫ y, y ∂stdGaussian (EuclideanSpace ℝ (Fin m)))
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
    inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ r) (EuclideanSpace.basisFun (Fin m) ℝ s) at hc
  simpa [integral_id_stdGaussian, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, PiLp.single_apply, eq_comm] using hc

noncomputable def scalarCoeff (f : EuclideanSpace ℝ (Fin m) → ℝ) (r : Fin m) : ℝ :=
  ∫ x, x r * f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))

noncomputable def scalarLinear (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := ∑ r, x r * scalarCoeff f r

lemma scalarLinear_memLp (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    MemLp (scalarLinear f) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  exact memLp_finsetSum _ fun r _ => (coord_memLp r).mul_const _

lemma integral_coord_scalarLinear (f : EuclideanSpace ℝ (Fin m) → ℝ) (r : Fin m) :
    (∫ x, x r * scalarLinear f x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      scalarCoeff f r := by
  simp only [scalarLinear, Finset.mul_sum, ← mul_assoc]
  rw [integral_finsetSum]
  · simp only [integral_mul_const, coord_second_moment]
    simp
  · intro s _
    exact ((coord_memLp r).integrable_mul (coord_memLp s)).mul_const _

lemma integral_scalarLinear_mul (f g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) :
    (∫ x, scalarLinear f x * g x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∑ r, scalarCoeff f r * scalarCoeff g r := by
  simp only [scalarLinear, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    change (∫ x, x r * scalarCoeff f r * g x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = _
    rw [show (fun x => x r * scalarCoeff f r * g x) =
      (fun x => scalarCoeff f r * (x r * g x)) by funext x; ring, integral_const_mul]
    rfl
  · intro r _
    exact ((coord_memLp r).mul_const _).integrable_mul hg

lemma scalarCoeff_linear (f : EuclideanSpace ℝ (Fin m) → ℝ) (r : Fin m) :
    scalarCoeff (scalarLinear f) r = scalarCoeff f r :=
  integral_coord_scalarLinear f r

lemma scalar_second_moment (f g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hg : MemLp g 2 (stdGaussian (EuclideanSpace ℝ (Fin m)))) :
    (∫ x, f x * g x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      (∑ r, scalarCoeff f r * scalarCoeff g r) +
        ∫ x, (f x - scalarLinear f x) * (g x - scalarLinear g x)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  have hLf := scalarLinear_memLp f
  have hLg := scalarLinear_memLp g
  have hfg := hf.integrable_mul hg
  have hLfg := hLf.integrable_mul hg
  have hfLg := hf.integrable_mul hLg
  have hLfLg := hLf.integrable_mul hLg
  have he : (fun x => (f x - scalarLinear f x) * (g x - scalarLinear g x)) =
      fun x => f x * g x - scalarLinear f x * g x - f x * scalarLinear g x +
        scalarLinear f x * scalarLinear g x := by funext x; ring
  rw [he, integral_add (f := fun x => f x * g x - scalarLinear f x * g x - f x * scalarLinear g x)
      (g := fun x => scalarLinear f x * scalarLinear g x) ((hfg.sub hLfg).sub hfLg) hLfLg,
    integral_sub (f := fun x => f x * g x - scalarLinear f x * g x)
      (g := fun x => f x * scalarLinear g x) (hfg.sub hLfg) hfLg,
    integral_sub (f := fun x => f x * g x) (g := fun x => scalarLinear f x * g x) hfg hLfg,
    integral_scalarLinear_mul f g hg,
    integral_scalarLinear_mul f (scalarLinear g) hLg]
  simp_rw [scalarCoeff_linear]
  have he' : (∫ x, f x * scalarLinear g x ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      ∑ r, scalarCoeff f r * scalarCoeff g r := by
    simp_rw [mul_comm (f _) (scalarLinear g _)]
    rw [integral_scalarLinear_mul g f hf]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he']
  ring

noncomputable def momentCoefficient
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) (r : Fin m) :
    Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => scalarCoeff (fun x => A x i j) r

noncomputable def momentRemainder
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  A x - ∑ r, x r • momentCoefficient A r

lemma momentRemainder_apply
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :
    momentRemainder A x i j = A x i j - scalarLinear (fun x => A x i j) x := by
  simp [momentRemainder, momentCoefficient, scalarLinear, Matrix.sum_apply]

lemma momentRemainder_memLp
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (i j : Fin m) :
    MemLp (fun x => momentRemainder A x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have he : (fun x => momentRemainder A x i j) =
      ((fun x => A x i j) - scalarLinear (fun x => A x i j)) := by
    funext x
    exact momentRemainder_apply A x i j
  rw [he]
  exact (hA i j).sub (scalarLinear_memLp (fun x => A x i j))

lemma matrix_square_integrable
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (i j : Fin m) :
    Integrable (fun x => (A x * A x) i j) (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun r _ => (hA i r).integrable_mul (hA r j)

lemma moment_matrix_second
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (i j : Fin m) :
    (∫ x, (A x * A x) i j ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      (∑ r, momentCoefficient A r * momentCoefficient A r) i j +
        ∫ x, (momentRemainder A x * momentRemainder A x) i j
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  rw [integral_finsetSum (f := fun k x => A x i k * A x k j) _ (fun k _ => (hA i k).integrable_mul (hA k j)),
    integral_finsetSum (f := fun k x => momentRemainder A x i k * momentRemainder A x k j) _ (fun k _ => (momentRemainder_memLp A hA i k).integrable_mul
      (momentRemainder_memLp A hA k j))]
  simp_rw [momentRemainder_apply]
  simp_rw [scalar_second_moment _ _ (hA i _) (hA _ j)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  rfl

lemma momentCoefficient_isHermitian
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).IsHermitian) (r : Fin m) :
    (momentCoefficient A r).IsHermitian := by
  exact Submission.Obl.Entropy__centered_slack_transports.coefficient_isHermitian A hA r

lemma momentRemainder_isHermitian
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).IsHermitian) (x : EuclideanSpace ℝ (Fin m)) :
    (momentRemainder A x).IsHermitian := by
  apply (hA x).sub
  rw [Matrix.IsHermitian]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
  apply Finset.sum_congr rfl
  intro r _
  rw [(momentCoefficient_isHermitian A hA r).eq]

end Submission.Obl.Entropy__first_chaos_absorption
