import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.Pointwise

open scoped BigOperators Topology
open Matrix MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def entryPartial (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) : Matrix n n ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => A y i j) x (PiLp.single 2 r (1 : ℝ))

lemma entryPartial_isHermitian (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    (entryPartial A r x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, entryPartial, Matrix.of_apply]
  have heq : (fun y => A y j i) = (fun y => A y i j) := by
    funext y
    simpa only [star_trivial] using (hA y).apply i j
  rw [heq]

lemma measurable_entryPartial (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (r : Fin m) (i j : n) : Measurable (fun x => entryPartial A r x i j) :=
  measurable_fderiv_apply_const ℝ (fun y => A y i j) _

lemma linearPart_hasFDerivAt (X : Fin m → Matrix n n ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (i j : n) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => ∑ s, y s * X s i j)
      (∑ s, X s i j • PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin m => ℝ) s) x :=
  HasFDerivAt.fun_sum fun s _ => (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin m => ℝ) s).hasFDerivAt.mul_const _

lemma entryPartial_remainder (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j))
    (X : Fin m → Matrix n n ℝ) (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    entryPartial (fun y => A y - ∑ s, y s • X s) r x = entryPartial A r x - X r := by
  ext i j
  simp only [entryPartial, Matrix.of_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  erw [((hA i j x).hasFDerivAt.sub (linearPart_hasFDerivAt X x i j)).fderiv]
  simp [ContinuousLinearMap.sum_apply, PiLp.single_apply, PiLp.proj_apply]

noncomputable def firstResidual (k : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ) (X : Fin m → Matrix n n ℝ)
    (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) : Matrix n n ℝ :=
  entryPartial (fun y => cfc k (A y)) r x - X r * cfc (deriv k) (A x)

noncomputable def secondResidual (k : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ) (X : Fin m → Matrix n n ℝ)
    (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) : Matrix n n ℝ :=
  entryPartial (fun y => cfc (deriv k) (A y)) r x - X r * cfc (deriv (deriv k)) (A x)

noncomputable def scalarF (k : ℝ → ℝ) (a : ℝ) : ℝ := k a * (1 + deriv k a)
noncomputable def scalarP (k : ℝ → ℝ) (a : ℝ) : ℝ :=
  deriv (scalarF k) a - (deriv k a)^2 - (40/3)*(deriv (deriv k) a)^2
noncomputable def scalarE (k : ℝ → ℝ) (a : ℝ) : ℝ :=
  deriv (scalarF k) a - 2*(deriv k a)^2 - (80/3)*(deriv (deriv k) a)^2

noncomputable def thirdResidual (k : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix n n ℝ) (X : Fin m → Matrix n n ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin m) → Matrix n n ℝ)
    (r : Fin m) (x : EuclideanSpace ℝ (Fin m)) : Matrix n n ℝ :=
  entryPartial (fun y => cfc (scalarF k) (A y)) r x - X r * cfc (deriv (scalarF k)) (A x) -
    2 • (firstResidual k A X r x * cfc (deriv k) (A x)) -
    (80/3 : ℝ) • (secondResidual k A X r x * cfc (deriv (deriv k)) (A x)) +
    (3/2 : ℝ) • (g r x * cfc (deriv k) (A x))

noncomputable def dividedDiff (v : ℝ → ℝ) (a c : ℝ) : ℝ :=
  if a = c then deriv v c else (v a - v c)/(a-c)
noncomputable def deltaK (k : ℝ → ℝ) (a c : ℝ) : ℝ := dividedDiff k a c - deriv k c
noncomputable def deltaB (k : ℝ → ℝ) (a c : ℝ) : ℝ :=
  dividedDiff (deriv k) a c - deriv (deriv k) c
noncomputable def psi (k : ℝ → ℝ) (a c : ℝ) : ℝ :=
  dividedDiff (scalarF k) a c - deriv (scalarF k) c -
    2*deriv k c*deltaK k a c - (80/3)*deriv (deriv k) c*deltaB k a c

lemma dividedDiff_eq_dslope (v : ℝ → ℝ) (a c : ℝ) : dividedDiff v a c = dslope v a c := by
  by_cases h : a = c
  · subst c
    simp [dividedDiff, dslope_same]
  · rw [dividedDiff, if_neg h, dslope_of_ne v (Ne.symm h), slope_def_field]
    field_simp
    <;> ring

lemma scalarF_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ENat) k) :
    ContDiff ℝ (⊤ : ENat) (scalarF k) := by
  exact hk.mul (contDiff_const.add (contDiff_infty_iff_deriv.mp hk).2)

lemma scalarP_continuous {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ENat) k) :
    Continuous (scalarP k) := by
  have hb := (contDiff_infty_iff_deriv.mp hk).2
  have hl := (contDiff_infty_iff_deriv.mp hb).2
  have hf := (contDiff_infty_iff_deriv.mp (scalarF_smooth hk)).2
  exact (hf.continuous.sub (hb.continuous.pow 2)).sub
    (continuous_const.mul (hl.continuous.pow 2))

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
