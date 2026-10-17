import Submission.Obl.Entropy__transport_finite_jacobian_energy.Determinant

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise ContDiff

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation in a fixed, constant direction. -/
noncomputable def directional (v : E) (f : E → F) (x : E) : F := fderiv ℝ f x v

lemma contDiff_directional {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (directional v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma directional_twice {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional v (directional w f) x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

lemma directional_comm {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional v (directional w f) x = directional w (directional v f) x := by
  rw [directional_twice hf, directional_twice hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ENat) : WithTop ENat) ≤ (⊤ : ENat)
    exact WithTop.coe_le_coe.mpr le_top) v w

lemma directional_sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    {x : E} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (v : E) :
    directional v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, directional v (f i) x := by
  simp only [directional, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]

lemma directional_mul {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    directional v (fun y => f y * g y) x =
      directional v f x * g x + f x * directional v g x := by
  simp only [directional, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma directional_sub {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    directional v (fun y => f y - g y) x = directional v f x - directional v g x := by
  simp only [directional, fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma differentiableAt_matrix_entry {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (i j : ι) :
    DifferentiableAt ℝ (fun y => A y i j) x :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j

lemma directional_matrix_entry {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (i j : ι) (v : E) :
    directional v (fun y => A y i j) x = directional v A x i j := by
  dsimp [directional]
  rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i]
  rfl

lemma differentiableAt_matrix_mul {A B : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => A y * B y) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun y => ∑ k, A y i k * B y k j) x
  exact DifferentiableAt.fun_sum fun k _ =>
    (differentiableAt_matrix_entry hA i k).mul (differentiableAt_matrix_entry hB k j)

lemma directional_matrix_mul {A B : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : E) :
    directional v (fun y => A y * B y) x =
      directional v A x * B x + A x * directional v B x := by
  ext i j
  rw [← directional_matrix_entry (differentiableAt_matrix_mul hA hB) i j]
  simp only [Matrix.mul_apply, Matrix.add_apply]
  erw [directional_sum Finset.univ (fun k _ =>
    (differentiableAt_matrix_entry hA i k).mul (differentiableAt_matrix_entry hB k j))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change directional v (fun y => A y i k * B y k j) x = _
  erw [directional_mul (differentiableAt_matrix_entry hA i k)
    (differentiableAt_matrix_entry hB k j)]
  erw [directional_matrix_entry hA, directional_matrix_entry hB]

lemma directional_matrix_trace {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    directional v (fun y => (A y).trace) x = (directional v A x).trace := by
  simp only [Matrix.trace, Matrix.diag]
  rw [directional_sum Finset.univ (fun i _ => differentiableAt_matrix_entry hA i i)]
  simp_rw [directional_matrix_entry hA]

lemma directional_matrix_inv {A : E → Matrix ι ι ℝ}
    (hA : ContDiff ℝ 1 A) (hinv : ∀ x, (A x).det ≠ 0) (v x : E) :
    directional v (fun y => (A y)⁻¹) x =
      -(A x)⁻¹ * directional v A x * (A x)⁻¹ := by
  have hAi := (contDiff_matrix_inv hA hinv).differentiable one_ne_zero x
  have hAd := hA.differentiable one_ne_zero x
  have hid : (fun y => (A y)⁻¹ * A y) = fun _ : E => (1 : Matrix ι ι ℝ) := by
    funext y
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hinv y))
  have hz := directional_matrix_mul hAi hAd v
  rw [hid] at hz
  dsimp only [directional] at hz
  erw [fderiv_const] at hz
  change (0 : Matrix ι ι ℝ) = _ at hz
  have hz' := congrArg (fun M : Matrix ι ι ℝ => M * (A x)⁻¹) hz
  rw [Matrix.zero_mul, Matrix.add_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv x)), Matrix.mul_one] at hz'
  change _ = -(A x)⁻¹ * directional v A x * (A x)⁻¹
  rw [neg_mul, neg_mul]
  exact eq_neg_of_add_eq_zero_left hz'.symm

end Submission.Obl.Entropy__transport_finite_jacobian_energy
