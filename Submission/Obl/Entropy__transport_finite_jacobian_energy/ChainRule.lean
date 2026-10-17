import Submission.Obl.Entropy__transport_finite_jacobian_energy.Hessian

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.Elementwise ContDiff

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma clm_apply_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : space m →L[ℝ] F) (v : space m) : L v = ∑ i, v i • L (basisVector i) := by
  have hv : v = ∑ i, v i • basisVector i := by
    simpa only [basisVector, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v).symm
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

lemma directional_comp_jacobian {f : space m → ℝ} {T : space m → space m}
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ T x (basisVector j)) i)
    {x : space m} (hf : DifferentiableAt ℝ f (T x)) (hT : DifferentiableAt ℝ T x)
    (i : Fin m) :
    directional (basisVector i) (f ∘ T) x =
      ∑ r, directional (basisVector r) f (T x) * J x r i := by
  change fderiv ℝ (f ∘ T) x (basisVector i) = _
  rw [fderiv_comp x hf hT, ContinuousLinearMap.comp_apply,
    clm_apply_basis (fderiv ℝ f (T x))]
  apply Finset.sum_congr rfl
  intro r _
  rw [hJ]
  simp only [directional, smul_eq_mul, mul_comm]

lemma directional_coordinate (i j : Fin m) (x : space m) :
    directional (basisVector j) (fun y : space m => y i) x = if i = j then 1 else 0 := by
  change fderiv ℝ (EuclideanSpace.proj i : space m →L[ℝ] ℝ) x (basisVector j) = _
  erw [(EuclideanSpace.proj i : space m →L[ℝ] ℝ).fderiv]
  simp [basisVector, PiLp.single_apply]

/-- A coordinate form of the second derivative chain rule for a gradient map. -/
lemma directional_comp_twice {φ V : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (x : space m) (i j : Fin m) :
    directional (basisVector j) (directional (basisVector i) (V ∘ gradient φ)) x =
      (J x * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) (gradient φ x)
        (basisVector u) (basisVector v)) * J x) i j +
      ∑ r, directional (basisVector r) V (gradient φ x) *
        directional (basisVector r) (fun y => J y i j) x := by
  have hT := (contDiff_gradient hφ).differentiable (by simp)
  have hJc := contDiff_jacobian hφ hJ
  have hJe (r s : Fin m) : ContDiff ℝ ∞ (fun y => J y r s) :=
    contDiff_pi.mp (contDiff_pi.mp hJc r) s
  have hVe (r : Fin m) := contDiff_directional hV (basisVector r)
  have he : directional (basisVector i) (V ∘ gradient φ) =
      fun y => ∑ r, directional (basisVector r) V (gradient φ y) * J y r i :=
    funext fun y => directional_comp_jacobian hJ (hV.differentiable (by simp) _) (hT y) i
  rw [he]
  erw [directional_sum Finset.univ (fun r _ =>
    ((hVe r).differentiable (by simp) _ |>.comp x (hT x)).mul
      ((hJe r i).differentiable (by simp) x))]
  have he' (r : Fin m) :
      directional (basisVector j)
        (fun y => directional (basisVector r) V (gradient φ y) * J y r i) x =
      (∑ s, fderiv ℝ (fderiv ℝ V) (gradient φ x) (basisVector r) (basisVector s) *
        J x s j) * J x r i +
      directional (basisVector r) V (gradient φ x) *
        directional (basisVector r) (fun y => J y i j) x := by
    erw [directional_mul (((hVe r).differentiable (by simp) _).comp x (hT x))
      ((hJe r i).differentiable (by simp) x)]
    have hchain := directional_comp_jacobian hJ ((hVe r).differentiable (by simp) _) (hT x) j
    change directional (basisVector j)
      ((directional (basisVector r) V) ∘ gradient φ) x = _ at hchain
    rw [hchain]
    simp_rw [directional_comm hV _ (basisVector r), directional_twice hV]
    rw [jacobian_derivative_symmetric hφ hJ x j r i,
      jacobian_derivative_swap hφ hJ x i r j]
    rfl
  change (∑ r, directional (basisVector j)
    (fun y => directional (basisVector r) V (gradient φ y) * J y r i) x) = _
  simp_rw [he', Finset.sum_add_distrib]
  congr 1
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  erw [jacobian_symmetric hφ hJ x i s]
  ring

end Submission.Obl.Entropy__transport_finite_jacobian_energy
