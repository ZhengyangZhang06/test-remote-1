import Submission.Obl.Entropy__normalized_remainder.CFCAlgebra

open Filter Asymptotics
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace Submission.Obl.Entropy__normalized_remainder

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

/-- A continuous factor can be differentiated in a product if the other factor
vanishes at the base point. -/
lemma hasFDerivAt_mul_continuous_zero {f g : E → R} {f' : E →L[ℝ] R} {x : E}
    (hf : HasFDerivAt f f' x) (hf0 : f x = 0) (hg : ContinuousAt g x) :
    HasFDerivAt (fun y => f y * g y)
      (((ContinuousLinearMap.mul ℝ R).flip (g x)).comp f') x := by
  have hO : f =O[𝓝 x] (fun y => ‖y - x‖) := by
    simpa only [hf0, sub_zero] using hf.isBigO_sub.norm_right
  have ho : (fun y => g y - g x) =o[𝓝 x] (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).2
    simpa using hg.tendsto.sub (tendsto_const_nhds (x := g x))
  have hz : HasFDerivAt (fun y => f y * (g y - g x)) (0 : E →L[ℝ] R) x := by
    apply HasFDerivAt.of_isLittleO
    simpa only [hf0, zero_mul, sub_zero, zero_apply,
      mul_one, isLittleO_norm_right] using hO.mul_isLittleO ho
  convert! (hf.mul_const' (g x)).add hz using 1
  · funext y
    simp only [Pi.add_apply, mul_sub]
    abel
  · simp only [add_zero]
    rfl

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma continuous_dslope_of_differentiable {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℝ) :
    Continuous (dslope f a) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 a)).2
    ⟨hf.continuous.continuousOn, hf a⟩

omit [NormedSpace ℝ E] in
/-- Continuity of the divided-difference CFC along Hermitian matrix fields. -/
lemma continuous_cfc_dslope {A : E → Matrix n n ℝ} (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℝ) :
    Continuous (fun x => cfc (dslope f a) (A x)) := by
  exact hA.cfc_of_mem_nhdsSet (s := Set.univ) (dslope f a) (by simp)
    (fun x => (hAH x).isSelfAdjoint) (continuous_dslope_of_differentiable hf a).continuousOn

/-- The Frechet derivative of CFC along a differentiable Hermitian field.
This form uses a fixed spectral basis at the point of differentiation. -/
lemma hasFDerivAt_cfc {A : E → Matrix n n ℝ} (hA : Continuous A)
    (hAH : ∀ x, (A x).IsHermitian) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {x : E} {A' : E →L[ℝ] Matrix n n ℝ} (hAx : HasFDerivAt A A' x) :
    HasFDerivAt (fun y => cfc f (A y))
      (∑ i, (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ)
        (spectralProjector (hAH x) i)
        (cfc (dslope f ((hAH x).eigenvalues i)) (A x))).comp A') x := by
  have hi (i : n) := hasFDerivAt_mul_continuous_zero
    ((hAx.sub_const (A x)).const_mul (spectralProjector (hAH x) i))
    (by simp) (continuous_cfc_dslope hA hAH hf ((hAH x).eigenvalues i)).continuousAt
  have hh := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_add (cfc f (A x))
  convert! hh using 1
  funext y
  rw [← cfc_sub_eq_sum_projector (hAH x) (hAH y) f]
  abel

end Submission.Obl.Entropy__normalized_remainder
