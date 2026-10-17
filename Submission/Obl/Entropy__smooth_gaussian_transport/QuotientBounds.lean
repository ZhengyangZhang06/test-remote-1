import Submission.Obl.Entropy__smooth_gaussian_transport.UniformBoundedHolder
import Submission.Obl.Entropy__smooth_gaussian_transport.DirectionalQuotient
import Submission.Obl.Entropy__smooth_gaussian_transport.CutoffHessian

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem uniformBoundedHolder_quotients {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {α : ℝ}
    (hDf : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f))
    (h : ι → ℝ) (hh : ∀ i, h i ≠ 0) (v : X) :
    UniformBoundedHolder α (fun i => directionalQuotient f (h i) v) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hDf
  refine ⟨M * ‖v‖, C * ‖v‖, by positivity, by positivity, ?_, ?_⟩
  · intro i x
    exact directionalQuotient_norm_bound hf (hh i) v x (fun t ht => hb () _) 
  · intro i x y
    apply directionalQuotient_holder_bound hf (hh i)
    intro t ht
    simpa only [add_sub_add_right_eq_sub] using hm () (x + t • (h i • v)) (y + t • (h i • v))

def UniformDerivativeHolder {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (α : ℝ) (f : X → Y) : Prop :=
  UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f)

theorem uniformBoundedHolder_quotients_of_derivative {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) {α : ℝ} (hDf : UniformDerivativeHolder α f)
    (h : ι → ℝ) (hh : ∀ i, h i ≠ 0) (v : X) :
    UniformBoundedHolder α (fun i => directionalQuotient f (h i) v) :=
  uniformBoundedHolder_quotients hf hDf h hh v

theorem uniformBoundedHolder_fixed_quotient {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {α : ℝ} (hf : UniformBoundedHolder α (fun (_ : Unit) => f)) (h : ℝ) (v : X) :
    UniformBoundedHolder α (fun (_ : Unit) => directionalQuotient f h v) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  have hshift : UniformBoundedHolder α (fun (_ : Unit) x => f (x + h • v)) := by
    refine ⟨M, C, hM, hC, fun _ x => hb () _, ?_⟩
    intro i x y
    simpa only [add_sub_add_right_eq_sub] using hm () (x + h • v) (y + h • v)
  exact (UniformBoundedHolder.constant α h⁻¹).smul (hshift.sub ⟨M, C, hM, hC, hb, hm⟩)

theorem uniformBoundedHolder_hessian_mul {ι X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ : X → ℝ} {f : ι → X → ℝ} {α : ℝ}
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (h0 : UniformBoundedHolder α f)
    (h1 : UniformBoundedHolder α (fun i => fderiv ℝ (f i)))
    (h2 : UniformBoundedHolder α (fun i => iteratedFDeriv ℝ 2 (f i))) :
    UniformBoundedHolder α (fun i => iteratedFDeriv ℝ 2 (fun x => χ x * f i x)) := by
  have hc0 : UniformBoundedHolder α (fun (_ : ι) => χ) :=
    .of_compact_c1 (hχ.of_le (by norm_num)) hχc hα hα1
  have hc1 : UniformBoundedHolder α (fun (_ : ι) => fderiv ℝ χ) :=
    .of_compact_c1 (hχ.fderiv_right (by norm_num)) (hχc.fderiv ℝ) hα hα1
  have hc2 : UniformBoundedHolder α (fun (_ : ι) => iteratedFDeriv ℝ 2 χ) :=
    .of_compact_c1 (hχ.iteratedFDeriv_right (by norm_num)) (hχc.iteratedFDeriv 2) hα hα1
  have hc := ((hc1.smulRight h1).add (h1.smulRight hc1)).mapLIE (hessianCurry X ℝ).symm
  convert! ((hc0.smul h2).add (h0.smul hc2)).add hc using 1
  funext i x
  exact iteratedFDeriv_two_mul (hχ.of_le (by norm_num)) (hf i) x

end Submission.Obl.Entropy__smooth_gaussian_transport
