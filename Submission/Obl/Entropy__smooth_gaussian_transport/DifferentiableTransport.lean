import Submission.Obl.Entropy__smooth_gaussian_transport.DualBounds
import Submission.Obl.Entropy__smooth_gaussian_transport.FirstRegularity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem brenier_contDiff_one {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ContDiff ℝ 1 φ ∧ ContDiff ℝ 1 (finiteConjugate φ) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  have hψdom := conjugateDomain_finiteConjugate hdom
  have hψ := finiteConjugate_convex hdom
  have hcontact := contactSet_subsingleton hm hφ hdom
    (fun _ hK => brenier_alexandrov_bounds hV hφ hlaw hK)
  have hcontact' := contactSet_subsingleton hm hψ hψdom
    (brenier_dual_alexandrov_bounds hV hφ hlaw)
  refine ⟨contDiff_one_of_dual_contactSet_subsingleton hφ hdom hcontact', ?_⟩
  apply contDiff_one_of_dual_contactSet_subsingleton hψ hψdom
  simpa only [finiteConjugate_involutive hφ hdom] using hcontact

theorem continuous_gradient_of_contDiff_one {m : ℕ} {u : E m → ℝ}
    (hu : ContDiff ℝ 1 u) : Continuous (gradient u) :=
  (InnerProductSpace.toDual ℝ (E m)).symm.continuous.comp (hu.continuous_fderiv (by norm_num))

theorem brenier_gradient_inverse {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    Function.LeftInverse (gradient (finiteConjugate φ)) (gradient φ) ∧
      Function.RightInverse (gradient (finiteConjugate φ)) (gradient φ) := by
  have hdom : conjugateDomain φ = univ := by
    apply conjugateDomain_eq_univ_of_transport hφ (stdGaussian_absolutelyContinuous m)
    rw [hlaw]
    exact target_support hV
  obtain ⟨hφ₁, hψ₁⟩ := brenier_contDiff_one hm hV hφ hlaw
  have hdφ := hφ₁.differentiable (by norm_num)
  have hdψ := hψ₁.differentiable (by norm_num)
  constructor
  · intro x
    have hx : IsSubgradient φ x (gradient φ x) := convex_gradient_support hφ (hdφ x)
    exact Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support
      (hdψ _) (hx.conjugate hdom)
  · intro y
    have hy : IsSubgradient (finiteConjugate φ) y (gradient (finiteConjugate φ) y) :=
      convex_gradient_support (finiteConjugate_convex hdom) (hdψ y)
    exact Submission.Lib.Brenier.ConvexGradientLaw.gradient_eq_of_support
      (hdφ _) ((subgradient_conjugate_iff hφ hdom).mpr hy)

/-- The transport and conjugate transport are continuous inverses everywhere. -/
noncomputable def brenierGradientHomeomorph {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) : E m ≃ₜ E m where
  toFun := gradient φ
  invFun := gradient (finiteConjugate φ)
  left_inv := (brenier_gradient_inverse hm hV hφ hlaw).1
  right_inv := (brenier_gradient_inverse hm hV hφ hlaw).2
  continuous_toFun := continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV hφ hlaw).1
  continuous_invFun := continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV hφ hlaw).2

theorem brenier_alexandrov_continuous_density {m : ℕ} (hm : 1 ≤ m) {V φ : E m → ℝ}
    (hV : Continuous V) (hφ : ConvexOn ℝ univ φ)
    (hlaw : Measure.map (gradient φ) (stdGaussian (E m)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    Continuous (fun x => Submission.Lib.EntropyRemainder.gaussianDensity x *
      Real.exp (V (gradient φ x))) :=
  Submission.Lib.EntropyRemainder.gaussianDensity_continuous.mul
    (Real.continuous_exp.comp (hV.comp
      (continuous_gradient_of_contDiff_one (brenier_contDiff_one hm hV hφ hlaw).1)))

end Submission.Obl.Entropy__smooth_gaussian_transport
