import Submission.Obl.Entropy__transport_finite_jacobian_energy.LogJacobian
import Submission.Obl.Entropy__transport_finite_jacobian_energy.GaussianIBP

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

/-- The differentiated transport equation against a smooth compact test. -/
lemma weak_jacobian_equation {φ V : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hpos : ∀ x, (J x).PosDef)
    (hmap : (stdGaussian (space m)).map (gradient φ) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    (i j : Fin m) {z : space m → ℝ} (hz : ContDiff ℝ ∞ z) (hzK : HasCompactSupport z) :
    (∫ x, z x * (-(if i = j then 1 else 0) +
      (J x * Matrix.of (fun u v => fderiv ℝ (fderiv ℝ V) (gradient φ x)
        (basisVector u) (basisVector v)) * J x) i j +
      ((J x)⁻¹ * directional (basisVector i) J x * (J x)⁻¹ *
        directional (basisVector j) J x).trace) ∂stdGaussian (space m)) =
    -(∑ r, ∑ s, ∫ x, directional (basisVector s) z x * (J x)⁻¹ s r *
      directional (basisVector r) J x i j ∂stdGaussian (space m)) := by
  have hc := contDiff_jacobian hφ hJ
  have hinv (x : space m) : (J x).det ≠ 0 := (hpos x).det_pos.ne'
  have hi := contDiff_matrix_inv hc hinv
  have he : ContDiff ℝ ∞ (fun x => J x i j) := contDiff_pi.mp (contDiff_pi.mp hc i) j
  let f (s r : Fin m) (x : space m) :=
    (J x)⁻¹ s r * directional (basisVector r) (fun y => J y i j) x
  have hf (s r : Fin m) : ContDiff ℝ ∞ (f s r) :=
    (contDiff_pi.mp (contDiff_pi.mp hi s) r).mul (contDiff_directional he (basisVector r))
  let D (s r : Fin m) (x : space m) :=
    directional (basisVector s) (f s r) x - x s * f s r x
  have hD (s r : Fin m) : Continuous (D s r) :=
    (contDiff_directional (hf s r) _).continuous.sub
      ((EuclideanSpace.proj s).continuous.mul (hf s r).continuous)
  have hI (s r : Fin m) : Integrable (fun x => z x * D s r x) (stdGaussian (space m)) :=
    (hz.continuous.mul (hD s r)).integrable_of_hasCompactSupport hzK.mul_right
  have hdiv := jacobian_divergence_form hφ hV contDiff_gaussianPotential hJ hinv
    (transport_gaussian_logdet hφ hV hJ hpos hmap) directional_gaussianPotential
  calc
    _ = ∫ x, ∑ s, ∑ r, z x * D s r x ∂stdGaussian (space m) := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      erw [hdiv x i j]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      dsimp [D, f]
      ring
    _ = ∑ s, ∑ r, ∫ x, z x * D s r x ∂stdGaussian (space m) := by
      rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun r _ => hI s r))]
      apply Finset.sum_congr rfl
      intro s _
      exact integral_finsetSum _ (fun r _ => hI s r)
    _ = ∑ s, ∑ r, -(∫ x, directional (basisVector s) z x * f s r x
        ∂stdGaussian (space m)) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      exact gaussian_compact_adjoint hz (hf s r) hzK s
    _ = _ := by
      simp only [Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp [f]
      erw [directional_matrix_entry (hc.differentiable (by simp) x)]
      ring

end Submission.Obl.Entropy__transport_finite_jacobian_energy
