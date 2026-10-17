import Submission.Obl.Entropy__transport_finite_jacobian_energy.WeakEquation
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Curvature
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Coercivity
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Flux
import Submission.Obl.Entropy__transport_finite_jacobian_energy.Energy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace Submission.Obl.Entropy__transport_finite_jacobian_energy

variable {m : ℕ}

lemma jacobian_energy_memLp {φ V : space m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    (hVpos : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    {J : space m → Matrix (Fin m) (Fin m) ℝ}
    (hJ : ∀ x i j, J x i j = (fderiv ℝ (gradient φ) x (basisVector j)) i)
    (hpos : ∀ x, (J x).PosDef)
    (hmap : (stdGaussian (space m)).map (gradient φ) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))))
    {ε M : ℝ} (hε : 0 < ε)
    (hlower : ∀ x, ((J x)⁻¹ - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (hbound : ∀ x s r, |(J x)⁻¹ s r| ≤ M) :
    ∀ r i j, MemLp (fun x => directional (basisVector r) J x i j) 2
      (stdGaussian (space m)) := by
  let H (r : Fin m) := directional (basisVector r) J
  let P (x : space m) := (J x)⁻¹
  let Q (x : space m) := J x * Matrix.of (fun u v =>
    fderiv ℝ (fderiv ℝ V) (gradient φ x) (basisVector u) (basisVector v)) * J x
  let R (i j : Fin m) (x : space m) :=
    -(if i = j then 1 else 0) + Q x i j + (P x * H i x * P x * H j x).trace
  let E (x : space m) := ∑ r, ∑ i, ∑ j, (H r x i j)^2
  let S (x : space m) := ∑ i, R i i x
  let b (s : Fin m) (x : space m) := ∑ r, ∑ i, P x s r * H r x i i
  have hJc := contDiff_jacobian hφ hJ
  have hHc (r : Fin m) : Continuous (H r) := (contDiff_directional hJc _).continuous
  have hPc : Continuous P := (contDiff_matrix_inv hJc (fun x => (hpos x).det_pos.ne')).continuous
  have hQc : Continuous Q := by
    apply (hJc.continuous.matrix_mul ?_).matrix_mul hJc.continuous
    apply continuous_pi
    intro u
    apply continuous_pi
    intro v
    have hc := ((contDiff_directional (contDiff_directional hV (basisVector v))
      (basisVector u)).comp (contDiff_gradient hφ)).continuous
    simpa only [Function.comp_def, directional_twice hV, Matrix.of_apply] using hc
  have hRc (i j : Fin m) : Continuous (R i j) :=
    (continuous_const.add ((continuous_apply j).comp ((continuous_apply i).comp hQc))).add
      ((((hPc.matrix_mul (hHc i)).matrix_mul hPc).matrix_mul (hHc j)).matrix_trace)
  have hEc : Continuous E := by
    apply continuous_finsetSum
    intro r _
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp ((continuous_apply i).comp (hHc r))).pow 2
  have hE0 (x : space m) : 0 ≤ E x := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSc : Continuous S := continuous_finsetSum _ fun i _ => hRc i i
  have hbc (s : Fin m) : Continuous (b s) := by
    apply continuous_finsetSum
    intro r _
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply r).comp ((continuous_apply s).comp hPc)).mul
      ((continuous_apply i).comp ((continuous_apply i).comp (hHc r)))
  have hsource (x : space m) : ε^2 * E x - (m : ℝ) ≤ S x := by
    have hi (i : Fin m) : ε^2 * (∑ u, ∑ v, (H i x u v)^2) - 1 ≤ R i i x := by
      have hco := weighted_trace_coercive (hpos x).inv.posSemidef hε.le (hlower x)
        (jacobian_directional_hermitian hφ hJ x i)
      have hq := curvature_diag_nonneg hV hVpos (J x) (hpos x).isHermitian (gradient φ x) i
      dsimp [R, P, H, Q]
      simp only [ite_true]
      linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, E, S] using hs
  have hflux (x : space m) : (∑ s, (b s x)^2) ≤
      ((m : ℝ)^5 * M^2 + 1) * E x := trace_flux_sq_bound (P x) (fun r => H r x) (hbound x)
  have hweak (z : space m → ℝ) (hz : ContDiff ℝ ∞ z) (hzK : HasCompactSupport z) :
      (∫ x, z x * S x ∂stdGaussian (space m)) =
        -(∑ s, ∫ x, directional (basisVector s) z x * b s x ∂stdGaussian (space m)) := by
    have hRI (i : Fin m) : Integrable (fun x => z x * R i i x) (stdGaussian (space m)) :=
      (hz.continuous.mul (hRc i i)).integrable_of_hasCompactSupport hzK.mul_right
    have hFI (s r i : Fin m) : Integrable (fun x =>
        directional (basisVector s) z x * P x s r * H r x i i) (stdGaussian (space m)) :=
      ((((contDiff_directional hz _).continuous.mul
        ((continuous_apply r).comp ((continuous_apply s).comp hPc))).mul
        ((continuous_apply i).comp ((continuous_apply i).comp (hHc r))))).integrable_of_hasCompactSupport
          ((hasCompactSupport_directional hzK _).mul_right.mul_right)
    calc
      _ = ∑ i, ∫ x, z x * R i i x ∂stdGaussian (space m) := by
        simp only [S, Finset.mul_sum]
        exact integral_finsetSum _ (fun i _ => hRI i)
      _ = -(∑ i, ∑ r, ∑ s, ∫ x,
          directional (basisVector s) z x * P x s r * H r x i i ∂stdGaussian (space m)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact weak_jacobian_equation hφ hV hJ hpos hmap i i hz hzK
      _ = -(∑ s, ∑ r, ∑ i, ∫ x,
          directional (basisVector s) z x * P x s r * H r x i i ∂stdGaussian (space m)) := by
        congr 1
        rw [Finset.sum_comm]
        calc
          _ = ∑ r, ∑ s, ∑ i, ∫ x, directional (basisVector s) z x * P x s r * H r x i i
              ∂stdGaussian (space m) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        simp only [b, Finset.mul_sum, ← mul_assoc]
        rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ => hFI s r i))]
        apply Finset.sum_congr rfl
        intro r _
        exact (integral_finsetSum _ (fun i _ => hFI s r i)).symm
  have hEI := energy_integrable_of_weak hEc hE0 hSc hbc (sq_pos_of_pos hε)
    (by positivity : 0 < (m : ℝ)^5 * M^2 + 1) (Nat.cast_nonneg m) hsource hflux hweak
  intro r i j
  have hc : Continuous (fun x => H r x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (hHc r))
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply hEI.mono' (hc.pow 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact tensor_entry_sq_le (fun r => H r x) r i j

end Submission.Obl.Entropy__transport_finite_jacobian_energy
