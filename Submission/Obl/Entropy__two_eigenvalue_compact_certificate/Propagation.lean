import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Expressions
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Stability
import Submission.Lib.GaussianTransport.GaussianTails

open Set

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

noncomputable def Model.parameter (M : Model) (x : ℝ) : ℝ := M.center + M.radius*x

def Model.gap (M : Model) : List ℚ := padd M.hazard (pscale (-1) M.coordinate)

def Model.qResidual (M : Model) : List ℚ :=
  padd (pdiff M.hazard) (pscale (-M.radius) (pmul M.hazard M.gap))

def Model.kResidual (M : Model) : List ℚ :=
  padd (pdiff M.ratio) (pscale (-M.radius) (padd [1] (pscale (-1) (pmul M.ratio M.gap))))

theorem Model.eval_coordinate (M : Model) (x : ℝ) : peval M.coordinate x = M.parameter x := by
  simp [coordinate, parameter, peval, mul_comm]

theorem Model.eval_gap (M : Model) (x : ℝ) :
    peval M.gap x = peval M.hazard x - M.parameter x := by
  simp [gap, peval_add, peval_scale, eval_coordinate, sub_eq_add_neg]

theorem Model.eval_qResidual (M : Model) (x : ℝ) :
    peval M.qResidual x = peval (pdiff M.hazard) x -
      (M.radius : ℝ)*peval M.hazard x*(peval M.hazard x-M.parameter x) := by
  simp only [qResidual, peval_add, peval_scale, peval_mul, eval_gap, Rat.cast_neg]
  ring

theorem Model.eval_kResidual (M : Model) (x : ℝ) :
    peval M.kResidual x = peval (pdiff M.ratio) x -
      (M.radius : ℝ)*(1-peval M.ratio x*(peval M.hazard x-M.parameter x)) := by
  simp only [kResidual, peval_add, peval_scale, peval_mul, eval_gap, peval,
    Rat.cast_neg, Rat.cast_one, mul_zero, add_zero]
  ring

theorem Model.hasDerivAt_parameter (M : Model) (x : ℝ) :
    HasDerivAt M.parameter (M.radius : ℝ) x := by
  change HasDerivAt (fun y => (M.center : ℝ) + (M.radius : ℝ)*y) (M.radius : ℝ) x
  convert! ((hasDerivAt_id x).const_mul (M.radius : ℝ)).const_add (M.center : ℝ) using 1
  simp

theorem Model.hazard_step (M : Model) {R E : ℝ} (hr : 0 < M.radius)
    (hgap : ∀ x : ℝ, |x| ≤ 1 → 0 < peval M.gap x)
    (hres : (pnorm M.qResidual : ℝ) ≤ R) (hE : 0 < E)
    (hanchor : |gaussianHazard (M.parameter 1) - peval M.hazard 1| ≤ E)
    {x : ℝ} (hx : |x| ≤ 1) :
    |gaussianHazard (M.parameter x)-peval M.hazard x| ≤ E+2*R := by
  have hr' : (0 : ℝ) < M.radius := by exact_mod_cast hr
  have hR : 0 ≤ R := le_trans (by exact_mod_cast pnorm_nonneg M.qResidual) hres
  refine stable_backward_error
    (f := fun y => gaussianHazard (M.parameter y)-peval M.hazard y)
    (x := x)
    (f' := fun y => (M.radius : ℝ)*gaussianHazard (M.parameter y)*
      (gaussianHazard (M.parameter y)-M.parameter y)-peval (pdiff M.hazard) y)
    (c := fun y => (M.radius : ℝ)*(gaussianHazard (M.parameter y)+peval M.gap y))
    (g := fun y => -peval M.qResidual y)
    ?_ ?_ ?_ ?_ hE hR hanchor (abs_le.mp hx)
  · intro y hy
    convert! ((hasDerivAt_gaussianHazard (M.parameter y)).comp y
      (M.hasDerivAt_parameter y)).sub (hasDerivAt_peval M.hazard y) using 1
    ring
  · intro y hy
    rw [M.eval_qResidual, M.eval_gap]
    ring
  · intro y hy
    exact mul_pos hr' (add_pos (gaussianHazard_pos _) (hgap y (abs_le.mpr hy)))
  · intro y hy
    simpa only [abs_neg] using (abs_peval_le M.qResidual (abs_le.mpr hy)).trans hres

theorem Model.ratio_step (M : Model) {R E K : ℝ} (hr : 0 < M.radius)
    (hres : (pnorm M.kResidual : ℝ) ≤ R) (hK : (pnorm M.ratio : ℝ) ≤ K)
    (hE : 0 < E)
    (hanchor : |transportRatio (M.parameter (-1)) - peval M.ratio (-1)| ≤ E)
    (hq : ∀ x : ℝ, |x| ≤ 1 →
      |gaussianHazard (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    {x : ℝ} (hx : |x| ≤ 1) :
    |transportRatio (M.parameter x)-peval M.ratio x| ≤ E+2*(R+M.radius*K/10^8) := by
  have hr' : (0 : ℝ) < M.radius := by exact_mod_cast hr
  have hR : 0 ≤ R := le_trans (by exact_mod_cast pnorm_nonneg M.kResidual) hres
  have hK' : 0 ≤ K := le_trans (by exact_mod_cast pnorm_nonneg M.ratio) hK
  have hF : 0 ≤ R+(M.radius : ℝ)*K/10^8 := by positivity
  have hh := stable_forward_error
    (f := fun y => transportRatio (M.parameter y)-peval M.ratio y)
    (f' := fun y => (M.radius : ℝ)*transportSlope (M.parameter y)-peval (pdiff M.ratio) y)
    (c := fun y => (M.radius : ℝ)*gaussianGap (M.parameter y))
    (g := fun y => -peval M.kResidual y-(M.radius : ℝ)*peval M.ratio y*
      (gaussianHazard (M.parameter y)-peval M.hazard y))
    (a := -1) (b := 1) (E := E) (F := R+(M.radius : ℝ)*K/10^8)
    (fun y hy => by
      convert! ((hasDerivAt_transportRatio (M.parameter y)).comp y
        (M.hasDerivAt_parameter y)).sub (hasDerivAt_peval M.ratio y) using 1
      ring)
    (fun y hy => by
      rw [M.eval_kResidual]
      dsimp only [transportSlope, gaussianGap]
      ring)
    (fun y hy => mul_pos hr' (gaussianGap_pos _))
    (fun y hy => ?_) hE hF hanchor (abs_le.mp hx)
  · have hx' := (abs_le.mp hx).2
    nlinarith
  · have habs := (abs_peval_le M.kResidual (abs_le.mpr hy)).trans hres
    have hratio := (abs_peval_le M.ratio (abs_le.mpr hy)).trans hK
    have hq' := hq y (abs_le.mpr hy)
    calc
      _ ≤ |peval M.kResidual y| + |(M.radius : ℝ)*peval M.ratio y*
        (gaussianHazard (M.parameter y)-peval M.hazard y)| := by
          simpa only [abs_neg] using abs_sub (-peval M.kResidual y)
            ((M.radius : ℝ)*peval M.ratio y*(gaussianHazard (M.parameter y)-peval M.hazard y))
      _ ≤ R+(M.radius : ℝ)*K/10^8 := by
        rw [abs_mul, abs_mul, abs_of_pos hr']
        calc
          _ ≤ R+(M.radius : ℝ)*K*(1/10^8) := by gcongr
          _ = _ := by ring

def Model.ODECheck (M : Model) (R K : ℚ) : Prop :=
  0 < M.radius ∧ pnorm M.qResidual ≤ R ∧ pnorm M.kResidual ≤ 2/10^10 ∧
    pnorm M.ratio ≤ K ∧ (⟨M.gap, 0⟩ : Enclosure).trunc.LowerBound (9/100)

instance (M : Model) (R K : ℚ) : Decidable (M.ODECheck R K) :=
  inferInstanceAs (Decidable (0 < M.radius ∧ pnorm M.qResidual ≤ R ∧
    pnorm M.kResidual ≤ 2/10^10 ∧ pnorm M.ratio ≤ K ∧
    (⟨M.gap, 0⟩ : Enclosure).trunc.LowerBound (9/100)))

theorem Model.ODECheck.gap_pos {M : Model} {R K : ℚ} (h : M.ODECheck R K)
    (x : ℝ) (hx : |x| ≤ 1) : 0 < peval M.gap x := by
  have hh : (⟨M.gap, 0⟩ : Enclosure).Holds x (peval M.gap x) := by
    simp [Enclosure.Holds]
  have hh' := h.2.2.2.2.le (hh.trunc hx) hx
  norm_num at hh'
  linarith

theorem Model.ODECheck.hazard_step {M : Model} {R K : ℚ} (h : M.ODECheck R K)
    {E : ℝ} (hE : 0 < E)
    (ha : |gaussianHazard (M.parameter 1)-peval M.hazard 1| ≤ E)
    {x : ℝ} (hx : |x| ≤ 1) :
    |gaussianHazard (M.parameter x)-peval M.hazard x| ≤ E+2*(R : ℝ) :=
  M.hazard_step h.1 h.gap_pos (by exact_mod_cast h.2.1) hE ha hx

theorem Model.ODECheck.ratio_step {M : Model} {R K : ℚ} (h : M.ODECheck R K)
    {E : ℝ} (hE : 0 < E)
    (ha : |transportRatio (M.parameter (-1))-peval M.ratio (-1)| ≤ E)
    (hq : ∀ x : ℝ, |x| ≤ 1 →
      |gaussianHazard (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    {x : ℝ} (hx : |x| ≤ 1) :
    |transportRatio (M.parameter x)-peval M.ratio x| ≤
      E+2*((2/10^10 : ℝ)+(M.radius : ℝ)*(K : ℝ)/10^8) := by
  have hr : (pnorm M.kResidual : ℝ) ≤ ((2/10^10 : ℚ) : ℝ) := by exact_mod_cast h.2.2.1
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hr
  convert! M.ratio_step (K := (K : ℝ)) h.1 hr (by exact_mod_cast h.2.2.2.1) hE ha hq hx using 1 <;> norm_num

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
