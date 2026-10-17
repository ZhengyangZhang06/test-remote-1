import Submission.Obl.Entropy__smooth_gaussian_transport.HolderChanges
import Submission.Obl.Entropy__smooth_gaussian_transport.HessianOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem uniformBoundedHolder_hessian_comp {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} (hf : ContDiff ℝ 2 f) {α : ℝ} (hα : 0 ≤ α)
    (hmod : UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 f))
    (L : Y →L[ℝ] X) :
    UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun y => f (L y))) := by
  have h := (hmod.comp_lipschitz_domain hα L.lipschitz).mapCLM
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin 2 => L))
  convert! h using 1
  funext i x
  exact L.iteratedFDeriv_comp_right hf x le_rfl

end Submission.Obl.Entropy__smooth_gaussian_transport
