import Submission.Obl.Entropy__smooth_gaussian_transport.PerturbedSchauder
import Submission.Obl.Entropy__smooth_gaussian_transport.UniformHolderLimit

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem contDiff_two_of_uniform_limit_hessian_holder
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {C α : ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) (hg : ContDiff ℝ 1 g) (hC : 0 ≤ C) (hα : 0 < α)
    (hfg : TendstoUniformly (fun n => fderiv ℝ (f n)) (fderiv ℝ g) atTop)
    (hmod : ∀ n x y, ‖iteratedFDeriv ℝ 2 (f n) x - iteratedFDeriv ℝ 2 (f n) y‖ ≤ C * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 g ∧ ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨hd, hconv, hholder⟩ := contDiff_one_of_uniform_limit_holder_derivative
    (fun n => (hf n).fderiv_right (by norm_num : (1 : WithTop ENat) + 1 ≤ 2)) hC hα hfg
    (fun n x y => by rw [norm_second_fderiv_sub]; exact hmod n x y)
  refine ⟨(contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨fderiv ℝ g, hd, fun x => (hg.differentiable_one x).hasFDerivAt⟩, ?_⟩
  intro x y
  simpa only [norm_second_fderiv_sub] using hholder x y

/-- A uniform Schauder estimate persists through a C¹ limit of compactly
supported solutions of small perturbations of the Laplacian. -/
theorem contDiff_two_of_perturbed_schauder_limit {m : ℕ} {α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hS : ∀ (f : E m → ℝ) (M C : ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ M → 0 ≤ C →
      (∀ x, ‖f x‖ ≤ M) →
      (∀ x y, |laplacian f x - laplacian f y| ≤ C * ‖x - y‖ ^ α) →
      ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ K * (M + C) * ‖x - y‖ ^ α)
    {f g : ℕ → E m → ℝ} {u : E m → ℝ}
    {T : ℕ → E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    {M N G ε L t : ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    (hu : ContDiff ℝ 1 u)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hL : 0 ≤ L) (ht : 0 < t)
    (hsmall : K * (ε + L * t ^ α) ≤ 1 / 2)
    (hb : ∀ n x, ‖f n x‖ ≤ M) (hdb : ∀ n x, ‖fderiv ℝ (f n) x‖ ≤ N)
    (hT : ∀ n x, ‖T n x‖ ≤ ε)
    (hTm : ∀ n x y, ‖T n x - T n y‖ ≤ L * ‖x - y‖ ^ α)
    (hgm : ∀ n x y, |g n x - g n y| ≤ G * ‖x - y‖ ^ α)
    (heq : ∀ n x, laplacian (f n) x = g n x + T n x (iteratedFDeriv ℝ 2 (f n) x))
    (hex : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ 2 (f n) x - iteratedFDeriv ℝ 2 (f n) y‖ ≤ C * ‖x - y‖ ^ α)
    (hfg : TendstoUniformly (fun n => fderiv ℝ (f n)) (fderiv ℝ u) atTop) :
    ContDiff ℝ 2 u ∧ ∀ x y, ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤
      (2 * K * (M + G + 2 * L * N / t)) * ‖x - y‖ ^ α := by
  exact contDiff_two_of_uniform_limit_hessian_holder hf hu (by positivity) hα hfg
    (fun n => perturbed_laplacian_schauder hα hα1 hK hS (hf n) (hfc n)
      hM hN hG hε hL ht hsmall (hb n) (hdb n) (hT n) (hTm n) (hgm n) (heq n) (hex n))

end Submission.Obl.Entropy__smooth_gaussian_transport
