import Submission.Obl.Entropy__smooth_gaussian_transport.QuotientSchauder
import Submission.Obl.Entropy__smooth_gaussian_transport.SmallCoefficientExtension
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderComposition

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

/-- A linear elliptic equation gains a derivative when its coefficients and
right-hand side have Hölder continuous first derivatives. -/
theorem linear_quotient_regularization {m : ℕ} {f g : E m → ℝ}
    {A : E m → (E m [×2]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hA : ContDiff ℝ 1 A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hH : UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 f))
    (hDg : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ g))
    (hDA : UniformDerivativeHolder α A)
    (x : E m) (hAx : A x = hessianTrace m)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (heq : ∀ z, ‖z - x‖ < r₀ → A z (iteratedFDeriv ℝ 2 f z) = g z)
    (v : E m) :
    ∃ χ : E m → ℝ, (∀ᶠ y in nhds x, χ y = 1) ∧
      ContDiff ℝ 2 (fun y => χ y * fderiv ℝ f y v) ∧
      UniformBoundedHolder α (fun (_ : Unit) => iteratedFDeriv ℝ 2 (fun y => χ y * fderiv ℝ f y v)) := by
  obtain ⟨ε, hε, hS⟩ := exists_quotient_schauder_threshold m hα hα1
  obtain ⟨P, ⟨L, hLip⟩, hPs, heP⟩ := exists_small_lipschitz_extension
    (contDiffAt_const.sub hA.contDiffAt) (by rw [hAx, sub_self]) hε
  have hP : UniformBoundedHolder α (fun (_ : ℕ) => P) := by
    refine ⟨ε, L + 2 * ε, hε.le, by positivity, fun _ => hPs, ?_⟩
    intro n
    apply holder_of_lipschitz_and_bound hε.le L.coe_nonneg hα hα1.le hPs
    intro z w
    simpa only [dist_eq_norm] using hLip.dist_le_mul z w
  obtain ⟨r, hr, hPe⟩ := Metric.mem_nhds_iff.mp heP
  let δ : ℝ := min r r₀ / 4
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδr : δ ≤ r / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδr₀ : δ ≤ r₀ / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨χ, hχ, hχc, hχsupp, hχrange, hχone⟩ :=
    exists_compact_smooth_cutoff (Metric.ball_mem_nhds x hδ)
  let c : ℝ := δ / (‖v‖ + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  let h : ℕ → ℝ := fun n => c * (1 / ((n : ℝ) + 1))
  have hh (n : ℕ) : 0 < h n := by dsimp only [h]; positivity
  have hlim : Tendsto h atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hstep (n : ℕ) : ‖h n • v‖ < δ := by
    have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hh' : h n ≤ c := by dsimp only [h]; nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hh n)]
    have hc' : c * (‖v‖ + 1) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg v]
  have hD : UniformBoundedHolder α (fun (_ : Unit) => fderiv ℝ f) :=
    .of_compact_c1 (hf.fderiv_right (by norm_num)) (hfc.fderiv ℝ) hα hα1.le
  have hqg := uniformBoundedHolder_quotients hg hDg h (fun n => (hh n).ne') v
  have hqA := uniformBoundedHolder_quotients_of_derivative hA hDA h (fun n => (hh n).ne') v
  let G : ℕ → E m → ℝ := fun n z => directionalQuotient g (h n) v z -
    directionalQuotient A (h n) v z (iteratedFDeriv ℝ 2 f z)
  have hG : UniformBoundedHolder α G := hqg.sub (hqA.clm_apply (hH.reindex (fun _ => ())))
  have hlocal (n : ℕ) (z : E m) (hz : χ z ≠ 0) :
      laplacian (directionalQuotient f (h n) v) z =
        G n z + P (z + h n • v) (iteratedFDeriv ℝ 2 (directionalQuotient f (h n) v) z) := by
    have hzδ : ‖z - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hχsupp (subset_closure hz)
    have hzw : ‖z + h n • v - x‖ < 2 * δ := by
      have he : z + h n • v - x = (z - x) + h n • v := by abel
      rw [he]
      exact (norm_add_le _ _).trans_lt (by linarith [hstep n])
    have heP' : P (z + h n • v) = hessianTrace m - A (z + h n • v) := by
      apply hPe
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have he0 := heq z (by linarith)
    have he1 := heq (z + h n • v) (by linarith)
    rw [heP', laplacian_eq_hessianTrace (directionalQuotient_contDiff hf (h n) v),
      directionalQuotient_iteratedFDeriv hf]
    dsimp only [G, directionalQuotient]
    simp only [sub_apply, smul_apply, map_smul, map_sub, smul_eq_mul]
    rw [he0, he1]
    ring
  obtain ⟨hres, hmod⟩ := hS f χ h v G (fun n z => P (z + h n • v)) hf
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ENat) ≤ ⊤))) hχc
    (fun n => (hh n).ne') hlim hD hH hG (hP.translate (fun n => h n • v))
    (fun n z => hPs _) hlocal
  exact ⟨χ, hχone, hres, hmod⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
