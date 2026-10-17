import Submission.Obl.Entropy__smooth_gaussian_transport.HolderLocalization

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_compact_smooth_cutoff {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {x : X} {U : Set X} (hU : U ∈ nhds x) :
    ∃ χ : X → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ ∀ᶠ y in nhds x, χ y = 1 := by
  obtain ⟨r, hr, hsub⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp hU
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let χ : X → ℝ := fun y => c (toEuclidean y)
  have hs : tsupport χ ⊆ Euclidean.closedBall x r := by
    rw [tsupport, ← Euclidean.closure_ball _ hr.ne']
    apply closure_mono
    intro y hy
    have hyy : toEuclidean y ∈ Function.support c := hy
    rwa [c.support_eq] at hyy
  refine ⟨χ, c.contDiff.comp (ContinuousLinearEquiv.contDiff _), ?_, hs.trans hsub,
    fun y => ⟨c.nonneg, c.le_one⟩, ?_⟩
  · exact IsCompact.of_isClosed_subset Euclidean.isCompact_closedBall isClosed_closure hs
  · exact c.eventuallyEq_one.comp_tendsto (toEuclidean.continuous.tendsto x)

theorem contDiff_smul_of_tsupport {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {χ : X → ℝ} {f : X → Y} {n : WithTop ENat}
    (hχ : ContDiff ℝ n χ) (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ n f x) :
    ContDiff ℝ n (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf x hx)
  · apply (contDiffAt_const (c := (0 : Y))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]

theorem exists_compact_c1_extension {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 1 f x) :
    ∃ g : X → Y, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨U, hU, hreg⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨χ, hχ, hχc, hχW, hχrange, hχone⟩ := exists_compact_smooth_cutoff (hW.mem_nhds hxW)
  refine ⟨fun y => χ y • f y, contDiff_smul_of_tsupport (hχ.of_le (by exact_mod_cast (le_top : (1 : ENat) ≤ ⊤)))
    (fun y hy => (hreg y (hWU (hχW hy))).contDiffAt (mem_of_superset (hW.mem_nhds (hχW hy)) hWU)),
      hχc.smul_right, ?_⟩
  filter_upwards [hχone] with y hy
  simp only [hy, one_smul]

end Submission.Obl.Entropy__smooth_gaussian_transport
