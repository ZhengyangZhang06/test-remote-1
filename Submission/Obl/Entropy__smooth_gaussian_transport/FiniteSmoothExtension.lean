import Submission.Obl.Entropy__smooth_gaussian_transport.SmoothExtension

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

theorem exists_compact_contDiff_extension {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {x : X} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ∃ g : X → Y, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨U, hU, hreg⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨χ, hχ, hχc, hχW, hχrange, hχone⟩ := exists_compact_smooth_cutoff (hW.mem_nhds hxW)
  refine ⟨fun y => χ y • f y, contDiff_smul_of_tsupport
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (n : ENat) ≤ ⊤)))
    (fun y hy => (hreg y (hWU (hχW hy))).contDiffAt (mem_of_superset (hW.mem_nhds (hχW hy)) hWU)),
      hχc.smul_right, ?_⟩
  filter_upwards [hχone] with y hy
  simp only [hy, one_smul]

end Submission.Obl.Entropy__smooth_gaussian_transport
