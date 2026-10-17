import Submission.Obl.Entropy__smooth_gaussian_transport.PerturbedSchauder
import Submission.Obl.Entropy__smooth_gaussian_transport.HolderLocalization

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

def UniformBoundedHolder {ι X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (α : ℝ) (f : ι → X → Y) : Prop :=
  ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ (∀ i x, ‖f i x‖ ≤ M) ∧
    ∀ i x y, ‖f i x - f i y‖ ≤ C * ‖x - y‖ ^ α

theorem UniformBoundedHolder.constant {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (α : ℝ) (c : Y) :
    UniformBoundedHolder α (fun (_ : ι) (_ : X) => c) := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ _ => le_rfl, ?_⟩
  intro i x y
  simp

theorem UniformBoundedHolder.reindex {ι ι' X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {α : ℝ} {f : ι → X → Y}
    (hf : UniformBoundedHolder α f) (g : ι' → ι) : UniformBoundedHolder α (fun i => f (g i)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  exact ⟨M, C, hM, hC, fun i => hb (g i), fun i => hm (g i)⟩

theorem UniformBoundedHolder.add {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {α : ℝ} {f g : ι → X → Y}
    (hf : UniformBoundedHolder α f) (hg : UniformBoundedHolder α g) :
    UniformBoundedHolder α (fun i x => f i x + g i x) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  obtain ⟨N, D, hN, hD, hc, hn⟩ := hg
  refine ⟨M + N, C + D, add_nonneg hM hN, add_nonneg hC hD,
    fun i x => (norm_add_le _ _).trans (add_le_add (hb i x) (hc i x)), ?_⟩
  intro i x y
  have he : (f i x + g i x) - (f i y + g i y) = (f i x - f i y) + (g i x - g i y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hm i x y) (hn i x y)).trans_eq (by ring))

theorem UniformBoundedHolder.neg {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {α : ℝ} {f : ι → X → Y}
    (hf : UniformBoundedHolder α f) : UniformBoundedHolder α (fun i x => -f i x) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨M, C, hM, hC, ?_, ?_⟩
  · intro i x; simpa only [norm_neg] using hb i x
  · intro i x y; simpa only [neg_sub_neg, norm_sub_rev] using hm i x y

theorem UniformBoundedHolder.sub {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {α : ℝ} {f g : ι → X → Y}
    (hf : UniformBoundedHolder α f) (hg : UniformBoundedHolder α g) :
    UniformBoundedHolder α (fun i x => f i x - g i x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem UniformBoundedHolder.mapCLM {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {α : ℝ} {f : ι → X → Y}
    (hf : UniformBoundedHolder α f) (A : Y →L[ℝ] Z) :
    UniformBoundedHolder α (fun i x => A (f i x)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨‖A‖ * M, ‖A‖ * C, by positivity, by positivity, ?_, ?_⟩
  · intro i x
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb i x) (norm_nonneg A))
  · intro i x y
    rw [← map_sub]
    exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hm i x y) (norm_nonneg A)).trans_eq (by ring))

theorem UniformBoundedHolder.clm_apply {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {α : ℝ}
    {T : ι → X → Y →L[ℝ] Z} {f : ι → X → Y}
    (hT : UniformBoundedHolder α T) (hf : UniformBoundedHolder α f) :
    UniformBoundedHolder α (fun i x => T i x (f i x)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hT
  obtain ⟨N, D, hN, hD, hc, hn⟩ := hf
  refine ⟨M * N, M * D + C * N, by positivity, by positivity, ?_, ?_⟩
  · intro i x
    exact ((T i x).le_opNorm _).trans (mul_le_mul (hb i x) (hc i x) (norm_nonneg _) hM)
  · intro i
    exact clm_product_holder hM hC (hb i) (hc i) (hm i) (hn i)

theorem UniformBoundedHolder.bilinear {ι X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {α : ℝ}
    {f : ι → X → Y} {g : ι → X → Z}
    (hf : UniformBoundedHolder α f) (hg : UniformBoundedHolder α g) (B : Y →L[ℝ] Z →L[ℝ] W) :
    UniformBoundedHolder α (fun i x => B (f i x) (g i x)) :=
  (hf.mapCLM B).clm_apply hg

theorem UniformBoundedHolder.smul {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {α : ℝ}
    {c : ι → X → ℝ} {f : ι → X → Y}
    (hc : UniformBoundedHolder α c) (hf : UniformBoundedHolder α f) :
    UniformBoundedHolder α (fun i x => c i x • f i x) :=
  hc.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ)

theorem UniformBoundedHolder.smulRight {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {α : ℝ}
    {p : ι → X → Y →L[ℝ] ℝ} {f : ι → X → Z}
    (hp : UniformBoundedHolder α p) (hf : UniformBoundedHolder α f) :
    UniformBoundedHolder α (fun i x => (p i x).smulRight (f i x)) :=
  hp.bilinear hf (ContinuousLinearMap.smulRightL ℝ Y Z)

theorem UniformBoundedHolder.mapLIE {ι X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {α : ℝ} {f : ι → X → Y}
    (hf : UniformBoundedHolder α f) (A : Y ≃ₗᵢ[ℝ] Z) :
    UniformBoundedHolder α (fun i x => A (f i x)) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := hf
  refine ⟨M, C, hM, hC, ?_, ?_⟩
  · intro i x; rw [A.norm_map]; exact hb i x
  · intro i x y; rw [← A.map_sub, A.norm_map]; exact hm i x y

theorem UniformBoundedHolder.of_compact_c1 {ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    UniformBoundedHolder α (fun (_ : ι) => f) := by
  obtain ⟨M, C, hM, hC, hb, hm⟩ := compact_c1_bounded_holder hf hfc hα hα1
  exact ⟨M, C, hM.le, hC.le, fun _ => hb, fun _ => hm⟩

end Submission.Obl.Entropy__smooth_gaussian_transport
