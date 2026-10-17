import Mathlib

/-!
Limits of Jacobians, used to extract the homogeneous terms at the origin in
Section 6, Lemma 6.1 of the supplied paper.
-/

namespace Submission.Lib.JacobianCompatibility

open Filter Set
open scoped Topology

/-- A limit of derivatives, uniform on every ball, has a primitive when the
primitives are normalized to vanish at the origin. -/
theorem exists_primitive_of_tendstoUniformlyOn_ball
    {ι E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {l : Filter ι} [NeBot l]
    (f : ι → E → V) (f' : ι → E → E →L[ℝ] V) (g' : E → E →L[ℝ] V)
    (hf : ∀ n x, HasFDerivAt (f n) (f' n x) x)
    (hzero : ∀ n, f n 0 = 0)
    (hlim : ∀ r : ℝ, TendstoUniformlyOn f' g' l (Metric.ball 0 r)) :
    ∃ g : E → V, ∀ x, HasFDerivAt g (g' x) x := by
  have hbase : Cauchy (Filter.map (fun n ↦ f n 0) l) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : V)) l (𝓝 0)).cauchy_map
  have hpoint : ∀ x : E, ∃ y : V, Tendsto (fun n ↦ f n x) l (𝓝 y) := by
    intro x
    apply cauchy_map_iff_exists_tendsto.mp
    exact (uniformCauchySeqOn_ball_of_fderiv (hlim (‖x‖ + 1)).uniformCauchySeqOn
      (fun n y _ ↦ hf n y) hbase).cauchy_map (by simp)
  choose g hg using hpoint
  refine ⟨g, fun x ↦ ?_⟩
  exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball (hlim (‖x‖ + 1))
    (fun n y _ ↦ hf n y) (fun y _ ↦ hg y) (by simp)

/-- A continuous-linear-map field is a Jacobian of a differentiable map. -/
def HasPrimitive {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (J : E → E →L[ℝ] V) : Prop :=
  ∃ f : E → V, ∀ x, HasFDerivAt f (J x) x

namespace HasPrimitive

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J K : E → E →L[ℝ] V}

lemma const (C : E →L[ℝ] V) : HasPrimitive (fun _ : E ↦ C) :=
  ⟨C, fun _ ↦ C.hasFDerivAt⟩

lemma add (hJ : HasPrimitive J) (hK : HasPrimitive K) :
    HasPrimitive (fun x ↦ J x + K x) := by
  obtain ⟨f, hf⟩ := hJ
  obtain ⟨g, hg⟩ := hK
  exact ⟨fun x ↦ f x + g x, fun x ↦ (hf x).add (hg x)⟩

lemma sub (hJ : HasPrimitive J) (hK : HasPrimitive K) :
    HasPrimitive (fun x ↦ J x - K x) := by
  obtain ⟨f, hf⟩ := hJ
  obtain ⟨g, hg⟩ := hK
  exact ⟨fun x ↦ f x - g x, fun x ↦ (hf x).sub (hg x)⟩

lemma smul (hJ : HasPrimitive J) (c : ℝ) :
    HasPrimitive (fun x ↦ c • J x) := by
  obtain ⟨f, hf⟩ := hJ
  exact ⟨fun x ↦ c • f x, fun x ↦ (hf x).const_smul c⟩

lemma precomp_smul (hJ : HasPrimitive J) (t : ℝ) :
    HasPrimitive (fun x ↦ J (t • x)) := by
  by_cases ht : t = 0
  · simpa only [ht, zero_smul] using const (J 0)
  obtain ⟨f, hf⟩ := hJ
  refine ⟨fun x ↦ t⁻¹ • f (t • x), fun x ↦ ?_⟩
  have h := ((hf (t • x)).comp x ((hasFDerivAt_id x).const_smul t)).const_smul t⁻¹
  have heq : t⁻¹ • ((J (t • x)).comp (t • ContinuousLinearMap.id ℝ E)) = J (t • x) := by
    ext v
    simp [smul_smul, ht]
  rw [heq] at h
  exact h

lemma of_tendstoUniformlyOn_ball [CompleteSpace V]
    {ι : Type*} {l : Filter ι} [NeBot l]
    (Jseq : ι → E → E →L[ℝ] V)
    (hseq : ∀ i, HasPrimitive (Jseq i))
    (hlim : ∀ r : ℝ, TendstoUniformlyOn Jseq J l (Metric.ball 0 r)) :
    HasPrimitive J := by
  choose f hf using hseq
  exact exists_primitive_of_tendstoUniformlyOn_ball
    (fun i x ↦ f i x - f i 0) Jseq J
    (fun i x ↦ (hf i x).sub_const (f i 0)) (by simp) hlim

end HasPrimitive

end Submission.Lib.JacobianCompatibility
