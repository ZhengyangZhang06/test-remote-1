import Submission.Obl.Entropy__smooth_gaussian_transport.DifferentiableTransport
import Submission.Obl.Entropy__smooth_gaussian_transport.DepthEstimate

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__smooth_gaussian_transport

noncomputable def symmetricAverage {m : ℕ} (u : E m → ℝ) (h x : E m) : ℝ :=
  (u (x + h) + u (x - h)) / 2

theorem symmetricAverage_convex {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (h : E m) : ConvexOn ℝ univ (symmetricAverage u h) := by
  have hc := ((translate_convex hu h).add (translate_convex hu (-h))).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert! hc using 1
  ext x
  simp only [symmetricAverage, Pi.add_apply, smul_eq_mul, sub_eq_add_neg]
  ring

theorem symmetricAverage_strictConvex {m : ℕ} {u : E m → ℝ}
    (hu : StrictConvexOn ℝ univ u) (h : E m) :
    StrictConvexOn ℝ univ (symmetricAverage u h) := by
  have hp : StrictConvexOn ℝ univ (fun x => u (x + h)) := by
    simpa only [preimage_univ, Function.comp_def] using hu.translate_left h
  have hn : StrictConvexOn ℝ univ (fun x => u (x - h)) := by
    simpa only [sub_eq_add_neg, preimage_univ, Function.comp_def] using hu.translate_left (-h)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h₁ := hp.2 hx hy hxy ha hb hab
  have h₂ := hn.2 hx hy hxy ha hb hab
  simp only [symmetricAverage, smul_eq_mul] at *
  nlinarith

theorem le_symmetricAverage {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (h x : E m) : u x ≤ symmetricAverage u h x := by
  have hp := hu.2 (mem_univ (x + h)) (mem_univ (x - h))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x - h) = x := by module
  rw [he] at hp
  change u x ≤ (u (x + h) + u (x - h)) / 2
  simp only [smul_eq_mul] at hp
  linarith

theorem symmetricAverage_conjugateDomain {m : ℕ} {u : E m → ℝ}
    (hu : ConvexOn ℝ univ u) (hdom : conjugateDomain u = univ) (h : E m) :
    conjugateDomain (symmetricAverage u h) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨C, hC⟩ := bounded_conjugate_values hdom p
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (sub_le_sub_left (le_symmetricAverage hu h x) _).trans (hC (mem_range_self x))

theorem symmetricAverage_contDiff {m : ℕ} {u : E m → ℝ} {n : WithTop ENat}
    (hu : ContDiff ℝ n u) (h : E m) : ContDiff ℝ n (symmetricAverage u h) :=
  ((hu.comp (contDiff_id.add contDiff_const)).add
    (hu.comp (contDiff_id.sub contDiff_const))).div_const 2

theorem gradient_symmetricAverage {m : ℕ} {u : E m → ℝ}
    (hu : Differentiable ℝ u) (h x : E m) :
    gradient (symmetricAverage u h) x =
      (1 / 2 : ℝ) • (gradient u (x + h) + gradient u (x - h)) := by
  have hp := (hasFDerivAt_comp_add_right h).mpr (hu (x + h)).hasFDerivAt
  have hn := (hasFDerivAt_comp_sub h).mpr (hu (x - h)).hasFDerivAt
  have hd : HasFDerivAt (symmetricAverage u h)
      ((1 / 2 : ℝ) • (fderiv ℝ u (x + h) + fderiv ℝ u (x - h))) x := by
    convert! (hp.add hn).const_mul (1 / 2 : ℝ) using 1
    ext y
    simp only [symmetricAverage, Pi.add_apply]
    ring
  simp only [gradient, hd.fderiv, map_smul, map_add]

theorem strict_subgradient_support {m : ℕ} {u : E m → ℝ}
    (hu : StrictConvexOn ℝ univ u) {x p : E m} (hp : IsSubgradient u x p)
    {y : E m} (hxy : x ≠ y) : u x + inner ℝ p (y - x) < u y := by
  have hc := hu.2 (mem_univ x) (mem_univ y) hxy
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hs := hp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  have he : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y - x = (1 / 2 : ℝ) • (y - x) := by module
  rw [he, real_inner_smul_right] at hs
  simp only [smul_eq_mul] at hc
  linarith

theorem gradient_injective_of_strictConvex {m : ℕ} {u : E m → ℝ}
    (hu : StrictConvexOn ℝ univ u) (hd : Differentiable ℝ u) :
    Function.Injective (gradient u) := by
  intro x y he
  by_contra hxy
  have h₁ := strict_subgradient_support hu (convex_gradient_support hu.convexOn (hd x)) hxy
  have h₂ := convex_gradient_support hu.convexOn (hd y) x
  rw [← he, ← neg_sub y x, inner_neg_right] at h₂
  linarith

end Submission.Obl.Entropy__smooth_gaussian_transport
