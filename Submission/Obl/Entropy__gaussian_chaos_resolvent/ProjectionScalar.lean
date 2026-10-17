import Submission.Obl.Entropy__gaussian_chaos_resolvent.Assembly
import Submission.Obl.Entropy__gaussian_chaos_resolvent.ScalarInverse

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Obl.Entropy__gaussian_chaos_resolvent

theorem memLp_coordinate {m : ℕ} (r : Fin m) :
    MemLp (fun x : E m => x r) 2 (gaussian m) := by
  have he : hermiteEuclidean (raiseIndex (0 : Fin m → ℕ) r) = fun x : E m => x r :=
    funext (hermiteEuclidean_raise_zero r)
  rw [← he]
  exact memLp_hermiteEuclidean _

@[simp] theorem integral_coordinate {m : ℕ} (r : Fin m) :
    (∫ x : E m, x r ∂gaussian m) = 0 := by
  have h := integral_hermiteEuclidean_mul (raiseIndex 0 r) 0
  have hn : raiseIndex 0 r ≠ 0 := by
    intro hh
    have := congrFun hh r
    simp at this
  simpa [hn] using h

@[simp] theorem integral_coordinate_mul {m : ℕ} (r s : Fin m) :
    (∫ x : E m, x r * x s ∂gaussian m) = if r = s then 1 else 0 := by
  have h := integral_hermiteEuclidean_mul (raiseIndex 0 r) (raiseIndex 0 s)
  have he : raiseIndex (0 : Fin m → ℕ) r = raiseIndex 0 s ↔ r = s := by
    constructor
    · intro hh
      by_contra hrs
      have := congrFun hh r
      simp [raiseIndex, hrs] at this
    · rintro rfl
      rfl
  simpa [he] using h

noncomputable def linearChaos {m : ℕ} (c : Fin m → ℝ) (x : E m) : ℝ := ∑ r, x r * c r

theorem contDiff_linearChaos {m : ℕ} (c : Fin m → ℝ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (linearChaos c) := by
  apply ContDiff.sum
  intro r _
  exact (EuclideanSpace.proj r : E m →L[ℝ] ℝ).contDiff.mul contDiff_const

theorem coordDeriv_linearChaos {m : ℕ} (c : Fin m → ℝ) (r : Fin m) (x : E m) :
    coordDeriv (linearChaos c) r x = c r := by
  let L : E m →L[ℝ] ℝ := ∑ s, c s • EuclideanSpace.proj s
  have he : linearChaos c = L := by
    funext y
    simp [linearChaos, L, mul_comm]
  rw [he, coordDeriv, L.fderiv]
  simp [L, Pi.single_apply]

theorem memLp_linearChaos {m : ℕ} (c : Fin m → ℝ) :
    MemLp (linearChaos c) 2 (gaussian m) :=
  memLp_finsetSum _ (fun r _ => (memLp_coordinate r).mul_const (c r))

@[simp] theorem integral_linearChaos {m : ℕ} (c : Fin m → ℝ) :
    (∫ x, linearChaos c x ∂gaussian m) = 0 := by
  unfold linearChaos
  rw [integral_finsetSum _ (fun r _ =>
    ((memLp_coordinate r).integrable (by norm_num)).mul_const (c r))]
  simp [integral_mul_const]

theorem integral_coordinate_linearChaos {m : ℕ} (c : Fin m → ℝ) (r : Fin m) :
    (∫ x, x r * linearChaos c x ∂gaussian m) = c r := by
  simp only [linearChaos, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (f := fun s (x : E m) => x r * (x s * c s)) (fun s _ =>
    ((memLp_coordinate r).integrable_mul ((memLp_coordinate s).mul_const (c s))))]
  simp_rw [← mul_assoc, integral_mul_const, integral_coordinate_mul]
  simp

theorem integral_mul_linearChaos {m : ℕ} {f : E m → ℝ} (hf : MemLp f 2 (gaussian m))
    (c : Fin m → ℝ) :
    (∫ x, f x * linearChaos c x ∂gaussian m) =
      ∑ r, c r * ∫ x, x r * f x ∂gaussian m := by
  simp only [linearChaos, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (f := fun r x => f x * (x r * c r)) (fun r _ => hf.integrable_mul ((memLp_coordinate r).mul_const (c r)))]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [← mul_assoc, integral_mul_const]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

theorem integral_sub_square {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x-g x)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ) - 2*(∫ x, f x*g x ∂μ) + ∫ x, (g x)^2 ∂μ := by
  have he (x) : (f x-g x)^2 = (f x)^2 - 2*(f x*g x) + (g x)^2 := by ring
  simp_rw [he]
  have hmul : Integrable (fun x => 2*(f x*g x)) μ := (hf.integrable_mul hg).const_mul 2
  have hsub : Integrable (fun x => (f x)^2-2*(f x*g x)) μ := hf.integrable_sq.sub hmul
  rw [integral_add hsub hg.integrable_sq, integral_sub hf.integrable_sq hmul, integral_const_mul]

noncomputable def firstCoeff {m : ℕ} (f : E m → ℝ) (r : Fin m) : ℝ :=
  ∫ x, x r * f x ∂gaussian m
noncomputable def secondRemainder {m : ℕ} (f : E m → ℝ) (x : E m) : ℝ :=
  f x - linearChaos (firstCoeff f) x

theorem contDiff_secondRemainder {m : ℕ} {f : E m → ℝ}
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (secondRemainder f) :=
  hf.sub (contDiff_linearChaos _)

theorem memLp_secondRemainder {m : ℕ} {f : E m → ℝ} (hf : MemLp f 2 (gaussian m)) :
    MemLp (secondRemainder f) 2 (gaussian m) := hf.sub (memLp_linearChaos _)

theorem coordDeriv_secondRemainder {m : ℕ} {f : E m → ℝ}
    (hf : Differentiable ℝ f) (r : Fin m) (x : E m) :
    coordDeriv (secondRemainder f) r x = coordDeriv f r x - firstCoeff f r := by
  unfold secondRemainder coordDeriv
  rw [fderiv_fun_sub (hf x) ((contDiff_linearChaos _).differentiable (by norm_num) x),
    ContinuousLinearMap.sub_apply]
  rw [show fderiv ℝ (linearChaos (firstCoeff f)) x (PiLp.single 2 r (1 : ℝ)) = firstCoeff f r
    from coordDeriv_linearChaos _ r x]

theorem integral_secondRemainder {m : ℕ} {f : E m → ℝ} (hf : MemLp f 2 (gaussian m))
    (hmean : (∫ x, f x ∂gaussian m) = 0) : (∫ x, secondRemainder f x ∂gaussian m) = 0 := by
  simp only [secondRemainder]
  rw [integral_sub (hf.integrable (by norm_num))
    ((memLp_linearChaos _).integrable (by norm_num)), hmean, integral_linearChaos, sub_self]

theorem integral_coordinate_secondRemainder {m : ℕ} {f : E m → ℝ}
    (hf : MemLp f 2 (gaussian m)) (r : Fin m) :
    (∫ x, x r * secondRemainder f x ∂gaussian m) = 0 := by
  simp only [secondRemainder, mul_sub]
  have h1 : Integrable (fun x : E m => x r*f x) (gaussian m) :=
    (memLp_coordinate r).integrable_mul hf
  have h2 : Integrable (fun x : E m => x r*linearChaos (firstCoeff f) x) (gaussian m) :=
    (memLp_coordinate r).integrable_mul (memLp_linearChaos _)
  rw [integral_sub h1 h2, integral_coordinate_linearChaos]
  exact sub_self _

theorem integral_coordDeriv {m : ℕ} {f : E m → ℝ} (hf : Differentiable ℝ f)
    (hf2 : MemLp f 2 (gaussian m)) (r : Fin m)
    (hdf2 : MemLp (coordDeriv f r) 2 (gaussian m)) :
    (∫ x, coordDeriv f r x ∂gaussian m) = firstCoeff f r := by
  have h := integral_coord_deriv_mul_hermite r hf hf2 hdf2 0
  simpa [coordDeriv, firstCoeff, mul_comm] using h

theorem integral_secondRemainder_sq {m : ℕ} {f : E m → ℝ}
    (hf : MemLp f 2 (gaussian m)) :
    (∫ x, (secondRemainder f x)^2 ∂gaussian m) =
      (∫ x, (f x)^2 ∂gaussian m) - ∑ r, (firstCoeff f r)^2 := by
  have hcross : (∫ x, f x*linearChaos (firstCoeff f) x ∂gaussian m) =
      ∑ r, (firstCoeff f r)^2 := by
    simpa only [firstCoeff, pow_two] using integral_mul_linearChaos hf (firstCoeff f)
  have hlin : (∫ x, (linearChaos (firstCoeff f) x)^2 ∂gaussian m) =
      ∑ r, (firstCoeff f r)^2 := by
    simpa only [integral_coordinate_linearChaos, pow_two] using
      integral_mul_linearChaos (memLp_linearChaos (firstCoeff f)) (firstCoeff f)
  change (∫ x, (f x-linearChaos (firstCoeff f) x)^2 ∂gaussian m) = _
  rw [integral_sub_square hf (memLp_linearChaos _), hcross, hlin]
  ring

theorem integral_coordDeriv_secondRemainder_sq {m : ℕ} {f : E m → ℝ}
    (hf : Differentiable ℝ f) (hf2 : MemLp f 2 (gaussian m)) (r : Fin m)
    (hdf2 : MemLp (coordDeriv f r) 2 (gaussian m)) :
    (∫ x, (coordDeriv (secondRemainder f) r x)^2 ∂gaussian m) =
      (∫ x, (coordDeriv f r x)^2 ∂gaussian m) - (firstCoeff f r)^2 := by
  simp_rw [coordDeriv_secondRemainder hf]
  rw [integral_sub_square hdf2 (memLp_const (firstCoeff f r)), integral_mul_const,
    integral_coordDeriv hf hf2 r hdf2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem scalar_projection_cancellation {m : ℕ} {f : E m → ℝ}
    (hf : Differentiable ℝ f) (hf2 : MemLp f 2 (gaussian m))
    (hdf2 : ∀ r, MemLp (coordDeriv f r) 2 (gaussian m)) :
    (∫ x, (f x)^2 ∂gaussian m) - (∑ r, ∫ x, (coordDeriv f r x)^2 ∂gaussian m) =
      (∫ x, (secondRemainder f x)^2 ∂gaussian m) -
        (∑ r, ∫ x, (coordDeriv (secondRemainder f) r x)^2 ∂gaussian m) := by
  rw [integral_secondRemainder_sq hf2]
  simp_rw [integral_coordDeriv_secondRemainder_sq hf hf2 _ (hdf2 _)]
  rw [Finset.sum_sub_distrib]
  ring

end Submission.Obl.Entropy__gaussian_chaos_resolvent
