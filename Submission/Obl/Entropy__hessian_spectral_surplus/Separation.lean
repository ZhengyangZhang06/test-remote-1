import Submission.Obl.Entropy__hessian_spectral_surplus.SpectralWeights

open scoped BigOperators Topology
open Matrix Filter MeasureTheory

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def surplusWeight (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (1 + (if min a b < -3 then 0 else if min a b < -2 then 19/100
    else if min a b < -1 then 38/100 else 68/100)) / 16 *
    (1 + (f a - f b) ^ 2 / 30 + (f a - f b) ^ 4 / 1680) * (f a - f b) ^ 2

lemma surplusWeight_nonneg (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ surplusWeight f a b := by
  unfold surplusWeight
  split_ifs <;> positivity

noncomputable def spectralMoment {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Z : Matrix n n ℝ) (k : ℕ) : ℝ :=
  ∑ i, ∑ j, (f (hA.eigenvalues i) - f (hA.eigenvalues j)) ^ (2 * k) *
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z * hA.eigenvectorUnitary) i j ^ 2

noncomputable def spectralCutMoment {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (c : ℝ) (Z : Matrix n n ℝ) (k : ℕ) : ℝ :=
  ∑ i, ∑ j, (if c ≤ min (hA.eigenvalues i) (hA.eigenvalues j) then 1 else 0) *
    (f (hA.eigenvalues i) - f (hA.eigenvalues j)) ^ (2 * k) *
    ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z * hA.eigenvectorUnitary) i j ^ 2

lemma separation_expansion {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Z : Matrix n n ℝ) :
    (∑ i, ∑ j, surplusWeight f (hA.eigenvalues i) (hA.eigenvalues j) *
      ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z * hA.eigenvectorUnitary) i j ^ 2) =
      (spectralMoment hA f Z 1 + spectralMoment hA f Z 2 / 30 +
        spectralMoment hA f Z 3 / 1680 +
        (19/100) * (spectralCutMoment hA f (-3) Z 1 + spectralCutMoment hA f (-3) Z 2 / 30 +
          spectralCutMoment hA f (-3) Z 3 / 1680) +
        (19/100) * (spectralCutMoment hA f (-2) Z 1 + spectralCutMoment hA f (-2) Z 2 / 30 +
          spectralCutMoment hA f (-2) Z 3 / 1680) +
        (30/100) * (spectralCutMoment hA f (-1) Z 1 + spectralCutMoment hA f (-1) Z 2 / 30 +
          spectralCutMoment hA f (-1) Z 3 / 1680)) / 16 := by
  simp only [spectralMoment, spectralCutMoment, Finset.sum_div, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold surplusWeight
  by_cases h3 : min (hA.eigenvalues i) (hA.eigenvalues j) < -3
  · have h2 : min (hA.eigenvalues i) (hA.eigenvalues j) < -2 := by linarith
    have h1 : min (hA.eigenvalues i) (hA.eigenvalues j) < -1 := by linarith
    simp [h3, h2, h1, not_le.mpr h3, not_le.mpr h2, not_le.mpr h1]
    ring
  · by_cases h2 : min (hA.eigenvalues i) (hA.eigenvalues j) < -2
    · have h1 : min (hA.eigenvalues i) (hA.eigenvalues j) < -1 := by linarith
      simp [h3, h2, h1, le_of_not_gt h3, not_le.mpr h2, not_le.mpr h1]
      ring
    · by_cases h1 : min (hA.eigenvalues i) (hA.eigenvalues j) < -1
      · simp [h3, h2, h1, le_of_not_gt h3, le_of_not_gt h2, not_le.mpr h1]
        ring
      · simp [h3, h2, h1, le_of_not_gt h3, le_of_not_gt h2, le_of_not_gt h1]
        ring

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

lemma measurable_spectralMoment {A Z : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f)
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) (k : ℕ) :
    Measurable (fun x => spectralMoment (hA x) f (Z x) k) := by
  have hL (i j : n) := ((continuous_cfc_matrix hA hAc hf).matrix_elem i j).measurable
  have hC := measurable_iterComm_entries hL hZ k
  have hm : Measurable (fun x => ∑ i, ∑ j, iterComm (cfc f (A x)) (Z x) k i j ^ 2) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hC i j).pow_const 2
  convert! hm using 1
  funext x
  exact (commutator_squareSum (hA x) f (Z x) k).symm

lemma measurable_spectralCutMoment {A Z : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f)
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) (c : ℝ) (k : ℕ) :
    Measurable (fun x => spectralCutMoment (hA x) f c (Z x) k) := by
  let P : X → Matrix n n ℝ := fun x => cfc (fun t : ℝ => if c ≤ t then 1 else 0) (A x)
  have hP : ∀ i j, Measurable (fun x => P x i j) := measurable_cfc_cutoff hA hAc c
  have hL (i j : n) := ((continuous_cfc_matrix hA hAc hf).matrix_elem i j).measurable
  have hC := measurable_iterComm_entries hL hZ k
  have hPC := measurable_matrix_mul_entries (measurable_matrix_mul_entries hP hC) hP
  have hm : Measurable (fun x => ∑ i, ∑ j,
      (P x * iterComm (cfc f (A x)) (Z x) k * P x) i j ^ 2) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hPC i j).pow_const 2
  convert! hm using 1
  funext x
  exact (cutoff_commutator_squareSum (hA x) f c (Z x) k).symm

/-- The full piecewise spectral separation weight is measurable in fixed coordinates. -/
lemma measurable_separation {A Z : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f)
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) :
    Measurable (fun x => ∑ i, ∑ j, surplusWeight f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
      (((hA x).eigenvectorUnitary : Matrix n n ℝ).transpose * Z x *
        (hA x).eigenvectorUnitary) i j ^ 2) := by
  simp_rw [separation_expansion]
  have hM := measurable_spectralMoment hA hAc hf hZ
  have hC := measurable_spectralCutMoment hA hAc hf hZ
  exact (((((hM 1).add ((hM 2).div_const 30)).add ((hM 3).div_const 1680)).add
    ((((hC (-3) 1).add ((hC (-3) 2).div_const 30)).add
      ((hC (-3) 3).div_const 1680)).const_mul (19/100))).add
    ((((hC (-2) 1).add ((hC (-2) 2).div_const 30)).add
      ((hC (-2) 3).div_const 1680)).const_mul (19/100))).add
    ((((hC (-1) 1).add ((hC (-1) 2).div_const 30)).add
      ((hC (-1) 3).div_const 1680)).const_mul (30/100)) |>.div_const 16

end Submission.Obl.Entropy__hessian_spectral_surplus
