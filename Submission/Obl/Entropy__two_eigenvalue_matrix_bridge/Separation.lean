import Submission.Obl.Entropy__two_eigenvalue_matrix_bridge.MatrixL2

open scoped BigOperators Topology
open Matrix MeasureTheory Filter

namespace Submission.Obl.Entropy__two_eigenvalue_matrix_bridge

open Submission.Lib.PairEstimate

variable {n Ω : Type*} [Fintype n] [DecidableEq n]

noncomputable def gapWeight (v : ℝ → ℝ) (a c : ℝ) : ℝ :=
  (1 + (if min a c < -3 then 0 else if min a c < -2 then 19/100
    else if min a c < -1 then 38/100 else 68/100)) / 16 *
    (1 + (v a - v c)^2/30 + (v a - v c)^4/1680) * (v a - v c)^2

lemma cut_min (t a c : ℝ) : cut t (min a c) = cut t a * cut t c := by
  simp only [cut, le_min_iff]
  split_ifs <;> norm_num <;> tauto

lemma step_cut (z : ℝ) :
    (if z < -3 then (0 : ℝ) else if z < -2 then 19/100
      else if z < -1 then 38/100 else 68/100) =
      (19/100) * cut (-3) z + (19/100) * cut (-2) z + (3/10) * cut (-1) z := by
  unfold cut
  split_ifs <;> norm_num at * <;> linarith

noncomputable def momentEnergy (L Z : Matrix n n ℝ) : ℝ :=
  squareEnergy (iterComm L 1 Z) + squareEnergy (iterComm L 2 Z) / 30 +
    squareEnergy (iterComm L 3 Z) / 1680

noncomputable def projectedMomentEnergy (P L Z : Matrix n n ℝ) : ℝ :=
  squareEnergy (P * iterComm L 1 Z * P) + squareEnergy (P * iterComm L 2 Z * P) / 30 +
    squareEnergy (P * iterComm L 3 Z * P) / 1680

noncomputable def separationEnergy (v : ℝ → ℝ) (A Z : Matrix n n ℝ) : ℝ :=
  (momentEnergy (cfc v A) Z +
    (19/100) * projectedMomentEnergy (cfc (cut (-3)) A) (cfc v A) Z +
    (19/100) * projectedMomentEnergy (cfc (cut (-2)) A) (cfc v A) Z +
    (3/10) * projectedMomentEnergy (cfc (cut (-1)) A) (cfc v A) Z) / 16

lemma momentEnergy_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) :
    momentEnergy (cfc v A) Z = ∑ i, ∑ j,
      ((v (hA.eigenvalues i) - v (hA.eigenvalues j))^2 +
        (v (hA.eigenvalues i) - v (hA.eigenvalues j))^4/30 +
        (v (hA.eigenvalues i) - v (hA.eigenvalues j))^6/1680) *
      ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
        hA.eigenvectorUnitary) i j ^ 2 := by
  unfold momentEnergy
  simp only [iterComm_energy hA, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma projectedMomentEnergy_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) (t : ℝ) :
    projectedMomentEnergy (cfc (cut t) A) (cfc v A) Z = ∑ i, ∑ j,
      cut t (hA.eigenvalues i) * cut t (hA.eigenvalues j) *
      ((v (hA.eigenvalues i) - v (hA.eigenvalues j))^2 +
        (v (hA.eigenvalues i) - v (hA.eigenvalues j))^4/30 +
        (v (hA.eigenvalues i) - v (hA.eigenvalues j))^6/1680) *
      ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
        hA.eigenvectorUnitary) i j ^ 2 := by
  unfold projectedMomentEnergy
  simp only [projected_iterComm_energy hA, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma separationEnergy_eigenbasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : ℝ → ℝ) (Z : Matrix n n ℝ) :
    separationEnergy v A Z = ∑ i, ∑ j,
      gapWeight v (hA.eigenvalues i) (hA.eigenvalues j) *
        ((hA.eigenvectorUnitary : Matrix n n ℝ).transpose * Z *
          hA.eigenvectorUnitary) i j ^ 2 := by
  unfold separationEnergy
  rw [momentEnergy_eigenbasis hA]
  simp only [projectedMomentEnergy_eigenbasis hA, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold gapWeight
  rw [step_cut]
  simp only [cut_min]
  ring

open scoped Matrix.Norms.L2Operator in
lemma continuous_cfc_entries [TopologicalSpace Ω]
    (A : Ω → Matrix n n ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) (v : ℝ → ℝ) (hv : Continuous v) (i j : n) :
    Continuous (fun x => cfc v (A x) i j) := by
  have hh : Continuous (fun x => cfc v (A x)) :=
    hAc.cfc_of_mem_nhdsSet _ (s := Set.univ) Filter.univ_mem
      (fun x => (hA x).isSelfAdjoint) hv.continuousOn
  exact (continuous_apply j).comp ((continuous_apply i).comp hh)

section Measure
variable [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
variable {μ : Measure Ω}

lemma integrable_separationEnergy (A Z : Ω → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian) (hAc : Continuous A)
    (hAb : ∃ R : ℝ, 0 ≤ R ∧ ∀ x i j, |A x i j| ≤ R)
    (hZ : ∀ i j, MemLp (fun x => Z x i j) 2 μ)
    (v : ℝ → ℝ) (hv : Continuous v) :
    Integrable (fun x => separationEnergy v (A x) (Z x)) μ := by
  have hLc (i j : n) : AEStronglyMeasurable (fun x => cfc v (A x) i j) μ :=
    (continuous_cfc_entries A hA hAc v hv i j).aestronglyMeasurable
  have hLb := bounded_cfc_entries A hA hAb v hv
  have hI (k : ℕ) := l2_iterComm hZ hLc hLb k
  have hEc (k : ℕ) : Integrable (fun x => squareEnergy (iterComm (cfc v (A x)) k (Z x))) μ :=
    integrable_squareSum (hI k)
  have hPc (t : ℝ) (i j : n) :
      AEStronglyMeasurable (fun x => cfc (cut t) (A x) i j) μ :=
    (measurable_cfc_cut A hA hAc t i j).aestronglyMeasurable
  have hPb (t : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j, |cfc (cut t) (A x) i j| ≤ C := by
    refine ⟨Fintype.card n, Nat.cast_nonneg _, fun x i j => ?_⟩
    simpa only [mul_one] using cfc_entry_bound (hA x) (cut t) zero_le_one
      (fun _ => cut_abs_le _ _) i j
  have hPE (t : ℝ) (k : ℕ) : Integrable (fun x => squareEnergy
      (cfc (cut t) (A x) * iterComm (cfc v (A x)) k (Z x) * cfc (cut t) (A x))) μ :=
    integrable_squareSum (l2_mul_bounded_right
      (l2_mul_bounded_left (hI k) (hPc t) (hPb t)) (hPc t) (hPb t))
  have hM : Integrable (fun x => momentEnergy (cfc v (A x)) (Z x)) μ :=
    ((hEc 1).add ((hEc 2).div_const 30)).add ((hEc 3).div_const 1680)
  have hPM (t : ℝ) : Integrable (fun x =>
      projectedMomentEnergy (cfc (cut t) (A x)) (cfc v (A x)) (Z x)) μ :=
    ((hPE t 1).add ((hPE t 2).div_const 30)).add ((hPE t 3).div_const 1680)
  exact (((hM.add ((hPM (-3)).const_mul (19/100))).add
    ((hPM (-2)).const_mul (19/100))).add ((hPM (-1)).const_mul (3/10))).div_const 16

lemma integrable_separation_spectral (A Z : Ω → Matrix n n ℝ)
    (hA : ∀ x, (A x).IsHermitian) (hAc : Continuous A)
    (hAb : ∃ R : ℝ, 0 ≤ R ∧ ∀ x i j, |A x i j| ≤ R)
    (hZ : ∀ i j, MemLp (fun x => Z x i j) 2 μ)
    (v : ℝ → ℝ) (hv : Continuous v) :
    Integrable (fun x => ∑ i, ∑ j,
      gapWeight v ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        (((hA x).eigenvectorUnitary : Matrix n n ℝ).transpose * Z x *
          (hA x).eigenvectorUnitary) i j ^ 2) μ := by
  convert integrable_separationEnergy A Z hA hAc hAb hZ v hv using 1
  funext x
  exact (separationEnergy_eigenbasis (hA x) v (Z x)).symm

end Measure

end Submission.Obl.Entropy__two_eigenvalue_matrix_bridge
