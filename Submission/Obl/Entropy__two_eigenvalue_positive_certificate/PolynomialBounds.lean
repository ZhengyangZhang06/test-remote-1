import Mathlib

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def millsPolynomial (u : ℝ) : ℝ := 1 - u + 3 * u ^ 2 - 15 * u ^ 3 + 105 * u ^ 4 - 945 * u ^ 5 + 10395 * u ^ 6

noncomputable def millsPolynomialLower (u : ℝ) : ℝ := 1 - u + 3 * u ^ 2 - 15 * u ^ 3 + 105 * u ^ 4 - 945 * u ^ 5 + 10395 * u ^ 6 - 135135 * u ^ 7

noncomputable def hazardPolynomial (u : ℝ) : ℝ := 1 + u - 2 * u ^ 2 + 10 * u ^ 3 - 74 * u ^ 4

noncomputable def hazardPolynomialUpper (u : ℝ) : ℝ := 1 + u - 2 * u ^ 2 + 10 * u ^ 3 - 74 * u ^ 4 + 706 * u ^ 5

theorem millsPolynomialLower_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    1 - u ≤ millsPolynomialLower u := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 3 * u ^ 2 - 15 * u ^ 3 + 105 * u ^ 4 - 945 * u ^ 5 + 10395 * u ^ 6 - 135135 * u ^ 7 =
      u ^ 2 * ((3 / 1 : ℝ) * (1 - 100 * u) ^ 5 +
      (297 / 20 : ℝ) * (100 * u) * (1 - 100 * u) ^ 4 +
      (58821 / 2000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) ^ 3 +
      (5826111 / 200000 : ℝ) * (100 * u) ^ 3 * (1 - 100 * u) ^ 2 +
      (288594279 / 20000000 : ℝ) * (100 * u) ^ 4 * (1 - 100 * u) +
      (5719290873 / 2000000000 : ℝ) * (100 * u) ^ 5) := by ring
  have hn : 0 ≤ 3 * u ^ 2 - 15 * u ^ 3 + 105 * u ^ 4 - 945 * u ^ 5 + 10395 * u ^ 6 - 135135 * u ^ 7 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

theorem millsPolynomial_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    millsPolynomial u ≤ 1 - u + 3 * u ^ 2 := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 15 * u ^ 3 - 105 * u ^ 4 + 945 * u ^ 5 - 10395 * u ^ 6 =
      u ^ 3 * ((15 / 1 : ℝ) * (1 - 100 * u) ^ 3 +
      (879 / 20 : ℝ) * (100 * u) * (1 - 100 * u) ^ 2 +
      (85989 / 2000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) +
      (2806821 / 200000 : ℝ) * (100 * u) ^ 3) := by ring
  have hn : 0 ≤ 15 * u ^ 3 - 105 * u ^ 4 + 945 * u ^ 5 - 10395 * u ^ 6 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

theorem hazardPolynomial_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    0 ≤ hazardPolynomial u := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 1 + u - 2 * u ^ 2 + 10 * u ^ 3 - 74 * u ^ 4 =
      (1 / 1 : ℝ) * (1 - 100 * u) ^ 4 +
      (401 / 100 : ℝ) * (100 * u) * (1 - 100 * u) ^ 3 +
      (30149 / 5000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) ^ 2 +
      (402961 / 100000 : ℝ) * (100 * u) ^ 3 * (1 - 100 * u) +
      (50490463 / 50000000 : ℝ) * (100 * u) ^ 4 := by ring
  have hn : 0 ≤ 1 + u - 2 * u ^ 2 + 10 * u ^ 3 - 74 * u ^ 4 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

theorem hazardPolynomialUpper_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    hazardPolynomialUpper u ≤ 1 + u := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 2 * u ^ 2 - 10 * u ^ 3 + 74 * u ^ 4 - 706 * u ^ 5 =
      u ^ 2 * ((2 / 1 : ℝ) * (1 - 100 * u) ^ 3 +
      (59 / 10 : ℝ) * (100 * u) * (1 - 100 * u) ^ 2 +
      (29037 / 5000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) +
      (953347 / 500000 : ℝ) * (100 * u) ^ 3) := by ring
  have hn : 0 ≤ 2 * u ^ 2 - 10 * u ^ 3 + 74 * u ^ 4 - 706 * u ^ 5 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

theorem mills_hazard_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    millsPolynomial u * hazardPolynomial u ≤ 1 := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 706 * u ^ 5 - 8868 * u ^ 6 - 14445 * u ^ 7 + 38010 * u ^ 8 - 173880 * u ^ 9 + 769230 * u ^ 10 =
      u ^ 5 * ((706 / 1 : ℝ) * (1 - 100 * u) ^ 5 +
      (86033 / 25 : ℝ) * (100 * u) * (1 - 100 * u) ^ 4 +
      (13407671 / 2000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) ^ 3 +
      (652362451 / 100000 : ℝ) * (100 * u) ^ 3 * (1 - 100 * u) ^ 2 +
      (7927551953 / 2500000 : ℝ) * (100 * u) ^ 4 * (1 - 100 * u) +
      (615911848123 / 1000000000 : ℝ) * (100 * u) ^ 5) := by ring
  have hn : 0 ≤ 706 * u ^ 5 - 8868 * u ^ 6 - 14445 * u ^ 7 + 38010 * u ^ 8 - 173880 * u ^ 9 + 769230 * u ^ 10 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

theorem mills_hazard_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 100) :
    1 ≤ millsPolynomialLower u * hazardPolynomialUpper u := by
  have hu : 0 ≤ 1 - 100 * u := by linarith
  have he : 8162 * u ^ 6 - 118572 * u ^ 7 - 183735 * u ^ 8 + 518280 * u ^ 9 - 2787750 * u ^ 10 + 17338860 * u ^ 11 - 95405310 * u ^ 12 =
      u ^ 6 * ((8162 / 1 : ℝ) * (1 - 100 * u) ^ 6 +
      (1194657 / 25 : ℝ) * (100 * u) * (1 - 100 * u) ^ 5 +
      (232966053 / 2000 : ℝ) * (100 * u) ^ 2 * (1 - 100 * u) ^ 4 +
      (3782745607 / 25000 : ℝ) * (100 * u) ^ 3 * (1 - 100 * u) ^ 3 +
      (8837126877 / 80000 : ℝ) * (100 * u) ^ 4 * (1 - 100 * u) ^ 2 +
      (21485703409443 / 500000000 : ℝ) * (100 * u) ^ 5 * (1 - 100 * u) +
      (695839854098069 / 100000000000 : ℝ) * (100 * u) ^ 6) := by ring
  have hn : 0 ≤ 8162 * u ^ 6 - 118572 * u ^ 7 - 183735 * u ^ 8 + 518280 * u ^ 9 - 2787750 * u ^ 10 + 17338860 * u ^ 11 - 95405310 * u ^ 12 := by
    rw [he]
    positivity
  dsimp [millsPolynomial, millsPolynomialLower, hazardPolynomial, hazardPolynomialUpper]
  nlinarith only [hn]

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
