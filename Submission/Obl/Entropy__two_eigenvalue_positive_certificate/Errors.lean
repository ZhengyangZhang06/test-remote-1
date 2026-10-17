import Submission.Obl.Entropy__two_eigenvalue_positive_certificate.PolynomialBounds

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Submission.Obl.Entropy__two_eigenvalue_positive_certificate

noncomputable def bRemainder (u w e h s : ℝ) : ℝ :=
  15 * u * w +
  ((-111 / 2)) * u ^ 2 +
  1 * u ^ 2 * s +
  (-105) * u ^ 2 * w +
  (975 / 2) * u ^ 3 +
  (-3) * u ^ 3 * s +
  945 * u ^ 3 * w +
  ((-10605 / 2)) * u ^ 4 +
  15 * u ^ 4 * s +
  (-10395) * u ^ 4 * w +
  945 * u ^ 5 +
  (-105) * u ^ 5 * s +
  ((-1 / 2)) * u ^ 5 * e +
  (-1) * u ^ 5 * w * e +
  (-10395) * u ^ 6 +
  945 * u ^ 6 * s +
  (-10395) * u ^ 7 * s +
  (-1) * u ^ 7 * e +
  (-1) * u ^ 8 * e * s

theorem bRemainder_bound {u w e h s : ℝ}
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1611 / 50000)
    (he : |e| ≤ 135135) (hh : |h| ≤ 706) (hs : |s| ≤ 3) :
    |bRemainder u w e h s| ≤ (3 / 250) := by
  have h0 : |15 * u * w| ≤ (4833 / 1000000) := by
    calc
      _ = 15 * |u| * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 15 * (1 / 100) * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h1 : |((-111 / 2)) * u ^ 2| ≤ (111 / 20000) := by
    calc
      _ = (111 / 2) * |u| ^ 2 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (111 / 2) * (1 / 100) ^ 2 := by gcongr
      _ = _ := by norm_num
  have h2 : |1 * u ^ 2 * s| ≤ (3 / 10000) := by
    calc
      _ = 1 * |u| ^ 2 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 2 * 3 := by gcongr
      _ = _ := by norm_num
  have h3 : |(-105) * u ^ 2 * w| ≤ (33831 / 100000000) := by
    calc
      _ = 105 * |u| ^ 2 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 105 * (1 / 100) ^ 2 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h4 : |(975 / 2) * u ^ 3| ≤ (39 / 80000) := by
    calc
      _ = (975 / 2) * |u| ^ 3 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (975 / 2) * (1 / 100) ^ 3 := by gcongr
      _ = _ := by norm_num
  have h5 : |(-3) * u ^ 3 * s| ≤ (9 / 1000000) := by
    calc
      _ = 3 * |u| ^ 3 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 3 * (1 / 100) ^ 3 * 3 := by gcongr
      _ = _ := by norm_num
  have h6 : |945 * u ^ 3 * w| ≤ (304479 / 10000000000) := by
    calc
      _ = 945 * |u| ^ 3 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 945 * (1 / 100) ^ 3 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h7 : |((-10605 / 2)) * u ^ 4| ≤ (2121 / 40000000) := by
    calc
      _ = (10605 / 2) * |u| ^ 4 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (10605 / 2) * (1 / 100) ^ 4 := by gcongr
      _ = _ := by norm_num
  have h8 : |15 * u ^ 4 * s| ≤ (9 / 20000000) := by
    calc
      _ = 15 * |u| ^ 4 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 15 * (1 / 100) ^ 4 * 3 := by gcongr
      _ = _ := by norm_num
  have h9 : |(-10395) * u ^ 4 * w| ≤ (3349269 / 1000000000000) := by
    calc
      _ = 10395 * |u| ^ 4 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 4 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h10 : |945 * u ^ 5| ≤ (189 / 2000000000) := by
    calc
      _ = 945 * |u| ^ 5 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 945 * (1 / 100) ^ 5 := by gcongr
      _ = _ := by norm_num
  have h11 : |(-105) * u ^ 5 * s| ≤ (63 / 2000000000) := by
    calc
      _ = 105 * |u| ^ 5 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 105 * (1 / 100) ^ 5 * 3 := by gcongr
      _ = _ := by norm_num
  have h12 : |((-1 / 2)) * u ^ 5 * e| ≤ (27027 / 4000000000) := by
    calc
      _ = (1 / 2) * |u| ^ 5 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (1 / 2) * (1 / 100) ^ 5 * 135135 := by gcongr
      _ = _ := by norm_num
  have h13 : |(-1) * u ^ 5 * w * e| ≤ (43540497 / 100000000000000) := by
    calc
      _ = 1 * |u| ^ 5 * |w| * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 5 * (1611 / 50000) * 135135 := by gcongr
      _ = _ := by norm_num
  have h14 : |(-10395) * u ^ 6| ≤ (2079 / 200000000000) := by
    calc
      _ = 10395 * |u| ^ 6 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 6 := by gcongr
      _ = _ := by norm_num
  have h15 : |945 * u ^ 6 * s| ≤ (567 / 200000000000) := by
    calc
      _ = 945 * |u| ^ 6 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 945 * (1 / 100) ^ 6 * 3 := by gcongr
      _ = _ := by norm_num
  have h16 : |(-10395) * u ^ 7 * s| ≤ (6237 / 20000000000000) := by
    calc
      _ = 10395 * |u| ^ 7 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 7 * 3 := by gcongr
      _ = _ := by norm_num
  have h17 : |(-1) * u ^ 7 * e| ≤ (27027 / 20000000000000) := by
    calc
      _ = 1 * |u| ^ 7 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 7 * 135135 := by gcongr
      _ = _ := by norm_num
  have h18 : |(-1) * u ^ 8 * e * s| ≤ (81081 / 2000000000000000) := by
    calc
      _ = 1 * |u| ^ 8 * |e| * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 8 * 135135 * 3 := by gcongr
      _ = _ := by norm_num
  dsimp only [bRemainder]
  calc
    _ ≤ |15 * u * w| + |((-111 / 2)) * u ^ 2| + |1 * u ^ 2 * s| + |(-105) * u ^ 2 * w| + |(975 / 2) * u ^ 3| + |(-3) * u ^ 3 * s| + |945 * u ^ 3 * w| + |((-10605 / 2)) * u ^ 4| + |15 * u ^ 4 * s| + |(-10395) * u ^ 4 * w| + |945 * u ^ 5| + |(-105) * u ^ 5 * s| + |((-1 / 2)) * u ^ 5 * e| + |(-1) * u ^ 5 * w * e| + |(-10395) * u ^ 6| + |945 * u ^ 6 * s| + |(-10395) * u ^ 7 * s| + |(-1) * u ^ 7 * e| + |(-1) * u ^ 8 * e * s| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (le_rfl) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]

noncomputable def jRemainder (u w e h s : ℝ) : ℝ :=
  90 * u * w +
  (-358) * u ^ 2 +
  2 * u ^ 2 * s +
  (-840) * u ^ 2 * w +
  4815 * u ^ 3 +
  (-12) * u ^ 3 * s +
  (-1) * u ^ 3 * h +
  9450 * u ^ 3 * w +
  (8715 / 2) * u ^ 4 +
  90 * u ^ 4 * s +
  (1 / 2) * u ^ 4 * e +
  10395 * u ^ 4 * w +
  1 * u ^ 4 * w * e +
  9450 * u ^ 5 +
  (-840) * u ^ 5 * s +
  (1 / 2) * u ^ 5 * e +
  1 * u ^ 5 * w * e +
  10395 * u ^ 6 +
  9450 * u ^ 6 * s +
  1 * u ^ 6 * e +
  10395 * u ^ 7 * s +
  1 * u ^ 7 * e +
  1 * u ^ 7 * e * s +
  1 * u ^ 8 * e * s

theorem jRemainder_bound {u w e h s : ℝ}
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1611 / 50000)
    (he : |e| ≤ 135135) (hh : |h| ≤ 706) (hs : |s| ≤ 3) :
    |jRemainder u w e h s| ≤ (3 / 40) := by
  have h0 : |90 * u * w| ≤ (14499 / 500000) := by
    calc
      _ = 90 * |u| * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 90 * (1 / 100) * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h1 : |(-358) * u ^ 2| ≤ (179 / 5000) := by
    calc
      _ = 358 * |u| ^ 2 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 358 * (1 / 100) ^ 2 := by gcongr
      _ = _ := by norm_num
  have h2 : |2 * u ^ 2 * s| ≤ (3 / 5000) := by
    calc
      _ = 2 * |u| ^ 2 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 2 * (1 / 100) ^ 2 * 3 := by gcongr
      _ = _ := by norm_num
  have h3 : |(-840) * u ^ 2 * w| ≤ (33831 / 12500000) := by
    calc
      _ = 840 * |u| ^ 2 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 840 * (1 / 100) ^ 2 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h4 : |4815 * u ^ 3| ≤ (963 / 200000) := by
    calc
      _ = 4815 * |u| ^ 3 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 4815 * (1 / 100) ^ 3 := by gcongr
      _ = _ := by norm_num
  have h5 : |(-12) * u ^ 3 * s| ≤ (9 / 250000) := by
    calc
      _ = 12 * |u| ^ 3 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 12 * (1 / 100) ^ 3 * 3 := by gcongr
      _ = _ := by norm_num
  have h6 : |(-1) * u ^ 3 * h| ≤ (353 / 500000) := by
    calc
      _ = 1 * |u| ^ 3 * |h| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 3 * 706 := by gcongr
      _ = _ := by norm_num
  have h7 : |9450 * u ^ 3 * w| ≤ (304479 / 1000000000) := by
    calc
      _ = 9450 * |u| ^ 3 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 9450 * (1 / 100) ^ 3 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h8 : |(8715 / 2) * u ^ 4| ≤ (1743 / 40000000) := by
    calc
      _ = (8715 / 2) * |u| ^ 4 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (8715 / 2) * (1 / 100) ^ 4 := by gcongr
      _ = _ := by norm_num
  have h9 : |90 * u ^ 4 * s| ≤ (27 / 10000000) := by
    calc
      _ = 90 * |u| ^ 4 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 90 * (1 / 100) ^ 4 * 3 := by gcongr
      _ = _ := by norm_num
  have h10 : |(1 / 2) * u ^ 4 * e| ≤ (27027 / 40000000) := by
    calc
      _ = (1 / 2) * |u| ^ 4 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (1 / 2) * (1 / 100) ^ 4 * 135135 := by gcongr
      _ = _ := by norm_num
  have h11 : |10395 * u ^ 4 * w| ≤ (3349269 / 1000000000000) := by
    calc
      _ = 10395 * |u| ^ 4 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 4 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h12 : |1 * u ^ 4 * w * e| ≤ (43540497 / 1000000000000) := by
    calc
      _ = 1 * |u| ^ 4 * |w| * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 4 * (1611 / 50000) * 135135 := by gcongr
      _ = _ := by norm_num
  have h13 : |9450 * u ^ 5| ≤ (189 / 200000000) := by
    calc
      _ = 9450 * |u| ^ 5 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 9450 * (1 / 100) ^ 5 := by gcongr
      _ = _ := by norm_num
  have h14 : |(-840) * u ^ 5 * s| ≤ (63 / 250000000) := by
    calc
      _ = 840 * |u| ^ 5 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 840 * (1 / 100) ^ 5 * 3 := by gcongr
      _ = _ := by norm_num
  have h15 : |(1 / 2) * u ^ 5 * e| ≤ (27027 / 4000000000) := by
    calc
      _ = (1 / 2) * |u| ^ 5 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (1 / 2) * (1 / 100) ^ 5 * 135135 := by gcongr
      _ = _ := by norm_num
  have h16 : |1 * u ^ 5 * w * e| ≤ (43540497 / 100000000000000) := by
    calc
      _ = 1 * |u| ^ 5 * |w| * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 5 * (1611 / 50000) * 135135 := by gcongr
      _ = _ := by norm_num
  have h17 : |10395 * u ^ 6| ≤ (2079 / 200000000000) := by
    calc
      _ = 10395 * |u| ^ 6 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 6 := by gcongr
      _ = _ := by norm_num
  have h18 : |9450 * u ^ 6 * s| ≤ (567 / 20000000000) := by
    calc
      _ = 9450 * |u| ^ 6 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 9450 * (1 / 100) ^ 6 * 3 := by gcongr
      _ = _ := by norm_num
  have h19 : |1 * u ^ 6 * e| ≤ (27027 / 200000000000) := by
    calc
      _ = 1 * |u| ^ 6 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 6 * 135135 := by gcongr
      _ = _ := by norm_num
  have h20 : |10395 * u ^ 7 * s| ≤ (6237 / 20000000000000) := by
    calc
      _ = 10395 * |u| ^ 7 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 10395 * (1 / 100) ^ 7 * 3 := by gcongr
      _ = _ := by norm_num
  have h21 : |1 * u ^ 7 * e| ≤ (27027 / 20000000000000) := by
    calc
      _ = 1 * |u| ^ 7 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 7 * 135135 := by gcongr
      _ = _ := by norm_num
  have h22 : |1 * u ^ 7 * e * s| ≤ (81081 / 20000000000000) := by
    calc
      _ = 1 * |u| ^ 7 * |e| * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 7 * 135135 * 3 := by gcongr
      _ = _ := by norm_num
  have h23 : |1 * u ^ 8 * e * s| ≤ (81081 / 2000000000000000) := by
    calc
      _ = 1 * |u| ^ 8 * |e| * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 8 * 135135 * 3 := by gcongr
      _ = _ := by norm_num
  dsimp only [jRemainder]
  calc
    _ ≤ |90 * u * w| + |(-358) * u ^ 2| + |2 * u ^ 2 * s| + |(-840) * u ^ 2 * w| + |4815 * u ^ 3| + |(-12) * u ^ 3 * s| + |(-1) * u ^ 3 * h| + |9450 * u ^ 3 * w| + |(8715 / 2) * u ^ 4| + |90 * u ^ 4 * s| + |(1 / 2) * u ^ 4 * e| + |10395 * u ^ 4 * w| + |1 * u ^ 4 * w * e| + |9450 * u ^ 5| + |(-840) * u ^ 5 * s| + |(1 / 2) * u ^ 5 * e| + |1 * u ^ 5 * w * e| + |10395 * u ^ 6| + |9450 * u ^ 6 * s| + |1 * u ^ 6 * e| + |10395 * u ^ 7 * s| + |1 * u ^ 7 * e| + |1 * u ^ 7 * e * s| + |1 * u ^ 8 * e * s| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (le_rfl) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]

noncomputable def rRemainder (u w e h s : ℝ) : ℝ :=
  6 * u ^ 2 * s +
  (-7560) * u ^ 2 * w +
  ((-29133 / 2)) * u ^ 3 +
  (-60) * u ^ 3 * s +
  2 * u ^ 3 * h +
  ((-1 / 2)) * u ^ 3 * e +
  (-31185) * u ^ 3 * w +
  (-1) * u ^ 3 * w * e +
  (-9040) * u ^ 4 +
  630 * u ^ 4 * s +
  (-4) * u ^ 4 * h +
  ((-3 / 2)) * u ^ 4 * e +
  (-3) * u ^ 4 * w * e +
  (-25709) * u ^ 5 +
  (-7560) * u ^ 5 * s +
  20 * u ^ 5 * h +
  (-1) * u ^ 5 * e +
  (-31185) * u ^ 6 * s +
  (-148) * u ^ 6 * h +
  (-3) * u ^ 6 * e +
  (-1) * u ^ 6 * e * s +
  1 * u ^ 7 * h ^ 2 +
  (-3) * u ^ 7 * e * s

theorem rRemainder_bound {u w e h s : ℝ}
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1611 / 50000)
    (he : |e| ≤ 135135) (hh : |h| ≤ 706) (hs : |s| ≤ 3) :
    |rRemainder u w e h s| ≤ (3 / 25) := by
  have h0 : |6 * u ^ 2 * s| ≤ (9 / 5000) := by
    calc
      _ = 6 * |u| ^ 2 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 6 * (1 / 100) ^ 2 * 3 := by gcongr
      _ = _ := by norm_num
  have h1 : |(-7560) * u ^ 2 * w| ≤ (304479 / 12500000) := by
    calc
      _ = 7560 * |u| ^ 2 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 7560 * (1 / 100) ^ 2 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h2 : |((-29133 / 2)) * u ^ 3| ≤ (29133 / 2000000) := by
    calc
      _ = (29133 / 2) * |u| ^ 3 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (29133 / 2) * (1 / 100) ^ 3 := by gcongr
      _ = _ := by norm_num
  have h3 : |(-60) * u ^ 3 * s| ≤ (9 / 50000) := by
    calc
      _ = 60 * |u| ^ 3 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 60 * (1 / 100) ^ 3 * 3 := by gcongr
      _ = _ := by norm_num
  have h4 : |2 * u ^ 3 * h| ≤ (353 / 250000) := by
    calc
      _ = 2 * |u| ^ 3 * |h| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 2 * (1 / 100) ^ 3 * 706 := by gcongr
      _ = _ := by norm_num
  have h5 : |((-1 / 2)) * u ^ 3 * e| ≤ (27027 / 400000) := by
    calc
      _ = (1 / 2) * |u| ^ 3 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (1 / 2) * (1 / 100) ^ 3 * 135135 := by gcongr
      _ = _ := by norm_num
  have h6 : |(-31185) * u ^ 3 * w| ≤ (10047807 / 10000000000) := by
    calc
      _ = 31185 * |u| ^ 3 * |w| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 31185 * (1 / 100) ^ 3 * (1611 / 50000) := by gcongr
      _ = _ := by norm_num
  have h7 : |(-1) * u ^ 3 * w * e| ≤ (43540497 / 10000000000) := by
    calc
      _ = 1 * |u| ^ 3 * |w| * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 3 * (1611 / 50000) * 135135 := by gcongr
      _ = _ := by norm_num
  have h8 : |(-9040) * u ^ 4| ≤ (113 / 1250000) := by
    calc
      _ = 9040 * |u| ^ 4 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 9040 * (1 / 100) ^ 4 := by gcongr
      _ = _ := by norm_num
  have h9 : |630 * u ^ 4 * s| ≤ (189 / 10000000) := by
    calc
      _ = 630 * |u| ^ 4 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 630 * (1 / 100) ^ 4 * 3 := by gcongr
      _ = _ := by norm_num
  have h10 : |(-4) * u ^ 4 * h| ≤ (353 / 12500000) := by
    calc
      _ = 4 * |u| ^ 4 * |h| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 4 * (1 / 100) ^ 4 * 706 := by gcongr
      _ = _ := by norm_num
  have h11 : |((-3 / 2)) * u ^ 4 * e| ≤ (81081 / 40000000) := by
    calc
      _ = (3 / 2) * |u| ^ 4 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ (3 / 2) * (1 / 100) ^ 4 * 135135 := by gcongr
      _ = _ := by norm_num
  have h12 : |(-3) * u ^ 4 * w * e| ≤ (130621491 / 1000000000000) := by
    calc
      _ = 3 * |u| ^ 4 * |w| * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 3 * (1 / 100) ^ 4 * (1611 / 50000) * 135135 := by gcongr
      _ = _ := by norm_num
  have h13 : |(-25709) * u ^ 5| ≤ (25709 / 10000000000) := by
    calc
      _ = 25709 * |u| ^ 5 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 25709 * (1 / 100) ^ 5 := by gcongr
      _ = _ := by norm_num
  have h14 : |(-7560) * u ^ 5 * s| ≤ (567 / 250000000) := by
    calc
      _ = 7560 * |u| ^ 5 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 7560 * (1 / 100) ^ 5 * 3 := by gcongr
      _ = _ := by norm_num
  have h15 : |20 * u ^ 5 * h| ≤ (353 / 250000000) := by
    calc
      _ = 20 * |u| ^ 5 * |h| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 20 * (1 / 100) ^ 5 * 706 := by gcongr
      _ = _ := by norm_num
  have h16 : |(-1) * u ^ 5 * e| ≤ (27027 / 2000000000) := by
    calc
      _ = 1 * |u| ^ 5 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 5 * 135135 := by gcongr
      _ = _ := by norm_num
  have h17 : |(-31185) * u ^ 6 * s| ≤ (18711 / 200000000000) := by
    calc
      _ = 31185 * |u| ^ 6 * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 31185 * (1 / 100) ^ 6 * 3 := by gcongr
      _ = _ := by norm_num
  have h18 : |(-148) * u ^ 6 * h| ≤ (13061 / 125000000000) := by
    calc
      _ = 148 * |u| ^ 6 * |h| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 148 * (1 / 100) ^ 6 * 706 := by gcongr
      _ = _ := by norm_num
  have h19 : |(-3) * u ^ 6 * e| ≤ (81081 / 200000000000) := by
    calc
      _ = 3 * |u| ^ 6 * |e| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 3 * (1 / 100) ^ 6 * 135135 := by gcongr
      _ = _ := by norm_num
  have h20 : |(-1) * u ^ 6 * e * s| ≤ (81081 / 200000000000) := by
    calc
      _ = 1 * |u| ^ 6 * |e| * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 6 * 135135 * 3 := by gcongr
      _ = _ := by norm_num
  have h21 : |1 * u ^ 7 * h ^ 2| ≤ (124609 / 25000000000000) := by
    calc
      _ = 1 * |u| ^ 7 * |h| ^ 2 := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 1 * (1 / 100) ^ 7 * 706 ^ 2 := by gcongr
      _ = _ := by norm_num
  have h22 : |(-3) * u ^ 7 * e * s| ≤ (243243 / 20000000000000) := by
    calc
      _ = 3 * |u| ^ 7 * |e| * |s| := by simp only [abs_mul, abs_pow]; norm_num
      _ ≤ 3 * (1 / 100) ^ 7 * 135135 * 3 := by gcongr
      _ = _ := by norm_num
  dsimp only [rRemainder]
  calc
    _ ≤ |6 * u ^ 2 * s| + |(-7560) * u ^ 2 * w| + |((-29133 / 2)) * u ^ 3| + |(-60) * u ^ 3 * s| + |2 * u ^ 3 * h| + |((-1 / 2)) * u ^ 3 * e| + |(-31185) * u ^ 3 * w| + |(-1) * u ^ 3 * w * e| + |(-9040) * u ^ 4| + |630 * u ^ 4 * s| + |(-4) * u ^ 4 * h| + |((-3 / 2)) * u ^ 4 * e| + |(-3) * u ^ 4 * w * e| + |(-25709) * u ^ 5| + |(-7560) * u ^ 5 * s| + |20 * u ^ 5 * h| + |(-1) * u ^ 5 * e| + |(-31185) * u ^ 6 * s| + |(-148) * u ^ 6 * h| + |(-3) * u ^ 6 * e| + |(-1) * u ^ 6 * e * s| + |1 * u ^ 7 * h ^ 2| + |(-3) * u ^ 7 * e * s| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (le_rfl) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]

noncomputable def tailB (u t e h s : ℝ) : ℝ :=
  t - 3 / 2 + (17 / 2 - 3 * t) * u + bRemainder u (u*t) e h s
noncomputable def tailJ (u t e h s : ℝ) : ℝ :=
  2*t - 4 + (37 - 12*t)*u + jRemainder u (u*t) e h s
noncomputable def tailR (u t e h s : ℝ) : ℝ :=
  6*t - 14 + (197 - 60*t)*u + (630*t - 4028 + 2*h)*u^2 + rRemainder u (u*t) e h s

/-- Exact polynomial expansion of the three differentiated tail expressions. -/
theorem tail_polynomial_identities {u : ℝ} (hu : u ≠ 0) (t e h s : ℝ) :
    let F := millsPolynomial u + e*u^7
    let H := hazardPolynomial u + h*u^5
    let T := t + u + s*u^2
    ((1-F)/(2*u) + (1-F)*T = 1/2 + u * tailB u t e h s) ∧
    (1 + F/2 - H - (1-F)/(2*u) + ((1+u)*F-1)*T = u^2 * tailJ u t e h s) ∧
    (-(2*(1/2-u*tailB u t e h s) - (H^2-H)/u + u*tailJ u t e h s) =
      u^2 * tailR u t e h s) := by
  dsimp [millsPolynomial, hazardPolynomial, tailB, tailJ, tailR,
    bRemainder, jRemainder, rRemainder]
  constructor
  · field_simp; ring
  constructor <;> (field_simp; ring)

/-- The uniform enclosures required in the positive-tail argument. -/
theorem tail_BJR_errors {u t e h s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/100) (ht : 3221/1000 ≤ t)
    (hut : |u*t| ≤ 1611/50000)
    (hut1 : u*(t-2721/1000) ≤ 501/100000)
    (hut2 : u^2*(t-2971/1000) ≤ 251/10000000)
    (he : |e| ≤ 135135) (hh0 : 0 ≤ h) (hh1 : h ≤ 706) (hs : |s| ≤ 3) :
    |tailB u t e h s - (t-3/2)| ≤ 1/25 ∧
    |tailJ u t e h s - (2*t-4)| ≤ 7/50 ∧
    |tailR u t e h s - (6*t-14)| ≤ 9/10 := by
  have hu : |u| ≤ 1/100 := by rwa [abs_of_nonneg hu0]
  have hh : |h| ≤ 706 := by rwa [abs_of_nonneg hh0]
  have hbt := bRemainder_bound hu hut he hh hs
  have hjt := jRemainder_bound hu hut he hh hs
  have hrt := rRemainder_bound hu hut he hh hs
  have hl := mul_le_mul_of_nonneg_left ht hu0
  have hb : |(17/2-3*t)*u| ≤ 1503/100000 := by
    rw [abs_le]
    constructor <;> nlinarith only [hl, hut1, hu0]
  have hj : |(37-12*t)*u| ≤ 1503/25000 := by
    rw [abs_le]
    constructor <;> nlinarith only [hl, hut1, hu0]
  have hr : |(197-60*t)*u| ≤ 1503/5000 := by
    rw [abs_le]
    constructor <;> nlinarith only [hl, hut1, hu0, hu1]
  have hg : |(630*t-4028+2*h)*u^2| ≤ 1/5 := by
    have hu2 : u^2 ≤ (1/100 : ℝ)^2 := by nlinarith only [hu0, hu1]
    have htl := mul_le_mul_of_nonneg_left ht (sq_nonneg u)
    have hhlo := mul_nonneg hh0 (sq_nonneg u)
    have hhhi := mul_le_mul_of_nonneg_right hh1 (sq_nonneg u)
    rw [abs_le]
    constructor <;> nlinarith only [hu2, htl, hhlo, hhhi, hut2, sq_nonneg u]
  dsimp only [tailB, tailJ, tailR]
  refine ⟨?_, ?_, ?_⟩
  · have htri := abs_add_le ((17/2-3*t)*u) (bRemainder u (u*t) e h s)
    rw [show t - 3/2 + (17/2-3*t)*u + bRemainder u (u*t) e h s - (t-3/2) =
      (17/2-3*t)*u + bRemainder u (u*t) e h s by ring]
    linarith only [htri, hb, hbt]
  · have htri := abs_add_le ((37-12*t)*u) (jRemainder u (u*t) e h s)
    rw [show 2*t - 4 + (37-12*t)*u + jRemainder u (u*t) e h s - (2*t-4) =
      (37-12*t)*u + jRemainder u (u*t) e h s by ring]
    linarith only [htri, hj, hjt]
  · have htri := (abs_add_le ((197-60*t)*u + (630*t-4028+2*h)*u^2)
      (rRemainder u (u*t) e h s)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    rw [show 6*t - 14 + (197-60*t)*u + (630*t-4028+2*h)*u^2 +
        rRemainder u (u*t) e h s - (6*t-14) =
      ((197-60*t)*u + (630*t-4028+2*h)*u^2) + rRemainder u (u*t) e h s by ring]
    linarith only [htri, hr, hg, hrt]

end Submission.Obl.Entropy__two_eigenvalue_positive_certificate
