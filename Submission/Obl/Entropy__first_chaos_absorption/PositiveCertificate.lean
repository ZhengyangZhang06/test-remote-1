import Submission.Obl.Entropy__first_chaos_absorption.TailRatio
import Submission.Obl.Entropy__first_chaos_absorption.PositiveFunctions
import Submission.Obl.Entropy__first_chaos_absorption.PositiveLog
import Submission.Obl.Entropy__first_chaos_absorption.PositiveTail
import Submission.Obl.Entropy__first_chaos_absorption.Functions

open MeasureTheory ProbabilityTheory

namespace Submission.Obl.Entropy__first_chaos_absorption

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Submission.Lib.GaussianTransport

/-- Coarse, uniform derivative bounds on the positive tail, proved directly
from Mills inequalities and the elementary logarithmic estimate. -/
lemma positive_tail_derivative_bounds {r : ℝ} (hr : 10 ≤ r) :
    0 ≤ transportRatio r ∧ 47/100 ≤ transportSlope r ∧
    0 ≤ transportCurvature r ∧ transportCurvature r ≤ 1/50 ∧
    transportRatio r*(1/2-transportSlope r) ≤ 1/5 := by
  let u := (r⁻¹)^2
  let J := r*(normalCDF (-r)/normalPDF r)
  let T := Real.log (r*Real.sqrt (2*Real.pi))-Real.log J
  have hr0 : 0 < r := by linarith
  have hu : 0 < u := sq_pos_of_pos (inv_pos.mpr hr0)
  have hinv : r⁻¹ ≤ (1/10 : ℝ) := (inv_le_comm₀ hr0 (by norm_num)).mpr (by simpa using hr)
  have hu' : u ≤ 1/100 := by dsimp [u]; nlinarith [inv_pos.mpr hr0]
  have hu2 : u^2 ≤ 1/10000 := by nlinarith [sq_nonneg (u-1/100)]
  have hJpos : 0 < J := mul_pos hr0 (div_pos (normalCDF_pos _) (normalPDF_pos _))
  have hJ1 : 1-u ≤ J := by
    convert! mul_le_mul_of_nonneg_left (mills_lower_one hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp
  have hJ2 : J ≤ 1-u+3*u^2 := by
    convert! mul_le_mul_of_nonneg_left (mills_upper_two hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp
  have hJ3 : 1-u+3*u^2-15*u^3 ≤ J := by
    convert! mul_le_mul_of_nonneg_left (mills_lower_three hr0) hr0.le using 1
    simp only [u, inv_pow]
    field_simp
  have hJ0 : J ≤ 1 := by
    simpa [J, hr0.ne'] using mul_le_mul_of_nonneg_left (mills_upper_zero hr0) hr0.le
  obtain ⟨hTlo, hTr, huT⟩ := positive_tail_log_bounds hr hJ1 hJ0
  change 3 ≤ T at hTlo
  change T/r ≤ 9/25 at hTr
  change u*(T-3/2) ≤ 1/40 at huT
  have hT0 : 0 ≤ T := by linarith
  have huTcap : u*T ≤ 1/25 := by nlinarith only [huT, hu']
  obtain ⟨hq, hk, hb, hl⟩ := positive_tail_forms hr0
  change transportRatio r = r*J*(1/2+u*T) at hk
  change transportSlope r = 1-(1/(2*u)+T)*(1-J) at hb
  change transportCurvature r = r*millsCurvature u T J at hl
  have hk0 : 0 ≤ transportRatio r := by rw [hk]; positivity
  have hX : 0 ≤ (1/2 : ℝ)+u*T := by positivity
  have hkcap : transportRatio r ≤ (27/50)*r := by
    rw [hk]
    calc
      _ ≤ r*1*(1/2+u*T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ0 hr0.le) hX
      _ ≤ (27/50)*r := by nlinarith [mul_le_mul_of_nonneg_left huTcap hr0.le]
  let C := 1/(2*u)+T
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb0 : 47/100 ≤ transportSlope r := by
    have hprod := mul_le_mul_of_nonneg_left (show 1-J ≤ u-3*u^2+15*u^3 by linarith) hC
    have hid : 1-C*(u-3*u^2+15*u^3) =
        1/2-u*(T-3/2)-(15/2)*u^2+T*u^2*(3-15*u) := by
      dsimp [C]
      field_simp [hu.ne']
      ring
    have hpos : 0 ≤ T*u^2*(3-15*u) :=
      mul_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by linarith)
    have hbase : 47/100 ≤ 1-C*(u-3*u^2+15*u^3) := by
      rw [hid]
      nlinarith only [huT, hu2, hpos]
    change transportSlope r = 1-C*(1-J) at hb
    linarith only [hb, hbase, hprod]
  have hbshort : 1/2-transportSlope r ≤ u*T := by
    have hprod := mul_le_mul_of_nonneg_left (show 1-J ≤ u by linarith) hC
    rw [hb]
    calc
      _ ≤ 1/2-(1-C*u) := by dsimp [C] at hprod ⊢; linarith only [hprod]
      _ = u*T := by dsimp [C]; field_simp [hu.ne']; ring
  obtain ⟨hg0, hg1⟩ := millsCurvature_bounds hu hu' hTlo hJ3 hJ2
  have hl0 : 0 ≤ transportCurvature r := by rw [hl]; exact mul_nonneg hr0.le hg0
  have hl1 : transportCurvature r ≤ 1/50 := by
    calc
      _ ≤ r*((4+3*T)*u^2) := by rw [hl]; exact mul_le_mul_of_nonneg_left hg1 hr0.le
      _ = 4*(r⁻¹)^3+3*(T/r)*u := by dsimp [u]; field_simp [hr0.ne']
      _ ≤ 4*(1/10 : ℝ)^3+3*(9/25)*(1/100) := by gcongr
      _ ≤ 1/50 := by norm_num
  have hkb : transportRatio r*(1/2-transportSlope r) ≤ 1/5 := by
    have hbhalf := (transportSlope_lt_half r).le
    calc
      _ ≤ ((27/50)*r)*(u*T) := mul_le_mul hkcap hbshort
        (sub_nonneg.mpr hbhalf) (by positivity)
      _ = (27/50)*(T/r) := by dsimp [u]; field_simp [hr0.ne']
      _ ≤ (27/50)*(9/25) := mul_le_mul_of_nonneg_left hTr (by norm_num)
      _ ≤ 1/5 := by norm_num
  exact ⟨hk0, hb0, hl0, hl1, hkb⟩

/-- Both scalar certificates of Proposition 3.5 on the entire positive tail. -/
theorem positive_tail_certificates {a : ℝ} (ha : 10 ≤ a) :
    23/50 ≤ pValue a ∧ hValue a^2 ≤ (67/100)^2*pValue a := by
  obtain ⟨hk, hb, hl, hl', hkb⟩ := positive_tail_derivative_bounds ha
  exact positive_tail_algebra hk hb (transportSlope_lt_half a).le hl hl' hkb

end Submission.Obl.Entropy__first_chaos_absorption
