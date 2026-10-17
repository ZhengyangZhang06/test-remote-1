import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Groups
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.ActualEnclosures
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Matrix

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate
open Submission.Lib.GaussianTransport

noncomputable def eta : ℝ := (40/37)*(7/25)+(42/37)*(3/4)
noncomputable def nu : ℝ := (40/37)*(7/25)^2+(45/37)*(3/4)^2

noncomputable def certificate (R : Bin) (a : ℝ) : Prop :=
  0 < p a ∧ 0 < b a ∧ b a < 1/2 ∧ 0 < l a ∧
  ((R.bmin : ℝ) ≤ b a ∧ b a ≤ R.bmax ∧ L a ≤ R.lmax ∧
    D a ≤ (if R.negative then (59/200)*(7+a^2) else (R.dmax : ℝ)) ∧
    (R.kmin : ℝ) ≤ D a*E a ∧ D a*E a ≤ R.kmax ∧ D a*(3/2)*b a ≤ R.jmax) ∧
  (∀ u v : ℝ, ((82/37)*(b a)^2-eta*b a+nu/4+(40/3)*(l a)^2)*u^2+
    2*(nu/2-eta*b a)*u*v+nu*v^2+D a*(E a*u+(3/2)*b a*v)^2+
    (R.surplus : ℝ)*u^2+(3/4)*v^2 ≤ (43/100)*u^2+(26/100)*u*v+(68/25)*v^2) ∧
  ((R.zmin : ℝ) ≤ deriv l a/l a ∧ deriv l a/l a ≤ R.zmax ∧ l a/(q a-a) ≤ R.chimax) ∧
  4/5 ≤ 1+3*b a+k a*(deriv l a/l a) ∧ 1+3*b a+k a*(deriv l a/l a) ≤ 177/100

theorem certificate_of_groups (R : Bin) (a : ℝ)
    (hDmax : 0 < R.dmax ∨ R.negative = true)
    (hh : ∀ A ∈ groups R, 0 < A.value (actualValues a)) : certificate R a := by
  simp only [groups, List.forall_mem_cons, List.forall_mem_nil] at hh
  simp only [CExpr.value_add, CExpr.value_sub, CExpr.value_mul, CExpr.value_nat,
    CExpr.value, actualValues, apply_ite] at hh
  push_cast at hh
  simp only [← pow_two, ← p_formula, ← E_formula] at hh
  rcases hh with ⟨hbl,hbu,hl,hL,hp,hD,hKl,hKu,hJ,hzl,hzu,hHl,hHu,hchi,hslope,hlead,hdet,_⟩
  have hbpos : 0 < b a := by rw [b_eq]; exact transportSlope_pos a
  have hbhalf : b a < 1/2 := by rw [b_eq]; exact transportSlope_lt_half a
  have hdpos : 0 < q a-a := gaussianGap_pos a
  refine ⟨hp,hbpos,hbhalf,hl,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,⟨?_,?_,?_⟩,?_,?_⟩
  · linarith only [hbl]
  · linarith only [hbu]
  · unfold L
    linarith only [hL]
  · unfold D
    split_ifs with hneg
    · simp [hneg] at hD
      apply (div_le_iff₀ hp).mpr
      nlinarith only [hD]
    · simp [hneg] at hD
      have hr : (0 : ℝ) < R.dmax := by
        rcases hDmax with hr | hr
        · exact_mod_cast hr
        · exact False.elim (hneg hr)
      apply (div_le_iff₀ hp).mpr
      have hh := (div_lt_iff₀ hr).mp (show (5/17 : ℝ)/R.dmax < p a by linarith only [hD])
      nlinarith only [hh]
  · unfold D
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    linarith only [hKl]
  · unfold D
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    linarith only [hKu]
  · unfold D
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hp]
    linarith only [hJ]
  · intro u v
    have hm := rank_one_bound (p a)
      (43/100-R.surplus-(82/37)*(b a)^2+eta*b a-nu/4-(40/3)*(l a)^2)
      (197/100-nu) (13/100-nu/2+eta*b a) (E a) ((3/2)*b a) (5/17) hp
      (by simpa [eta, nu] using hlead) (by simpa [eta, nu] using hdet.le) u v
    unfold D
    nlinarith only [hm]
  · exact (le_div_iff₀ hl).mpr (by linarith only [hzl])
  · exact (div_le_iff₀ hl).mpr (by linarith only [hzu])
  · exact (div_le_iff₀ hdpos).mpr (by linarith only [hchi])
  · have hr : (4/5 : ℝ) ≤ (l a+3*b a*l a+k a*deriv l a)/l a :=
      (le_div_iff₀ hl).mpr (by linarith only [hHl])
    convert! hr using 1
    field_simp [hl.ne']
    <;> ring
  · have hr : (l a+3*b a*l a+k a*deriv l a)/l a ≤ (177/100 : ℝ) :=
      (div_le_iff₀ hl).mpr (by linarith only [hHu])
    convert! hr using 1
    field_simp [hl.ne']
    <;> ring

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
