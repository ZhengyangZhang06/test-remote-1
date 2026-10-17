import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Polynomial

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- Bernstein coefficients of a quartic on the two half intervals. -/
def bernCoeffs (p : List ℚ) : List ℚ :=
  let a := p[0]?.getD 0
  let b := p[1]?.getD 0
  let c := p[2]?.getD 0
  let d := p[3]?.getD 0
  let e := p[4]?.getD 0
  [a, a + b/4, a + b/2 + c/6, a + 3*b/4 + c/2 + d/4, a+b+c+d+e,
      a - b/4, a - b/2 + c/6, a - 3*b/4 + c/2 - d/4, a-b+c-d+e]

def Enclosure.LowerBound (A : Enclosure) (r : ℚ) : Prop :=
  A.poly.length ≤ 5 ∧ ∀ c ∈ bernCoeffs A.poly, r + A.error ≤ c

instance (A : Enclosure) (r : ℚ) : Decidable (A.LowerBound r) :=
  inferInstanceAs (Decidable (A.poly.length ≤ 5 ∧ ∀ c ∈ bernCoeffs A.poly, r + A.error ≤ c))

private theorem quartic_bound (a b c d e m t : ℝ)
    (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h0 : m ≤ a) (h1 : m ≤ a+b/4) (h2 : m ≤ a+b/2+c/6)
    (h3 : m ≤ a+3*b/4+c/2+d/4) (h4 : m ≤ a+b+c+d+e) :
    m ≤ a + t*(b+t*(c+t*(d+t*e))) := by
  have h : 0 ≤ (a-m)*(1-t)^4 + 4*(a+b/4-m)*t*(1-t)^3 +
      6*(a+b/2+c/6-m)*t^2*(1-t)^2 +
      4*(a+3*b/4+c/2+d/4-m)*t^3*(1-t) + (a+b+c+d+e-m)*t^4 := by
    have : 0 ≤ 1-t := sub_nonneg.mpr ht'
    have h0' := sub_nonneg.mpr h0
    have h1' := sub_nonneg.mpr h1
    have h2' := sub_nonneg.mpr h2
    have h3' := sub_nonneg.mpr h3
    have h4' := sub_nonneg.mpr h4
    positivity
  nlinarith only [h]

private theorem quartic_bound_abs (a b c d e m x : ℝ) (hx : |x| ≤ 1)
    (h0 : m ≤ a) (h1 : m ≤ a+b/4) (h2 : m ≤ a+b/2+c/6)
    (h3 : m ≤ a+3*b/4+c/2+d/4) (h4 : m ≤ a+b+c+d+e)
    (hn1 : m ≤ a-b/4) (hn2 : m ≤ a-b/2+c/6)
    (hn3 : m ≤ a-3*b/4+c/2-d/4) (hn4 : m ≤ a-b+c-d+e) :
    m ≤ a + x*(b+x*(c+x*(d+x*e))) := by
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  rcases le_total 0 x with hx0 | hx0
  · exact quartic_bound a b c d e m x hx0 hxu h0 h1 h2 h3 h4
  · have hh := quartic_bound a (-b) c (-d) e m (-x) (by linarith) (by linarith)
        h0 (by linarith) (by linarith) (by linarith) (by linarith)
    convert hh using 1 <;> ring

private theorem peval_quartic (p : List ℚ) (x : ℝ) (h : p.length ≤ 5) :
    peval p x = ((p[0]?.getD 0 : ℚ) : ℝ) + x * (((p[1]?.getD 0 : ℚ) : ℝ) +
      x * (((p[2]?.getD 0 : ℚ) : ℝ) + x * (((p[3]?.getD 0 : ℚ) : ℝ) +
        x * ((p[4]?.getD 0 : ℚ) : ℝ)))) := by
  rcases p with _ | ⟨a,p⟩ <;> simp_all [peval]
  rcases p with _ | ⟨b,p⟩ <;> simp_all [peval]
  rcases p with _ | ⟨c,p⟩ <;> simp_all [peval]
  rcases p with _ | ⟨d,p⟩ <;> simp_all [peval]
  rcases p with _ | ⟨e,p⟩ <;> simp_all [peval]
  have hp : p = [] := by simpa using (show p.length = 0 by omega)
  simp [hp, peval]

 theorem Enclosure.LowerBound.le {A : Enclosure} {r : ℚ} (hr : A.LowerBound r)
    {x v : ℝ} (hv : A.Holds x v) (hx : |x| ≤ 1) : (r : ℝ) ≤ v := by
  obtain ⟨hlen, hb⟩ := hr
  simp [bernCoeffs] at hb
  have hp : (r : ℝ) + (A.error : ℝ) ≤ peval A.poly x := by
    rw [peval_quartic A.poly x hlen]
    apply quartic_bound_abs _ _ _ _ _ _ _ hx
    all_goals first | exact_mod_cast hb.1 | exact_mod_cast hb.2.1 |
      exact_mod_cast hb.2.2.1 | exact_mod_cast hb.2.2.2.1 |
      exact_mod_cast hb.2.2.2.2.1 | exact_mod_cast hb.2.2.2.2.2.1 |
      exact_mod_cast hb.2.2.2.2.2.2.1 | exact_mod_cast hb.2.2.2.2.2.2.2.1 |
      exact_mod_cast hb.2.2.2.2.2.2.2.2
  have hv' := (abs_le.mp hv).1
  linarith

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
