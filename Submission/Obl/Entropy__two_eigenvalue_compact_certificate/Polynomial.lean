import Mathlib

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- Coefficients in increasing order, evaluated by Horner's rule. -/
def peval (p : List ℚ) (x : ℝ) : ℝ :=
  match p with
  | [] => 0
  | c :: p => (c : ℝ) + x * peval p x

/-- The coefficient one-norm. -/
def pnorm (p : List ℚ) : ℚ := (p.map abs).sum

def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

def pscale (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

def pmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => padd (pscale a q) (0 :: pmul p q)

theorem peval_add (p q : List ℚ) (x : ℝ) :
    peval (padd p q) x = peval p x + peval q x := by
  induction p generalizing q with
  | nil => simp [padd, peval]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, peval]
    | cons b q => simp only [padd, peval, Rat.cast_add, ih]; ring

theorem peval_scale (c : ℚ) (p : List ℚ) (x : ℝ) :
    peval (pscale c p) x = (c : ℝ) * peval p x := by
  induction p with
  | nil => simp [pscale, peval]
  | cons a p ih => simp only [pscale, List.map_cons, peval, Rat.cast_mul] at *; rw [ih]; ring

theorem peval_mul (p q : List ℚ) (x : ℝ) :
    peval (pmul p q) x = peval p x * peval q x := by
  induction p with
  | nil => simp [pmul, peval]
  | cons a p ih => rw [pmul, peval_add, peval_scale, peval, peval, ih]; ring

theorem pnorm_nonneg (p : List ℚ) : 0 ≤ pnorm p := by
  exact List.sum_nonneg (fun a ha => by obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; positivity)

theorem abs_peval_le (p : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |peval p x| ≤ (pnorm p : ℝ) := by
  induction p with
  | nil => simp [peval, pnorm]
  | cons a p ih =>
    have hnorm : (pnorm (a :: p) : ℝ) = |(a : ℝ)| + (pnorm p : ℝ) := by
      simp [pnorm]
    rw [hnorm, peval]
    calc
      |(a : ℝ) + x * peval p x| ≤ |(a : ℝ)| + |x * peval p x| := abs_add_le _ _
      _ ≤ |(a : ℝ)| + (pnorm p : ℝ) := by
        rw [abs_mul]
        gcongr
        calc
          |x| * |peval p x| ≤ 1 * |peval p x| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
          _ ≤ (pnorm p : ℝ) := by simpa using ih

theorem peval_append (p q : List ℚ) (x : ℝ) :
    peval (p ++ q) x = peval p x + x ^ p.length * peval q x := by
  induction p with
  | nil => simp [peval]
  | cons a p ih => simp only [List.cons_append, peval, List.length_cons, ih, pow_succ]; ring

theorem abs_peval_sub_take_le (n : ℕ) (p : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |peval p x - peval (p.take n) x| ≤ (pnorm (p.drop n) : ℝ) := by
  have he := peval_append (p.take n) (p.drop n) x
  rw [List.take_append_drop] at he
  rw [he, add_sub_cancel_left, abs_mul]
  calc
    |x ^ (p.take n).length| * |peval (p.drop n) x| ≤ 1 * |peval (p.drop n) x| := by
      gcongr
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hx
    _ ≤ (pnorm (p.drop n) : ℝ) := by simpa using abs_peval_le (p.drop n) hx

/-- Formal differentiation in coefficient-list form. -/
def pdiff : List ℚ → List ℚ
  | [] => []
  | _ :: p => padd p (0 :: pdiff p)

theorem hasDerivAt_peval (p : List ℚ) (x : ℝ) :
    HasDerivAt (peval p) (peval (pdiff p) x) x := by
  induction p with
  | nil => simpa only [peval, pdiff] using hasDerivAt_const x (0 : ℝ)
  | cons c p ih =>
    simpa only [pdiff, peval_add, peval, Rat.cast_zero, zero_add, one_mul, id_eq, Pi.mul_apply]
      using ((hasDerivAt_id x).mul ih).const_add (c : ℝ)

/-- A rational polynomial and a uniform absolute error. -/
structure Enclosure where
  poly : List ℚ
  error : ℚ

def Enclosure.Holds (A : Enclosure) (x v : ℝ) : Prop :=
  |v - peval A.poly x| ≤ (A.error : ℝ)

def Enclosure.trunc (A : Enclosure) : Enclosure :=
  ⟨A.poly.take 5, A.error + pnorm (A.poly.drop 5)⟩

def Enclosure.const (c : ℚ) : Enclosure := ⟨[c], 0⟩

def Enclosure.add (A B : Enclosure) : Enclosure :=
  ⟨padd A.poly B.poly, A.error + B.error⟩

def Enclosure.scale (c : ℚ) (A : Enclosure) : Enclosure :=
  ⟨pscale c A.poly, |c| * A.error⟩

def Enclosure.sub (A B : Enclosure) : Enclosure := A.add (B.scale (-1))

def Enclosure.mulFull (A B : Enclosure) : Enclosure :=
  ⟨pmul A.poly B.poly,
    pnorm A.poly * B.error + pnorm B.poly * A.error + A.error * B.error⟩

def Enclosure.mul (A B : Enclosure) : Enclosure := (A.mulFull B).trunc

theorem Enclosure.holds_const (c : ℚ) (x : ℝ) : (const c).Holds x c := by
  simp [Holds, const, peval]

theorem Enclosure.Holds.trunc {A : Enclosure} {x v : ℝ} (h : A.Holds x v)
    (hx : |x| ≤ 1) : A.trunc.Holds x v := by
  dsimp [Holds, Enclosure.trunc] at *
  push_cast
  calc
    |v - peval (A.poly.take 5) x| ≤ |v - peval A.poly x| +
        |peval A.poly x - peval (A.poly.take 5) x| := abs_sub_le _ _ _
    _ ≤ (A.error : ℝ) + (pnorm (A.poly.drop 5) : ℝ) :=
      add_le_add h (abs_peval_sub_take_le 5 A.poly hx)

theorem Enclosure.Holds.add {A B : Enclosure} {x u v : ℝ}
    (hu : A.Holds x u) (hv : B.Holds x v) : (A.add B).Holds x (u + v) := by
  dsimp [Holds, Enclosure.add] at *
  rw [peval_add, Rat.cast_add]
  calc
    |u + v - (peval A.poly x + peval B.poly x)| =
      |(u - peval A.poly x) + (v - peval B.poly x)| := by congr 1; ring
    _ ≤ |u - peval A.poly x| + |v - peval B.poly x| := abs_add_le _ _
    _ ≤ (A.error : ℝ) + (B.error : ℝ) := add_le_add hu hv

theorem Enclosure.Holds.scale {A : Enclosure} {x u : ℝ} (hu : A.Holds x u)
    (c : ℚ) : (A.scale c).Holds x ((c : ℝ) * u) := by
  dsimp [Holds, Enclosure.scale] at *
  rw [peval_scale, ← mul_sub, abs_mul, Rat.cast_mul, Rat.cast_abs]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)

theorem Enclosure.Holds.sub {A B : Enclosure} {x u v : ℝ}
    (hu : A.Holds x u) (hv : B.Holds x v) : (A.sub B).Holds x (u - v) := by
  simpa [Enclosure.sub, sub_eq_add_neg] using hu.add (hv.scale (-1))

theorem Enclosure.Holds.mulFull {A B : Enclosure} {x u v : ℝ}
    (hu : A.Holds x u) (hv : B.Holds x v) (hx : |x| ≤ 1) :
    (A.mulFull B).Holds x (u * v) := by
  dsimp only [Holds, Enclosure.mulFull] at *
  rw [peval_mul]
  push_cast
  have hau := abs_nonneg (u - peval A.poly x)
  have hav := abs_nonneg (v - peval B.poly x)
  have hae : 0 ≤ (A.error : ℝ) := hau.trans hu
  have hbe : 0 ≤ (B.error : ℝ) := hav.trans hv
  calc
    |u * v - peval A.poly x * peval B.poly x| =
        |peval A.poly x * (v - peval B.poly x) +
          peval B.poly x * (u - peval A.poly x) +
          (u - peval A.poly x) * (v - peval B.poly x)| := by congr 1; ring
    _ ≤ |peval A.poly x * (v - peval B.poly x)| +
          |peval B.poly x * (u - peval A.poly x)| +
          |(u - peval A.poly x) * (v - peval B.poly x)| := abs_add_three _ _ _
    _ ≤ (pnorm A.poly : ℝ) * (B.error : ℝ) +
          (pnorm B.poly : ℝ) * (A.error : ℝ) + (A.error : ℝ) * (B.error : ℝ) := by
      simp only [abs_mul]
      have ha := abs_peval_le A.poly hx
      have hb := abs_peval_le B.poly hx
      have hna : 0 ≤ (pnorm A.poly : ℝ) := (abs_nonneg _).trans ha
      have hnb : 0 ≤ (pnorm B.poly : ℝ) := (abs_nonneg _).trans hb
      gcongr

theorem Enclosure.Holds.mul {A B : Enclosure} {x u v : ℝ}
    (hu : A.Holds x u) (hv : B.Holds x v) (hx : |x| ≤ 1) :
    (A.mul B).Holds x (u * v) := (hu.mulFull hv hx).trunc hx

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
