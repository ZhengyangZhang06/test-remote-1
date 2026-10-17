import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Positivity

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

/-- The rational arithmetic expressions in the four certificate groups. -/
inductive CExpr where
  | var : Nat → CExpr
  | const : ℚ → CExpr
  | add : CExpr → CExpr → CExpr
  | sub : CExpr → CExpr → CExpr
  | mul : CExpr → CExpr → CExpr
  | scale : ℚ → CExpr → CExpr

def CExpr.value (v : Nat → ℝ) : CExpr → ℝ
  | .var i => v i
  | .const c => c
  | .add A B => A.value v + B.value v
  | .sub A B => A.value v - B.value v
  | .mul A B => A.value v * B.value v
  | .scale c A => (c : ℝ) * A.value v

def CExpr.enclose (v : Nat → Enclosure) : CExpr → Enclosure
  | .var i => v i
  | .const c => .const c
  | .add A B => (A.enclose v).add (B.enclose v)
  | .sub A B => (A.enclose v).sub (B.enclose v)
  | .mul A B => (A.enclose v).mul (B.enclose v)
  | .scale c A => (A.enclose v).scale c

theorem CExpr.holds (A : CExpr) {v : Nat → ℝ} {V : Nat → Enclosure} {x : ℝ}
    (hV : ∀ i, (V i).Holds x (v i)) (hx : |x| ≤ 1) :
    (A.enclose V).Holds x (A.value v) := by
  induction A with
  | var i => exact hV i
  | const c => exact Enclosure.holds_const c x
  | add A B ihA ihB => exact ihA.add ihB
  | sub A B ihA ihB => exact ihA.sub ihB
  | mul A B ihA ihB => exact ihA.mul ihB hx
  | scale c A ihA => exact ihA.scale c

theorem CExpr.nonneg_of_check (A : CExpr) {v : Nat → ℝ} {V : Nat → Enclosure} {x : ℝ}
    (hV : ∀ i, (V i).Holds x (v i)) (hx : |x| ≤ 1)
    (h : (A.enclose V).LowerBound 0) : 0 ≤ A.value v := by
  exact_mod_cast h.le (A.holds hV hx) hx

/-- A row of the piecewise polynomial model; the coefficients are rational input data. -/
structure Model where
  center : ℚ
  radius : ℚ
  hazard : List ℚ
  ratio : List ℚ

def Model.coordinate (M : Model) : List ℚ := [M.center, M.radius]

def Model.initial (M : Model) : Nat → Enclosure :=
  let A : Enclosure := ⟨M.coordinate, 0⟩
  let Q : Enclosure := ⟨M.hazard, 1/10^8⟩
  let K : Enclosure := ⟨M.ratio, 8/10^7⟩
  let D := Q.sub A
  let B := (Enclosure.const 1).sub (K.mulFull D)
  let J := (K.sub Q).add (A.mulFull B)
  let Y := ((B.scale 2).sub (Q.mulFull D)).add (A.mulFull J)
  fun i => (match i with
    | 0 => A
    | 1 => Q
    | 2 => K
    | 3 => D
    | 4 => B
    | 5 => J
    | 6 => Y
    | _ => Enclosure.const 0).trunc

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
