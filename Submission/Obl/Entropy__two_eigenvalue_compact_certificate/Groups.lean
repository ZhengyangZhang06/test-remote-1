import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Data

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

structure Bin where
  bmin : ℚ
  bmax : ℚ
  lmax : ℚ
  dmax : ℚ
  kmin : ℚ
  kmax : ℚ
  jmax : ℚ
  surplus : ℚ
  m0 : ℚ
  zmin : ℚ
  zmax : ℚ
  chimax : ℚ
  negative : Bool

def binO : Bin := ⟨0,9/100,3/5,0,37/100,14/25,18/25,13/100,0,-2/25,7/10,7/100,true⟩
def binN : Bin := ⟨83/1000,3/20,101/100,43/10,29/100,23/50,18/25,13/100,19/100,-2/25,7/10,7/100,false⟩
def binM : Bin := ⟨7/50,23/100,119/100,3,29/100,371/1000,17/25,13/100,38/100,-2/25,7/10,7/100,false⟩
def binC : Bin := ⟨11/50,171/500,119/100,43/25,29/100,199/500,61/100,123/1000,68/100,-19/40,0,97/1000,false⟩
def binP : Bin := ⟨337/1000,9/20,83/100,87/100,31/100,2/5,1/2,3/50,68/100,-19/40,0,97/1000,false⟩
def binT : Bin := ⟨89/200,1/2,1/5,16/25,8/25,2/5,12/25,11/500,68/100,-19/40,0,97/1000,false⟩

local instance : Add CExpr := ⟨CExpr.add⟩
local instance : Sub CExpr := ⟨CExpr.sub⟩
local instance : Mul CExpr := ⟨CExpr.mul⟩
local instance (n : Nat) : OfNat CExpr n := ⟨CExpr.const n⟩

theorem CExpr.value_add (v : Nat → ℝ) (A B : CExpr) :
    (A+B).value v = A.value v+B.value v := rfl

theorem CExpr.value_sub (v : Nat → ℝ) (A B : CExpr) :
    (A-B).value v = A.value v-B.value v := rfl

theorem CExpr.value_mul (v : Nat → ℝ) (A B : CExpr) :
    (A*B).value v = A.value v*B.value v := rfl

theorem CExpr.value_nat (v : Nat → ℝ) (n : Nat) :
    (OfNat.ofNat n : CExpr).value v = (n : ℝ) := by
  change ((n : ℚ) : ℝ) = (n : ℝ)
  simp

/-- Every inequality is expressed without division by a function value. -/
def groups (R : Bin) : List CExpr :=
  let a := CExpr.var 0
  let q := CExpr.var 1
  let k := CExpr.var 2
  let d := CExpr.var 3
  let b := CExpr.var 4
  let l := CExpr.var 5
  let y := CExpr.var 6
  let p := b+k*l-(l*l).scale (40/3)
  let E := p+b*(CExpr.const (3/4)-b)-(l*l).scale (40/3)
  let H := l+(b*l).scale 3+k*y
  let f := b.scale (3/2)
  let eta : ℚ := (40/37)*(7/25)+(42/37)*(3/4)
  let nu : ℚ := (40/37)*(7/25)^2+(45/37)*(3/4)^2
  let h := CExpr.const (43/100-R.surplus)-(b*b).scale (82/37)+b.scale eta-
    CExpr.const (nu/4)-(l*l).scale (40/3)
  let v := CExpr.const (197/100-nu)
  let o := CExpr.const (13/100-nu/2)+b.scale eta
  [b-CExpr.const R.bmin, CExpr.const R.bmax-b, l,
   CExpr.const ((3/40)*R.lmax)-l, p,
   if R.negative then p*(7+a*a)-1 else p-CExpr.const ((5/17)/R.dmax),
   E.scale (5/17)-p.scale R.kmin, p.scale R.kmax-E.scale (5/17),
   p.scale R.jmax-f.scale (5/17),
   y-l.scale R.zmin, l.scale R.zmax-y,
   H-l.scale (4/5), l.scale (177/100)-H, d.scale R.chimax-l,
   ((1-q*d)*(1-b*b)).scale 2-((b*l)*d).scale 2-((d*d)*(1-b*b)).scale R.m0,
   h*p-(E*E).scale (5/17),
   p*(h*v-o*o)-(E*E*v-(E.scale 2)*o*f+h*f*f).scale (5/17)]

def Model.Check (M : Model) (R : Bin) : Prop :=
  ∀ A ∈ groups R, (A.enclose M.initial).LowerBound (1/10^6)

scoped instance (M : Model) (R : Bin) : Decidable (M.Check R) :=
  inferInstanceAs (Decidable (∀ A ∈ groups R, (A.enclose M.initial).LowerBound (1/10^6)))

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
