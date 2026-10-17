import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Propagation
import Submission.Obl.Entropy__two_eigenvalue_compact_certificate.Functions

namespace Submission.Obl.Entropy__two_eigenvalue_compact_certificate

theorem Model.initial_holds (M : Model) {x : ℝ} (hx : |x| ≤ 1)
    (hq : |q (M.parameter x)-peval M.hazard x| ≤ 1/10^8)
    (hk : |k (M.parameter x)-peval M.ratio x| ≤ 8/10^7) :
    ∀ i, (M.initial i).Holds x (actualValues (M.parameter x) i) := by
  let a := M.parameter x
  let A : Enclosure := ⟨M.coordinate, 0⟩
  let Q : Enclosure := ⟨M.hazard, 1/10^8⟩
  let K : Enclosure := ⟨M.ratio, 8/10^7⟩
  let DD := Q.sub A
  let BB := (Enclosure.const 1).sub (K.mulFull DD)
  let JJ := (K.sub Q).add (A.mulFull BB)
  let YY := ((BB.scale 2).sub (Q.mulFull DD)).add (A.mulFull JJ)
  have ha : A.Holds x a := by simp [A, a, Enclosure.Holds, M.eval_coordinate]
  have hq' : Q.Holds x (q a) := by simpa [Q, a, Enclosure.Holds] using hq
  have hk' : K.Holds x (k a) := by simpa [K, a, Enclosure.Holds] using hk
  have hd : DD.Holds x (q a-a) := hq'.sub ha
  have hb : BB.Holds x (b a) := by
    rw [b_formula]
    simpa only [Rat.cast_one] using (Enclosure.holds_const 1 x).sub (hk'.mulFull hd hx)
  have hl : JJ.Holds x (l a) := by
    rw [l_formula]
    exact (hk'.sub hq').add (ha.mulFull hb hx)
  have hy : YY.Holds x (deriv l a) := by
    rw [deriv_l_formula]
    convert (hb.scale 2 |>.sub (hq'.mulFull hd hx)).add (ha.mulFull hl hx) using 1
    norm_num
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · exact ha.trunc hx
  · exact hq'.trunc hx
  · exact hk'.trunc hx
  · exact hd.trunc hx
  · exact hb.trunc hx
  · exact hl.trunc hx
  · exact hy.trunc hx
  · change (Enclosure.const 0).trunc.Holds x 0
    simpa only [Rat.cast_zero] using (Enclosure.holds_const 0 x).trunc hx

end Submission.Obl.Entropy__two_eigenvalue_compact_certificate
