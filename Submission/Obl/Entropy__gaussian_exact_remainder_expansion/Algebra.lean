import Submission.Lib.MatrixEntropy.Expansion

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.Entropy__gaussian_exact_remainder_expansion

open Submission.Lib.MatrixEntropy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Energy completion retaining the nonsymmetric derivative residual. -/
lemma energy_completion (T K X b D g : Matrix ι ι ℝ)
    (hT : T.IsHermitian) (hK : K.IsHermitian)
    (hX : X.IsHermitian) (hb : b.IsHermitian) (hg : g.IsHermitian)
    (hKD : K = X * b + D) :
    -(T * (K * K)).trace = -(T * b * (X * X) * b).trace
      - 2 * (T * X * D * b).trace + (3/2:ℝ) * (T * X * g * b).trace
      - 2 * ((T*b-b*T)*X*(D-(3/4:ℝ) • g)).trace
      - (T*(D-(3/4:ℝ) • g).transpose*(D-(3/4:ℝ) • g)).trace
      + (9/16:ℝ) * (T*(g*g)).trace - (3/2:ℝ) * (T*K*g).trace := by
  have he := trace_energy_expansion T K X b D hT hK hX hb hKD
  have hc := trace_square_completion T D g (3/4) hT hg
  have hr := trace_commutator_reorder T b X D
  have hrg := trace_commutator_reorder T b X g
  have hKs : K.transpose = K := by simpa using hK.eq
  have hXs : X.transpose = X := by simpa using hX.eq
  have hbs : b.transpose = b := by simpa using hb.eq
  have hKD' : K = b * X + D.transpose := by
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, hKs, hXs, hbs]
      using congrArg Matrix.transpose hKD
  have hKg : (T*K*g).trace = (T*b*X*g).trace + (T*D.transpose*g).trace := by
    rw [hKD']
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc]
  have hcw : ((T*b-b*T)*X*(D-(3/4:ℝ) • g)).trace =
      ((T*b-b*T)*X*D).trace - (3/4:ℝ)*((T*b-b*T)*X*g).trace := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul]
  rw [hcw]
  norm_num only at hc
  linarith

/-- The pointwise expansion leaves precisely the two integration-by-parts residuals. -/
lemma pointwise_expansion {ρ : Type*} [Fintype ρ]
    (A Y t k b l f f' P J B S T H F : Matrix ι ι ℝ)
    (K X D L df M g v w : ρ → Matrix ι ι ℝ)
    (hT : T.IsHermitian) (hS : S.IsHermitian) (hB : B.IsHermitian)
    (hb : b.IsHermitian) (hl : l.IsHermitian)
    (hK : ∀ r, (K r).IsHermitian) (hX : ∀ r, (X r).IsHermitian)
    (hg : ∀ r, (g r).IsHermitian)
    (hKD : ∀ r, K r = X r * b + D r)
    (hBB : B = ∑ r, X r * X r)
    (hH : H = -T * (B-1))
    (hSM : S*(B-1) = -(40/3:ℝ) • T)
    (hMSM : (B-1)*S*(B-1) = (40/3:ℝ) • H)
    (he : (2:ℝ) • t-k*k = A*f-f'+b*b+1)
    (hp : P = f'-b*b-(40/3:ℝ) • (l*l))
    (hj : J = f-(3/2:ℝ) • k-(80/3:ℝ) • ((b-(7/25:ℝ) • 1)*l))
    (hF : F = Y*(b-(7/25:ℝ) • 1)+∑ r, X r*L r)
    (hM : ∀ r, M r = df r-X r*f'-2 • (D r*b)-(80/3:ℝ) • (L r*l)+
      (3/2:ℝ) • (g r*b))
    (hw : ∀ r, w r = D r-(3/4:ℝ) • g r) :
    (T*((2:ℝ) • t-k*k-∑ r, K r*K r)).trace +
      ((F+(B-1)*l).transpose*S*(F+(B-1)*l)).trace +
      (∑ r, ((v r).transpose*S*v r).trace) =
    T.trace +
      (-(H*P).trace+(T*(Y*J+∑ r, X r*M r)).trace+
        (F.transpose*S*F).trace+(∑ r, ((v r).transpose*S*v r).trace)+
        (9/16:ℝ)*(T*(∑ r, g r*g r)).trace +
        (-(T*b*B*b-T*B*b*b).trace-
          2*((T*b-b*T)*(∑ r, X r*w r)).trace-
          (T*(∑ r, (w r).transpose*w r)).trace)) +
      (T*((A-Y)*f-∑ r, X r*df r)).trace +
      (3/2:ℝ)*((T*Y*k).trace-(T*(∑ r, K r*g r)).trace) := by
  have hu := trace_initial_weighted_square F (B-1) l S T H (3/40)
    (hB.sub Matrix.isHermitian_one) hl hS hT
    (by norm_num; simpa only [neg_smul] using hSM) (by norm_num; exact hMSM)
  norm_num only at hu
  have hen (r : ρ) := energy_completion T (K r) (X r) b (D r) (g r)
    hT (hK r) (hX r) hb (hg r) (hKD r)
  have hes := congrArg (fun z : ρ → ℝ => ∑ r, z r) (funext hen)
  simp only [← hw] at hes
  rw [he, hu, hp, hj]
  simp only [hM]
  -- Keep the common positive squares opaque while expanding every linear trace.
  have hFF : (T*F*l).trace =
      (T*(Y*(b-(7/25:ℝ) • 1)+∑ r, X r*L r)*l).trace := by rw [hF]
  rw [hFF, hH, hBB]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.neg_mul, Matrix.mul_neg, two_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Matrix.mul_assoc] at hes ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hes
  linarith only [hes]

end Submission.Obl.Entropy__gaussian_exact_remainder_expansion
