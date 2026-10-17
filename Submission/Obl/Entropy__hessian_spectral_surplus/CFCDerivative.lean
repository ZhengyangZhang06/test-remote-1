import Submission.Obl.Entropy__c1_bounded_matrix_calculus.CFCField
import Submission.Lib.PairEstimate.SpectralAlgebra

open scoped BigOperators Topology
open Matrix

namespace Submission.Obl.Entropy__hessian_spectral_surplus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Continuous scalar functions act continuously on Hermitian matrix fields. -/
lemma continuous_cfc_matrix {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℝ} (hA : ∀ x, (A x).IsHermitian)
    (hAc : Continuous A) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x => cfc f (A x)) := by
  exact Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) (by simp) hAc hA hf.continuousOn

/-- Daleckii--Krein's formula in any direction, including repeated eigenvalues. -/
theorem cfc_fderiv_in_eigenbasis {A : E → Matrix n n ℝ} {x : E}
    (hA : ∀ y, (A y).IsHermitian) (hAc : Continuous A)
    (hAd : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) (v : E) (i j : n) :
    let U : Matrix n n ℝ := (hA x).eigenvectorUnitary
    (U.transpose * Matrix.of (fun s t => fderiv ℝ (fun y => cfc f (A y) s t) x v) * U) i j =
      dslope f ((hA x).eigenvalues i) ((hA x).eigenvalues j) *
        (U.transpose * Matrix.of (fun s t => fderiv ℝ (fun y => A y s t) x v) * U) i j := by
  exact Submission.Obl.Entropy__c1_bounded_matrix_calculus.entryDirectionalDerivative_cfc_eigenbasis
    A (fun i j => hAc.matrix_elem i j) hA hf hAd v i j

end Submission.Obl.Entropy__hessian_spectral_surplus
