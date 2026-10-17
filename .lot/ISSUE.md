# o016: Entropy.mollified_convex_sequence

Type: `∀ m : ℕ, 1 ≤ m → ∀ Q : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ 1 (Q n) ∧ ConvexOn ℝ Set.univ (Q n) ∧ ∀ x y : (EuclideanSpace ℝ (Fin m)), ‖fderiv ℝ (Q n) x - fderiv ℝ (Q n) y‖ ≤ ((n : ℝ) + 1) * ‖x - y‖) → ∃ U : ℕ → (EuclideanSpace ℝ (Fin m)) → ℝ, (∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (U n) ∧ ∀ x v : (EuclideanSpace ℝ (Fin m)), (2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (U n)) x v) v ∧ (fderiv ℝ (fderiv ℝ (U n)) x v) v ≤ ((n : ℝ) + 1 + 2 / ((n : ℝ) + 1)) * ‖v‖ ^ 2) ∧ (∀ n x, Q n x ≤ U n x) ∧ ∀ x, Filter.Tendsto (fun n => U n x - Q n x) Filter.atTop (nhds 0)`

Statement: Lemma 5.2, smooth-potentials and Hessian-bounds step: any C1 convex sequence Q_n whose derivative is (n+1)-Lipschitz has smooth majorants U_n with Hessian between 2/(n+1) and n+1+2/(n+1), and U_n-Q_n tending pointwise to zero. Construct by even mollification at radius 1/(n+1) and addition of norm(x)^2/(n+1).

Role in the glue of o007: Supplies positive bounded smooth Hessians while preserving the common lower bound and density limit. The existing normalization and dominated-convergence helpers finish the parent.

Depends on: none
Weight: 4
Module: Submission/Obl/Entropy__mollified_convex_sequence.lean

Reviewer's comment: -

## The parent's proof (PROOF.md)

# Proof and proposed cut for Entropy.smooth_approximation

This split follows Section 5 of the supplied paper: Lemma 5.1 and the
Moreau, mollification, and dominated-convergence steps of Lemma 5.2.
The interfaces below use real functions and exp(-Q), so bounded supports
are handled without adding a new extended-real definition to a frozen type.
All new propositions will be closed over Mathlib and ChallengeDeps.

## 1. Exponential tail (Lemma 5.1)

Let f satisfy the parent's nonnegativity, upper semicontinuity,
log-concavity, integrability, and mass-one hypotheses. Put V=-log f on
S={f>0}, and V=+infinity outside S. S is convex; -log f is convex there.
Upper semicontinuity of f gives lower semicontinuity of V, including
at points outside S. Mass one makes S nonempty and of positive volume.
A convex positive-volume set has nonempty interior. Choose a simplex
inside S with interior, and bound V above there by its vertex values.
Thus a sublevel of V contains a ball. The next larger closed convex
sublevel has finite volume, since exp(-V) has integral one. It is bounded:
the convex hull of the ball and a distant point contains a cone whose
volume grows linearly with the distance (an interval in dimension one).
Along each ray from the center, convexity then gives a positive linear
lower bound for V outside a fixed ball. Lower semicontinuity and absence
of -infinity give a finite lower bound on the remaining compact ball.
Enlarge the constant to obtain a>0 and b>=0 with V(x)>=a*norm(x)-b.
Equivalently, f(x)<=exp(b-a*norm(x)) for all x, including f(x)=0.
Only this tail conclusion is requested from the first child; its moment
and entropy consequences are used in the final dominated-convergence step.

## 2. Moreau envelopes (Lemma 5.2 through its envelope-limit equation)

For j=n+1, minimize -log(f(y)) + j*norm(x-y)^2/2 over y in S.
The extended objective is lower semicontinuous, proper, coercive, and
strictly convex, hence has a unique minimizer p_j(x). Its minimum Q_j(x)
is finite. The tail bound and the triangle inequality give
Q_j(x)>=a*norm(x)-b-a^2/(2*j)>=a*norm(x)-(b+a^2/2).
Comparing the minimum at p with p+s*(z-p) and taking s down to zero gives
the subgradient inequality
V(z)>=V(p)+j*inner(x-p,z-p).
Adding it at x and x' yields
inner(x-x',p_j(x)-p_j(x'))>=norm(p_j(x)-p_j(x'))^2.
Both p_j and x-p_j(x) are 1-Lipschitz. Comparing the two minimizers at x
and x+h shows that Q_j is continuously differentiable with gradient
j*(x-p_j(x)), hence with j-Lipschitz derivative. Joint convexity of the
minimized function gives convexity of Q_j.
The Q_j increase and are at most V wherever V is finite. If Q_j(x)
remains bounded, the quadratic penalty and V>=-b imply p_j(x)->x;
lower semicontinuity then forces Q_j(x)->V(x). If V(x)=+infinity,
the same argument rules out bounded Q_j(x). Consequently exp(-Q_j(x))
converges to f(x) at every point. The second child packages the resulting
C1 convex sequence, its derivative bound, its common linear lower bound,
and this pointwise convergence.

## 3. Smooth Hessian bounds (Lemma 5.2, smooth-potentials step)

Choose an even, nonnegative C-infinity bump eta supported in the unit
ball, of integral one. Convolve Q_j with eta at radius 1/j and add
norm(x)^2/j to obtain W_j. Smooth convolution gives C-infinity regularity.
Convolution preserves convexity and the j-Lipschitz derivative bound,
so its Hessian is between 0 and j times the identity. The quadratic
summand adds 2/j times the identity, giving the required strictly positive
lower and finite upper Hessian bounds. Evenness makes the first moment
of eta vanish. Jensen gives Q_j<=Q_j*eta_(1/j); the Lipschitz derivative
Taylor bound gives Q_j*eta_(1/j)<=Q_j+1/(2*j). Thus
0<=W_j-Q_j<=1/(2*j)+norm(x)^2/j.
This preserves the common linear lower bound and ensures
exp(-W_j(x))->f(x), also where f is zero. This child assumes the exact
C1 convex sequence interface supplied by child 2 and does not use any
integral, entropy, or covariance conclusion of the parent.

