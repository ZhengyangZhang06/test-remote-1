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

## Proved helper step: normalization and convergence (end of Lemma 5.2)

Given such W_j, let g_j=exp(-W_j), Z_j=integral g_j, and
U_j=W_j+log Z_j. The common linear bound supplies a single integrable
exponential majorant for (1+norm(x)^2)*g_j. It also bounds
abs(W_j)*exp(-W_j): on u>=-B, abs(u)*exp(-u/2) is bounded, so this
entropy integrand is at most a constant times exp(-a*norm(x)/2).
All relevant functions are measurable. Every Z_j is finite and positive;
positivity follows because g_j is continuous and strictly positive.
Pointwise convergence and dominated convergence give Z_j->1,
unnormalized L1 convergence, vector first-moment convergence, coordinate
second-moment convergence, and integral(g_j*log g_j)->integral(f*log f).
At f=0 the entropy pointwise limit uses t*log t->0 as t decreases to zero.
Normalization gives exp(-U_j)=g_j/Z_j, with integral one; addition of the
constant log Z_j preserves smoothness and both Hessian bounds. Integrability
of all normalized quantities follows from the same bounds. Since Z_j->1,
the normalized L1 distances and first and raw second moments converge.
The identity Cov(h)_(i,j)=integral(h*x_i*x_j)-mean(h)_i*mean(h)_j for a
probability density converts these limits to centered covariance limits.
This identity and covariance convergence are already in the gate-accepted
Submission.Lib.EntropyTools and must be reused. Finally
H(g_j/Z_j)=-integral(g_j*log g_j)/Z_j+log Z_j
converges to H(f). This step is independent of log-concavity once
the sequence, common tail, and pointwise limit are supplied.
Normalization.lean and Limits.lean were merged from o007 branch x0017
at 88b5573, and Tails.lean was merged at b380f3a. These are complete Lean
proofs under this obligation's own subdirectory, compiled with the split.
Tails.lean proves exponential radial integrability by comparison with
(1+norm(x))^(-r), for r greater than the dimension. Its concrete polynomial
bound is
exp(-a*r)*(1+r^2)<=(1+8/a^2)*exp(-a*r/2) for r>=0,
and its entropy bound is
abs(u)*exp(-u)<=(2+abs(B)*exp(abs(B)/2))*exp(-u/2) for u>=-B.
These give the majorants used by Limits.lean. Thus no new child is needed
for the normalization and convergence arguments already supplied as proofs.

## Glue

Apply the tail child to f, then the Moreau child with its constants, then
the mollification child, then the proved normalization/convergence bridge.
The final split has three new children, with no sibling proof dependencies:
each downstream child takes its predecessor's properties as hypotheses.
Keep n=0 by taking the paper's j=n+1. The normalized potentials U_j and
the convergence conclusions give exactly the frozen parent statement.
No part of the analytic construction is claimed proved by writing this
split; the gate checks the closed interfaces and the Lean composition.

## Frozen interfaces and validation

The names are Entropy.log_concave_exponential_tail,
Entropy.moreau_envelope_sequence, and Entropy.mollified_convex_sequence.
They use only Mathlib and ChallengeDeps. The common derivative bound is
stated in the operator norm of fderiv; on this real Hilbert space this is
the gradient Lipschitz bound used in the paper. C-infinity uses the inner
ENat top coerced to WithTop ENat, exactly as in the parent.

The mollification child supplies the paper's exact Hessian constants;
its convergence conclusion is U_n(x)-Q_n(x)->0. Construction.lean proves
exp(-U_n(x))=exp(-Q_n(x))*exp(-(U_n(x)-Q_n(x))), giving the required
density limit even at zeros of f. It also packages the Hessian constants
into SmoothPotential. The main glue reassociates the Regular conjunction
to the parent's unchanged frozen statement.

The library search found no existing tail, Moreau, or mollification theorem.
The existing covariance identities and limit passage are imported through
Submission.Lib.EntropyTools.LimitPassage. lot sync generated the three
stubs, and its comparison reported no similar obligations for any child.
lake build Submission.Obl.Entropy__smooth_approximation passed, including
all four helper modules. This is validation of the conditional glue; the
three analytic child theorems still require proofs and gate acceptance.

lot check was run after the final commit. It returned exit code 4 and
reported that glue importing proposed-child stubs must be checked with
lot submit split. No failed proof check was reported; the submission is
the gate's validation step for this conditional split.
