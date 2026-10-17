# `oai_101_simplex_isotropic_constant`

The simplex inequality for isotropic constants (strong isotropic constant conjecture)

- Problem ID: `oai_101_simplex_isotropic_constant`
- Test Problem: no
- Submitter: (statement formalised for the First Proof / LOT experiment)
- Source: OpenAI, `A sharp entropy bound and the simplex inequality for isotropic constants`, October 5, 2026, Theorem 1.1 (inequality and equality case). See `../FIDELITY.md` for the correspondence between the paper and the Lean statement.

Do not modify `Challenge.lean` or `Solution.lean`. Those files are part of the
trusted benchmark and fixed by the repository.

Write your solution in `Submission.lean` and any additional local modules under
`Submission/`.

Participants may use declarations from the existing Mathlib imports. Broadening
the import header (especially to `import Mathlib`) can change elaboration of the
fixed statement; any added import must leave `lake build Solution` green. Helper
code not available through compatible imports must be inlined into the workspace.

Multi-file submissions are allowed through `Submission.lean` and additional local
modules under `Submission/`.

`lake test` runs comparator for this problem. The command expects a comparator
binary in `PATH`, or in the `COMPARATOR_BIN` environment variable.
