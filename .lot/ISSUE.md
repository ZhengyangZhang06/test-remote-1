# Task: The simplex inequality for isotropic constants (strong isotropic constant conjecture) (Lean-Eval `oai_101_simplex_isotropic_constant`)

Fill all 2 holes of the Lean-Eval problem `oai_101_simplex_isotropic_constant` in `Submission.lean`. The frozen
statement is in `Challenge.lean`, its vocabulary in `ChallengeDeps.lean`. Read `README.md`, `Challenge.lean`, `ChallengeDeps.lean` and
`holes.json` first.

Source: OpenAI, `A sharp entropy bound and the simplex inequality for isotropic constants`, October 5, 2026, Theorem 1.1 (inequality and equality case). See `../FIDELITY.md` for the correspondence between the paper and the Lean statement.

## Holes

| # | Kind | Challenge name | Fill in `Submission.lean` as |
|---|---|---|---|
| 1 | theorem | `theorem_1_1_ineq` | `Submission.theorem_1_1_ineq` |
| 2 | theorem | `theorem_1_1_eq` | `Submission.theorem_1_1_eq` |

`config.json` lists the theorems (`theorem_names`) and the required definitions (`definition_names`)
the comparator checks. The starter `Submission.lean` already declares every hole under
`namespace Submission`, with `sorry`: replace each `sorry` (a definition hole gets its data, a
theorem hole its proof). Keep every hole's name, binders (in this order) and type exactly as
written: `Solution.lean` restates the challenge and takes each hole from `Submission`, and the
comparator checks that its statements and definitions are the challenge's. Helper modules go in
`Submission/*.lean` (for example the existing `Submission/Helpers.lean`).

## Rules

- Toolchain is pinned: Lean v4.33.0, Mathlib `6f1ef4e5dd604a435bddba4747b13970cd65d2a1`.
  Do not change `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and do not run
  `lake update` or `lake exe cache get`.
- Everything except `Submission.lean` and `Submission/` is protected and must stay
  byte-identical (`.gitignore`, `Challenge.lean`, `ChallengeDeps.lean`, `README.md`, `Solution.lean`, `WorkspaceTest.lean`, `config.json`, `holes.json`, `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`, this file). Do not add `.lean` files anywhere else.
- Only `Submission.lean` and `.lean` files under `Submission/` with plain names (letters,
  digits, `_`) are taken from your checkout; the checker rebuilds everything else from the
  pristine workspace. No symbolic links anywhere in the repository (`.lake/` excepted).
- No `sorry`, `admit`, new axioms, `native_decide`, or other unsafe mechanisms. Only `propext`,
  `Quot.sound` and `Classical.choice` are permitted (checked transitively). For the root check
  no `sorry` may remain anywhere in the Submission sources.
- Submissions may not use IO, compile-time evaluation or command elaboration from text
  (`#eval`, `run_cmd`, `include_str`, `elabCommand`, ...), nor `unsafe`, `implemented_by` or
  `extern`.
- A fresh checkout has no `.lake/`. Before building in one, link the prebuilt Mathlib instead
  of downloading it:
  `mkdir -p .lake && ln -s /home/ubuntu/lean-runs/lean-test/deps/mathlib-6f1ef4e5/.lake/packages .lake/packages`
  (it is read-only), then `lake build Submission` / `lake build Solution`.
- Child theorems of a decomposition are checked as `Submission.<lean_name>` against their frozen
  type, elaborated in a file that imports exactly `Mathlib` and what `imports.txt` lists (`import ChallengeDeps`) (see
  `/home/ubuntu/lean-runs/lean-test/trusted-v7/oai_101_simplex_isotropic_constant/imports.txt`), with no `open` or
  `namespace`, and with `autoImplicit` off. Write fully qualified names and bind every variable;
  do not mention `Submission` declarations. A lemma declared as `Submission.foo` has
  `lean_name` `foo`; one declared as `Submission.Foo.bar` has `lean_name` `Foo.bar`.

## Acceptance

`bash /home/ubuntu/lean-runs/lean-test/trusted-v7/oai_101_simplex_isotropic_constant/check.sh <node_id>` (the configured
comparator command) exits 0 and prints `Your solution is okay!`. For `root` it verifies the
protected files, scans the Submission sources for forbidden constructs, then runs the official
comparator with `config.json` (theorems `theorem_1_1_ineq`, `theorem_1_1_eq`) and the nanoda kernel forced on, exactly as
Lean-Eval's `lake test` does: statement and definition equality, transitive axioms, and kernel
replay.
