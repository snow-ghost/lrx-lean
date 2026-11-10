# Palomar submission checklist

This repository contains the substantive LRX proof and an independent
statement/solution interface. Preparation does not register the result.

## Recorded mathematical claims

- `PalomarLRX.boundedRouting`: for every n ≥ 4 and every ordered pair of
  permutations, a literal L/R/X word of length at most n(n−1)/2 joins them.
- `PalomarLRX.exactDiameter`: the ordinary undirected Cayley graph with
  those generators has diameter n(n−1)/2 for every n ≥ 4.

All three letters cost one move. R is the inverse cyclic shift; rotations
are charged, and permutations are not identified modulo rotation.
The routing theorem ensures connectivity, avoiding the disconnected-graph
convention for natural-valued diameter. The result asserts neither
uniqueness of extremal permutations nor an executable shortest-word solver.

Challenge imports Mathlib alone. Its definitions are repeated in Solution,
where bridges identify the graph and preserve word evaluation and length.
The two intended proof placeholders occur only in Challenge. Solution and
the underlying development must have no missing proofs or nonstandard axioms.

## Reproduce the mechanical checks

The toolchain and Mathlib are pinned to v4.35.0. With Elan, Python 3, Git,
and Bubblewrap installed:

```sh
lake exe cache get
bash scripts/verify.sh
lake comparator --config comparator.json
```

The verification script builds LRXDiameter, Solution, and Challenge, and
audits full private and generated theorem bodies through `Verify.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Comparator checks that the independent Challenge statements are proved
by Solution. A successful build alone does not replace this comparison.
The GitHub workflow repeats these commands; inspect its result for the
exact commit being submitted.

Every committed Lean source uses the module system and has at most 10,000
physical lines. Challenge is under 300 lines and 32 KiB. The repository
contains no symbolic Lean sources or accompanying manuscript.
`formalization.yaml` identifies all seven authors, S. Uskov as responsible
maintainer, the MIT licence, mathematical sources, AI assistance, scope,
and the pre-submission review status. Source records distinguish related
work from assumptions of the proof.

## Submission fields

After the build, axiom audit, and Comparator pass for a committed snapshot,
check out that exact SHA when reproducing it. The `main` branch and the
`v1.0.0` release contain the Lean 4.35.0 submission interface:

| Field | Value |
|---|---|
| Repository | `snow-ghost/lrx-lean` |
| Commit | The full 40-character SHA from `git rev-parse HEAD` |
| Project path | Repository root |
| Comparator configuration | `comparator.json` |
| Metadata | `formalization.yaml` |
| Licence | Root `LICENSE`, MIT |

Use the immutable commit SHA; a branch name is insufficient. Submit through
[the Palomar submission site](https://submit.palomar-registry.org/).
The responsible author or maintainer should review the statement and
metadata before authorizing submission. No independent human peer review
or completed registration is asserted here.

Preparation follows [Palomar's submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
An automated editorial review and the decision to complete registration
are subsequent steps, separate from local mechanical checks.

## Current submission form

Use these values at https://submit.palomar-registry.org/:

| Form field | Value |
|---|---|
| Repository | `snow-ghost/lrx-lean` |
| Commit | The final checked 40-character SHA, never `main` or `palomar` |
| Comparator configuration | `comparator.json` |
| Project directory | Leave empty: repository root |
| Formalization metadata | Leave empty: default `formalization.yaml` |
| Existing Palomar ID | Leave empty for this new result |
| Your relationship | `I am a responsible author or maintainer of it` (confirmed by the author) |
| How approval was given | Leave empty for the responsible-author choice |
| Notes | Optional; may be left empty |

An optional manual mechanical preflight is defined in
`.github/workflows/palomar-preflight.yml`. It uses the pinned PalomarSubmission
commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` in full mode with
`palomar-standard-v1`. Check its mechanical report for `status: pass` on the
exact source SHA before submitting. Local build/audit/Comparator checks
alone do not replace that official preflight.

The preflight has no automatic pull-request trigger. A submission through
Palomar starts its own verification workflow; its result is recorded with
that submission.

The initial submission starts verification and review; completing registration
is a later decision after reading the review. The browser sign-in is performed
by the responsible person. No submission or registration is requested by this
preparation workflow.
