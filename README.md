# The LRX Cayley graph: exact diameter in Lean 4

**Authors: S. Uskov, A. Chervov, F. Levkovich-Maslyuk, I. Litvak, A. Smolensky, A. Soibelman, Dia Taha.**
[Authorship](AUTHORS.md) · [Русский](README.ru.md)
S. Uskov — ORCID: [0009-0006-5845-7013](https://orcid.org/0009-0006-5845-7013).

This repository formalizes the exact diameter of the Cayley graph of the
symmetric group Sₙ with three generators: L, a cyclic shift; R = L⁻¹;
and X, the transposition of the first two positions. Each letter costs
one move. For every integer n ≥ 4, the diameter is **n(n−1)/2**.
The problem is recorded in [OEIS A186783](https://oeis.org/A186783).

Both upper and lower bounds are proved in Lean. The main theorem has no
additional combinatorial hypotheses. The typeclass `NeZero n`, needed to
define the cyclic generators, follows from n ≥ 4.

## Main theorem

[`LRX.exact_diameter_all`](LRX/SharpDiameterAll.lean):

```lean
import LRX.SharpDiameterAll

example (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    (LRX.graph n).diam = n * (n - 1) / 2 :=
  LRX.exact_diameter_all n hn
```

[`LRXDiameter.lean`](LRXDiameter.lean) re-exports the result as
`LRXDiameter.exact_diameter`.

| Result | Lean declaration |
|---|---|
| Exact diameter for every n ≥ 4 | `LRX.exact_diameter_all` |
| Sharp upper bound for every n ≥ 4 | `LRX.sharp_diameter_all` |
| Routing for nonzero majorized lifts | `LRX.nonzero_lift_routing` |
| Matching lower bound | `LRX.diam_lower` |

[`LRX/Graph.lean`](LRX/Graph.lean) defines the graph using Mathlib's
`SimpleGraph.mulCayley`. [`LRX/WordMetric.lean`](LRX/WordMetric.lean)
relates graph walks to literal words in L, R, X. The lower bound is linked
to the list model by `LRX.ListBridge.graphIso`.
The theorem establishes the diameter; uniqueness of an extremal
permutation is a separate claim. Word existence uses classical reasoning;
the repository does not provide an executable shortest-word solver.

## Reproduce the verification

Install [Elan](https://github.com/leanprover/elan), Git, Python 3, and the
usual Lean build prerequisites. Then run:

```sh
git clone https://github.com/snow-ghost/lrx-lean.git
cd lrx-lean
lake exe cache get
bash scripts/verify.sh
```

The toolchain is pinned to **Lean 4.34.0**. Mathlib is pinned to commit
`5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0). Exact dependency
revisions are recorded in [`lake-manifest.json`](lake-manifest.json).
The cache command downloads Mathlib artifacts; the build checks the
proof sources in this repository.

[`scripts/verify.sh`](scripts/verify.sh) checks:

1. Source integrity against [`files.sha256`](files.sha256).
2. Absence of `sorry`, `admit`, `native_decide`, postulated `axiom`,
   `unsafe`, `implemented_by`, and `extern` outside comments.
3. The complete build with `lake build`.
4. [`Verify.lean`](Verify.lean), which audits every theorem of every
   package module, including private and generated helper theorems.

Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Any other axiom, including `sorryAx`, fails the audit.
Finite certificates are checked by the Lean kernel using `decide +kernel`;
the certificate generators are not trusted inputs to the proof.

The [GitHub Actions workflow](.github/workflows/lean.yml) builds the proof
and runs these checks on pushes and pull requests. Its current result is
shown in the repository's Actions tab. Each Lean process has an 8000 MB
memory limit; `LEAN_NUM_THREADS` can be set to reduce parallelism.

## Proof structure

| Path | Role |
|---|---|
| [`LRX/SharpDiameterAll.lean`](LRX/SharpDiameterAll.lean) | Final diameter and routing theorems |
| [`LRX/Graph.lean`](LRX/Graph.lean), [`LRX/WordMetric.lean`](LRX/WordMetric.lean) | Graph, generators, words, and their metric connection |
| `LRX/ExactDiameter.lean`, `GraphBridge.lean`, `GraphLower.lean`, `LRX/ListBridge.lean`, `LRX/LowerBound*.lean` | Lower bound and the bridge between graph and list models |
| `LRX/UpperReduction.lean` through `LRX/NinePeakPayment.lean` | Upper-bound reductions and case analysis |
| `LRX/Small{4,5,6}.lean`, `LRX/PackedSmall8*`, `LRX/NineShell*`, `LRX/TwoSizeCertificates/`, `LRX/*Chunks/` | Finite certificates |
| `Research/CayleyPy/` | Seven arithmetic modules used by the proof |
| `scripts/generators/` | Optional witness generators |
| [`provenance/`](provenance/) | Dependency and pruning records |

The proof contains 1137 modules, plus the entry point `LRXDiameter.lean`
and the verification file `Verify.lean`. The source set is restricted to
dependencies of the main diameter theorem. Pruning removed 66 modules
and 460 declarations. All remaining proof modules contribute to the
recorded constant dependency closure.

There are 23 user-level declarations outside that closure: retained
`simp` lemmas, derived `DecidableEq` instances, two lemmas in generated
certificate files, and one definitional equality needed by `simp only`.
These exceptions preserve source compilation and certificate reproducibility;
strict declaration-by-declaration minimality is not claimed.
The records are in [`provenance/dependency-closure.tsv`](provenance/dependency-closure.tsv),
[`provenance/pruning-report.json`](provenance/pruning-report.json), and
[`provenance/keep_extra.txt`](provenance/keep_extra.txt).

The repository contains the formalization, verification tools, and their
documentation. The build and audit require no accompanying manuscript.

## Citation and license

Please cite **S. Uskov, A. Chervov, F. Levkovich-Maslyuk, I. Litvak,
A. Smolensky, A. Soibelman, Dia Taha, _The LRX Cayley graph: exact diameter
of the symmetric group in Lean 4_**, with a link to this repository and,
preferably, a commit. GitHub's citation button uses [`CITATION.cff`](CITATION.cff).

The project is licensed under [MIT](LICENSE). Retain the copyright and
permission notices when redistributing the code. See [authorship](AUTHORS.md).
