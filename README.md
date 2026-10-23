# Spanning-tree isoperimetry in Lean

[![Lean verification](https://github.com/novou/spanning-tree-isoperimetry-lean/actions/workflows/lean.yml/badge.svg?branch=main&event=push)](https://github.com/novou/spanning-tree-isoperimetry-lean/actions/workflows/lean.yml)

Lean formalization of [*Spanning-Tree Maximization Forces Isoperimetry in the
Square Lattice*](https://arxiv.org/abs/2605.23773v3).

The project proves edge isoperimetry of spanning-tree maximizers, their maximum
values and classification up to lattice isometry for every positive cardinality,
the sharp stability inequality, exact corner-strip counts, and the extremal
asymptotic expansion. The canonical corner-strip domain is the unique maximizer
up to lattice isometry for every `N ≥ 18`; nonuniqueness occurs exactly at
`N = 3, 8, 10, 13`.

The development also includes the appendix's Fourier identities, rectangular
remainders, Green-function estimates, and numerical bounds.
[Manuscript coverage](docs/coverage.md) indexes the statements and Lean
declarations. The [proof correspondence](docs/proof-route-correspondence.md)
explains the common definitions, notation, and differences between the paper's
proofs and their formalization.

## Main theorems

The following names lie in the `SpanningTreeIsoperimetry` namespace:

| Result | Lean declaration |
| --- | --- |
| Edge isoperimetry and hull geometry | `maximizer_isoperimetric` |
| Maximum value at every positive cardinality | `AllCardinalityClassification.maximumValueTarget` |
| All maximizing isometry classes and exceptional nonuniqueness | `AllCardinalityClassification.maximizer_iff`, `AllCardinalityClassification.nonuniquenessTarget` |
| Unique canonical maximizer for `N ≥ 18` | `LargeClassification.uniqueClassificationTarget` |
| Sharp stability inequality and optimal coefficient | `sharp_stability_inequality`, `StabilitySharpness.coefficient_optimal` |
| Exact corner-strip counting product | `ScalarProduct.cornerStrip_product` |
| Exact strip-energy Fourier identity | `StripFourierIdentity.strip_limit_identity` |
| Extremal asymptotic expansion with `O(N^(-1/2))` remainder | `ExtremalAsymptotic.extremal_count_asymptotic` |

The three declarations whose names end in `Target` prove propositions defined in [Targets.lean](SpanningTreeIsoperimetry/Targets.lean).
[SpanningTreeIsoperimetry.lean](SpanningTreeIsoperimetry.lean) imports the full
development.

## Statement and proof interface

[Challenge.lean](Challenge.lean) independently defines the mathematical objects
and states sixteen principal results. Its theorem bodies are deliberate
Comparator holes. [Solution.lean](Solution.lean) supplies the corresponding
proofs from the formalization library.

[comparator.json](comparator.json) selects the compared theorems;
[formalization.yaml](formalization.yaml) records the mathematical sources,
provenance, and verification status. The
[statement interface](docs/statement-interface.md) describes the definitions,
compared results, and verification commands.

## Build and verification

### First build

Prerequisites: Python 3 and [elan](https://github.com/leanprover/elan).
The project pins Lean 4.35.0-rc2 and mathlib v4.35.0-rc2. From the repository root, run:

```sh
ELAN_HOME="$PWD/.tooling/elan" elan toolchain install "$(cat lean-toolchain)"
scripts/lake.sh exe cache get
python3 scripts/audit.py
```

These commands install the pinned toolchain, fetch the mathlib cache, and build
and audit the project. The toolchain is stored in `.tooling/elan` and selected
by `scripts/lake.sh`. [lean-toolchain](lean-toolchain) fixes the Lean version;
[lake-manifest.json](lake-manifest.json) pins dependency revisions.

### Subsequent verification

```sh
python3 scripts/audit.py
```

Current build artifacts are reused. For a build alone, run
`python3 scripts/build_serial.py`; add `--plan` to list its scope.
The build helper compiles dependencies sequentially. Run one build or audit at
a time, keeping source files fixed until it finishes.

### What the audit checks

The audit builds the project, checks that the required public theorems are
present, and inspects the axiom dependencies of the proof-library and Solution
theorems, including those in `Foundations/`. It permits `propext`, `Classical.choice`, and
`Quot.sound`. The independent Challenge holes are recorded separately.
Comparator compares the Challenge and Solution statements and checks the exported
proofs with the kernel. On Linux with Bubblewrap installed, run:

```sh
scripts/lake.sh env lake comparator --config comparator.json
```

The [statement interface](docs/statement-interface.md#verification) includes
the macOS command and explains the kernel checks.

| Output | Contents |
| --- | --- |
| `build/audit.json` | Checked declarations, required endpoints, and axiom dependencies |
| `build/build.log` | Build output |
| `build/axioms.log` | Declaration-level audit output |
| `build/serial/` | Per-module build logs |

## Continuous verification

[The GitHub Actions workflow](.github/workflows/lean.yml) runs on pushes, pull
requests, and manual dispatch. It installs the pinned toolchain, fetches
mathlib's cache, builds the project, runs the same audit, and checks the
Challenge and Solution with Comparator. Build artifacts are cached between
runs, and verification logs are retained with each run.

The badge reports the verification status of push runs on `main` in
[`novou/spanning-tree-isoperimetry-lean`](https://github.com/novou/spanning-tree-isoperimetry-lean).

## Source guide

```text
Challenge.lean                Independent statements
Solution.lean                 Proved statement interfaces
SpanningTreeIsoperimetry.lean   Aggregate proof-library import
SpanningTreeIsoperimetry/      Main proofs and supporting lemmas
Foundations/                  Included square-maximality proofs and license
docs/                         Coverage, proof correspondence, and attribution
scripts/                      Build and dependency audit
.github/workflows/            Continuous verification
```

| Topic | Starting points |
| --- | --- |
| Lattice domains and tree counts | [Grid](SpanningTreeIsoperimetry/Grid.lean), [MatrixTree](SpanningTreeIsoperimetry/MatrixTree.lean) |
| Hull comparison and isoperimetry | [InteriorCost](SpanningTreeIsoperimetry/InteriorCost.lean), [IntegerRigidityComparison](SpanningTreeIsoperimetry/IntegerRigidityComparison.lean), [Isoperimetry](SpanningTreeIsoperimetry/Isoperimetry.lean) |
| Corner energies and concentration | [CornerEnergy](SpanningTreeIsoperimetry/CornerEnergy.lean), [StripRigidity](SpanningTreeIsoperimetry/StripRigidity.lean), [CanonicalCornerConcentration](SpanningTreeIsoperimetry/CanonicalCornerConcentration.lean) |
| Polarization and classification | [StripTreeComparisons](SpanningTreeIsoperimetry/StripTreeComparisons.lean), [FerrersFoldTree](SpanningTreeIsoperimetry/FerrersFoldTree.lean), [AllCardinalityClassification](SpanningTreeIsoperimetry/AllCardinalityClassification.lean) |
| Stability and asymptotics | [Stability](SpanningTreeIsoperimetry/Stability.lean), [StabilitySharpness](SpanningTreeIsoperimetry/StabilitySharpness.lean), [ExtremalAsymptotic](SpanningTreeIsoperimetry/ExtremalAsymptotic.lean) |
| Exact counting | [ScalarResolvent](SpanningTreeIsoperimetry/ScalarResolvent.lean), [JacobiReduction](SpanningTreeIsoperimetry/JacobiReduction.lean), [ScalarProduct](SpanningTreeIsoperimetry/ScalarProduct.lean) |
| Appendix identities and bounds | [StripFourierIdentity](SpanningTreeIsoperimetry/StripFourierIdentity.lean), [FourthOrderRectangleError](SpanningTreeIsoperimetry/FourthOrderRectangleError.lean), [FiniteBoundaryMinors](SpanningTreeIsoperimetry/FiniteBoundaryMinors.lean), [PrintedEnergyBounds](SpanningTreeIsoperimetry/PrintedEnergyBounds.lean) |

### Included proof sources

Additional mathematical dependencies are included as source and checked with
the project. The square-maximality foundation is in [Foundations/](Foundations/),
and the matrix-tree proof is in
[External/KirchhoffMatrixTree.lean](SpanningTreeIsoperimetry/External/KirchhoffMatrixTree.lean).
Licenses and attribution are recorded in [third-party sources](docs/third-party.md).
