# Statement interface

[Challenge.lean](../Challenge.lean) defines the mathematical objects and states
sixteen principal results of the [paper](https://arxiv.org/abs/2605.23773v3).
Its definitions use Mathlib alone. [Solution.lean](../Solution.lean) repeats
these definitions and proves the statements using the repository's proof
library. Both modules use the namespace `SpanningTreeChallenge` and are
compiled in separate environments.

[comparator.json](../comparator.json) selects the sixteen theorems. Comparator
checks their types and axiom dependencies, then verifies the exported proofs.
The Challenge theorem bodies contain sixteen statement placeholders;
the Solution and proof library contain complete proofs.

## Mathematical definitions

The interface defines the induced square-lattice graph, its combinatorial
spanning-tree count, lattice isometries, the canonical corner-strip domain,
and the exceptional maximizing forms. At square cardinality, asymmetry is
the normalized symmetric difference from a translated square.

The counting construction uses rational path polynomials, layer continuants,
a modular numerator, and a signed Euclidean chain. Corner energies are defined
by nonnegative closed-walk series; Fourier coefficients use the cosine
coefficients of minus gamma. The resolvent identity uses Lean's total inverse
and division conventions for every real parameter. Away from the spectrum it
is the ordinary scalar resolvent, with convergent moment series for `abs(z) > 6`.

The [proof correspondence](proof-route-correspondence.md) gives the formulas,
coordinate conventions, and links to their implementations.

## Compared theorems

All declaration names below lie in `SpanningTreeChallenge`.

| Declaration | Mathematical content |
| --- | --- |
| `maximizer_isoperimetric` | Exact induced-edge count for every maximizer |
| `maximum_value` | Attained maximum and upper bound at every positive cardinality |
| `maximizer_iff` | All maximizing lattice-isometry classes, including the small exceptions |
| `nonuniqueness_iff` | Nonuniqueness exactly at `3, 8, 10, 13` |
| `unique_large` | Canonical maximality and uniqueness for `N >= 18` |
| `sharp_stability` | Square-cardinality stability with coefficient `alpha/4` |
| `coefficient_optimal` | Uniform optimality of that coefficient |
| `scalar_resolvent` | Scalar boundary resolvent and its rational expression |
| `scalar_series` | Convergent boundary-Green moment series equal to `q(z)/P(z)` for `abs(z) > 6` |
| `hankel_minor` | Equality of the leading Green-minor and moment-Hankel determinants |
| `scalar_chain` | Path/layer coprimality, proper numerator, decreasing remainder degrees, and linear quotients with positive leading coefficients |
| `cornerStrip_product` | Exact corner-strip spanning-tree product |
| `cornerStrip_recurrence` | Exact rational recurrence for every strip length `0 <= k <= w` |
| `extremal_count_asymptotic` | Extremal count with `O(N^(-1/2))` remainder |
| `strip_fourier_identity` | Exact critical strip-energy Fourier identity |
| `strip_energy_bound` | Uniform strip-energy bound `C_strip < 13/200` |

The [coverage index](coverage.md) also lists the supporting results and
appendix statements throughout the proof library.

## Verification

Build and audit the project using the [README instructions](../README.md#build-and-verification).
On Linux with Bubblewrap installed, run:

```sh
scripts/lake.sh env lake comparator --config comparator.json
```

On macOS, use the supported mode without the process sandbox:

```sh
scripts/lake.sh env lake comparator --config comparator.json --inadvisably-no-sandbox
```

The configuration enables NanoDa alongside Lean's exported-proof checker.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The [GitHub Actions workflow](../.github/workflows/lean.yml) runs the Linux
command and retains its output as `build/comparator.log`.

[formalization.yaml](../formalization.yaml) records the mathematical sources,
formalization methods, statement mapping, and verification results.
