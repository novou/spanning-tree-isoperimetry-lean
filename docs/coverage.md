# Manuscript coverage

This index maps the paper's statements to Lean declarations. It covers the
all-cardinality maximum values and equality classes, sharp stability, exact
scalar counts, extremal asymptotics, and appendix identities and estimates.
Abbreviated names lie in `SpanningTreeIsoperimetry` unless indicated otherwise.

The [proof correspondence](proof-route-correspondence.md) explains the
mathematical objects, normalizations, and proof methods. The
[statement interface](statement-interface.md) gives the sixteen principal
results selected for independent comparison. Build and audit commands are
in the [README](../README.md#build-and-verification).

| Paper file | Kind | Label | Lean implementation |
|---|---|---|---|
| `sections/01-introduction.tex` | theorem | `thm:intro-isoperimetric` | `SpanningTreeIsoperimetry.maximizer_isoperimetric`, all cardinalities |
| `sections/01-introduction.tex` | theorem | `thm:intro-classification` | `LargeClassification.uniqueClassificationTarget` and `AllCardinalityClassification.maximumValueTarget`, `nonuniquenessTarget`, `maximizer_iff` give maximum values and complete equality classes at every positive cardinality |
| `sections/01-introduction.tex` | theorem | `thm:intro-stability` | `sharp_stability_inequality` in `Stability.lean`; `StabilitySharpness.coefficient_optimal` proves the coefficient is optimal using equal-area rectangle counts and asymmetry |
| `sections/01-introduction.tex` | overview | Section 1.3, Exact enumeration | Exact product formula in `ScalarProduct.cornerStrip_product`; the formal manuscript statement is `thm:scalar-product` in Section 8 |
| `sections/03-isoperimetry.tex` | proposition | `prop:rectangular-comparison` | `RectangularComparison.rectangular_comparison`, strictness and equality, for every rs ≥ n² |
| `sections/03-isoperimetry.tex` | corollary | `cor:enhanced-hull` | `InteriorCost.enhanced_hull_bound_all`, including thin rectangles |
| `sections/03-isoperimetry.tex` | lemma | `lem:dual-factorization` | Included `Dual/ForestProduct.lean`, instantiated by `Boundary/MatrixTreeCompletion.lean` |
| `sections/03-isoperimetry.tex` | lemma | `lem:window-charging` | Included `Boundary/SlidingInjection.lean`, `Windows2D.lean`, and their canonical encoding |
| `sections/03-isoperimetry.tex` | proposition | `prop:gap-cost` | `BoundaryGap.boundary_gap_cost`, with inputs constructed in `EnhancedBoundary` |
| `sections/03-isoperimetry.tex` | lemma | `lem:local-estimates` | `InteriorSquareGain` and `WiredPairs`, including free-patch and clipping geometry |
| `sections/03-isoperimetry.tex` | proposition | `prop:interior-surcharge` | `InteriorCost.interior_log_factor_lt`, with wired margins, events, and square gain |
| `sections/03-isoperimetry.tex` | lemma | `lem:comparison-domain` | `ComparisonDomain.comparisonDomain_log_gain`, with card/connectivity and closed insertion gains |
| `sections/03-isoperimetry.tex` | proposition | `prop:integer-rigidity` | `IntegerRigidityComparison.integer_rigidity` proves the exact quantitative log-ratio inequality for every connected domain and arbitrary translated minimal hull, with comparison-domain cardinality/connectivity also exported. `normalized_maximizer_defects` proves the maximizing-domain consequence |
| `sections/03-isoperimetry.tex` | lemma | `lem:four-corner` | `FourCorners.four_corner_ferrers_partition`; short-side deficit in `HullArithmetic` |
| `sections/03-isoperimetry.tex` | lemma | `lem:projection-bound` | `Projection` bound and `ProjectionEquality.edgeCount_projection_eq_iff_hull` |
| `sections/03-isoperimetry.tex` | theorem | `thm:isoperimetric-rigidity` | `Isoperimetry.lean` hull shape, convexity, no finite holes, four corners, and exact edge count |
| `sections/04-corner-rigidity.tex` | definition | `def:corner-energy` | concrete series and convergence in `CornerEnergy`, `EnergyConvergence`; finite Green-minor energy and determinant limits in `CornerLimit` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:maximal-cells` | `Ferrers.maximalCells_card_le_defectCount` and `EnergyConvergence.realEnergy_maximalCells` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:three-cell-obstruction` | `Ferrers.three_cell_obstruction` and `EnergyConvergence.realEnergy_threeCell` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:repetition` | `Repetition` wordwise injections and `EnergyConvergence.realEnergy_duplicateRow` / `realEnergy_duplicateColumn` |
| `sections/04-corner-rigidity.tex` | proposition | `prop:strip-rigidity` | `StripRigidity.strip_energy_minimal`, `strip_energy_eq_iff`, and the uniform gap `nonstrip_energy_gap > 1/4000`, using small quadrant minors |
| `sections/04-corner-rigidity.tex` | proposition | `prop:concentration` | `CornerConcentration.concentration_minimal`, `concentration_eq_iff`, and `concentration_strict_gap`, for any finite family of Ferrers defects with positive total size |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-strip-error` | `CoarseStripError.finite_strip_error` proves the exact `4k/pi` reciprocal-square bound for both strip orientations; `finite_empty_strip_error` covers the empty strip including side length one. `FiniteLongStripError.finite_long_strip_error` proves the fourth-order long-side bound, with the finite inverse, quadrant limit, integral identity and flux sum included |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-transfer` | `CornerDeterminant.dirichletEnergy_transfer`; per-cell and convexity clauses in `CornerEnergyTransfer` |
| `sections/04-corner-rigidity.tex` | proposition | `prop:canonical-concentration` | `CanonicalCornerConcentration.canonical_family_optimal`, counts and equality iff lattice congruence on the canonical hull, every N≥18 |
| `sections/04-corner-rigidity.tex` | proposition | `prop:analytic-cutoff` | `MulticornerExclusion.not_isMaximizer` and `SingleCornerExclusion.not_isMaximizer` exclude every nonstrip corner configuration for N≥18; `LargeClassification.maximizer_congruent` gives the final canonical conclusion |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-classification` | For every `1 ≤ N ≤ 17`: `SmallMaximumValue.maximum_value_small` and `SmallMaximizerClassification.small_maximizer_iff`; `nonuniqueness_small_iff` proves nonuniqueness exactly at `3, 8, 10, 13` within this range |
| `sections/04-corner-rigidity.tex` | theorem | `thm:strip-reduction` | Complete classification: `LargeClassification.maximizer_iff` for N≥18 and `SmallMaximizerClassification.small_maximizer_iff` below 18, assembled in `AllCardinalityClassification.maximizer_iff` |
| `sections/05-polarization.tex` | lemma | `lem:polarization` | All four lattice reflection families: `PolarizationDeterminant`, with finite-domain trace and spectral proofs |
| `sections/05-polarization.tex` | lemma | `lem:polarization-strict` | `PolarizationStrict`, preferred-domain path and opposite singleton conditions; all four reflection families |
| `sections/05-polarization.tex` | proposition | `prop:separate-corners` | `CornerSeparationTree.separate_corners_treeCount` and `separate_corners_geometry`, with primal counts and every geometry premise discharged |
| `sections/05-polarization.tex` | proposition | `prop:orientation` | `StripTreeComparisons.orientation_treeCount` and its exact equality condition, including thin hulls |
| `sections/05-polarization.tex` | proposition | `prop:adjacent-hull` | `StripTreeComparisons.adjacent_hull_treeCount` and exact equality condition; six triples in `StripPolarization` |
| `sections/05-polarization.tex` | proposition | `prop:two-corner-fold` | `TwoCornerStripTree` primal comparison, cardinality and equality exactly at (r,s,b)=(4,4,1), all four orientations |
| `sections/05-polarization.tex` | proposition | `prop:ferrers-corner-fold` | `FerrersFoldTree.exists_ferrers_primal_fold`, connected target, same cardinality, new hull, weak/strict improvement and square-hook two-strip alternative |
| `sections/05-polarization.tex` | theorem | `thm:explicit-strip` | `CanonicalStrips.canonical_strip_optimal` and `strip_family_equality_congruent` for N≥18 within the entire strip family |
| `sections/06-classification.tex` | theorem | `thm:all-N-classification` | `AllCardinalityClassification.maximumValueTarget`, `nonuniquenessTarget`, and `maximizer_iff`, with connected candidates, all small exceptions/equality classes, and unique canonical shape for N≥18 |
| `sections/07-counting.tex` | proposition | `prop:scalar-resolvent` | Green–Hankel and q/P identification in `ScalarResolvent` / `ScalarModular`, and convergent moment expansion for `abs(z) > 6` in `ScalarSeries` |
| `sections/07-counting.tex` | theorem | `thm:scalar-product` | `ScalarProduct.cornerStrip_product`, with rational signed-chain coefficients, positivity, degree drops and all leading Green-minor products |
| `sections/09-stability.tex` | lemma | `lem:geometric-asymmetry` | `Targets.normalizedAsymmetry_sq_le_of_fits`, for arbitrary translated containing rectangles |
| `sections/09-stability.tex` | theorem | `thm:sharp-stability` | `sharp_stability_inequality` in `Stability.lean`; `StabilitySharpness.coefficient_optimal` proves the coefficient is optimal using equal-area rectangle counts and asymmetry |
| `sections/09-stability.tex` | proposition | `prop:extremal-asymptotic` | `ExtremalAsymptotic.extremal_count_asymptotic` for the intrinsic global maximum; `maximumCount_eq_proposed` connects it to the full value formula, and `CanonicalCountExpansion.square_constant_limit` identifies the square constant |
| `appendices/A-rectangles.tex` | lemma | `lem:epsilon-bound` | `EpsilonBounds.quarter_div_lt_epsilon` |
| `appendices/A-rectangles.tex` | lemma | `lem:coupled-rectangle-error` | `CoupledRectangleBounds.refined_rectangle_error_general`, `refined_rectangle_error`, and `coupled_rectangle_error`; fourth-order expansion and second-profile comparison |
| `appendices/A-rectangles.tex` | lemma | `lem:singleton-lower` | `FiniteSingletonSquareLower.singleton_lower_primal`, `5/(3 min(r,s)^4)` and the square bound `12/(5r^4)`, all primal sides ≥ 2; kernels, all small-side cases and strict constants proved |
| `appendices/A-rectangles.tex` | lemma | `lem:short-defect-corrections` | `FiniteShortDefectError.short_defect_lower_primal`, two-cell `21/(4r^4)` and square `20/r^4` bounds for `r ≥ 5`, `r ≤ s`, from the finite Green kernels and their estimates |
| `appendices/A-rectangles.tex` | lemma | `lem:normalized-rectangle-error` | `NormalizedRectangleError.normalized_rectangle_error`; strict source absorption in `source_absorption`, with the required analytic estimates |
| `appendices/A-rectangles.tex` | lemma | `lem:aspect-cost` | `AspectCost.aspect_difference`, `D_strictMonoOn`, `D_convexOn`, and `shifted_difference_antitone`, using the residual profile |
| `appendices/A-rectangles.tex` | lemma | `lem:flux-monotonicity` | `FluxBounds` side antitonicity, length monotonicity, diagonal monotonicity and cubic/fourth-order majorants |
| `appendices/B-boundary-minors.tex` | lemma | `lem:finite-boundary-minors` | all eight boundary-minor floors in `FiniteBoundaryMinors`; Ferrers Green-minor identification, domain monotonicity and five terminal comparisons in `FiniteBoundaryMinorBridge` |
| `appendices/B-corner-certificates.tex` | lemma | `lem:refined-envelope` | `RefinedCornerEnvelope.family_bound`, exact b(k) for every finite nonconcentrated Ferrers family, with obstruction kernels/energies and two-tier repetition proved |
| `appendices/B-corner-certificates.tex` | lemma | `lem:strip-supporting-lines` | `StripSupportingLines.strip_supporting_line`, `E_k < (k+27)/600` for every k, plus the exact fifth/sixth increment bounds |
| `appendices/B-corner-certificates.tex` | lemma | `lem:large-imbalance-exclusion` | `LargeImbalanceExclusion.count_lt_canonical`, nonconcentrated four-corner source counts strictly below canonical whenever T≥4 and t<T |
| `appendices/B-corner-certificates.tex` | lemma | `lem:rectangular-notch-family` | `RectangularNotchComparison.square_notch_count` and `rectangle_notch_count` give the exact strict actual-count comparisons in either orientation for b=2,r≥5 and b=3,r≥8 |
| `appendices/B-corner-certificates.tex` | lemma | `lem:single-corner-reduction` | `SingleCornerSmallReduction.tall_fold_alternative` supplies the strict fold/square-hook alternative; `SingleCornerSmallExclusion`, `SquareSingleCornerExclusion`, and `SingleCornerExclusion.not_isMaximizer` cover the single-corner families. The complete classification also guarantees a strict competitor for every such nonstrip source |
| `appendices/B-small-corner-families.tex` | lemma | `lem:multicorner-uniform` | `MulticornerExclusion.count_lt_canonical` proves strict tree-count domination for every family with at least two nonempty corner defects on a minimum-side-sum hull, N≥18 |

## Additional results

- `SquareResults.square_maximality`, `square_equality_iff`, and
  `square_isMaximizer` give the complete square-cardinality special case in
  the current definitions.
- `canonicalDomain_not_maximal_seventeen` in `CanonicalChecks.lean` proves that the threshold
  cannot be lowered to 17 for the canonical family. Optimality and uniqueness
  at every size at least 18 are proved in `LargeClassification`.
- `treeCount_eq_laplacian_cofactor` in `MatrixTree.lean` and the included Kirchhoff implementation
  connect the combinatorial count to its primal determinant.

- `MaximizerGeometry.exists_isMaximizer` proves existence at every positive
  cardinality via a finite bound on attainable graph counts.

- `UniformStripEnergy.realEnergy_strip_lt` proves `E_k < 81/1250 < 13/200`
  for every length. `stripEnergyLimit_lt` and `realEnergy_strip_tendsto`
  prove a finite monotone strip-energy limit with the same strict upper bound.
  The proof uses finite Green minors and half-plane exhaustion.
- `GreenExhaustion` identifies every entry of the exhausted six-site
  Green matrix and the three/six-point determinant limits.
- `LayerDeterminant.rectangleDirichlet_det_eq_continuant` gives the
  rectangle Dirichlet determinant from its layer continuant. The signed
  Euclidean product formula is checked in `ScalarProduct`.

- `QuadrantWalkCount` proves the second-reflection coefficient identity for
  quadrant words. `QuadrantGreen` exhausts two-site quadrant
  inverse entries to the exact boundary matrix. `SingletonEnergy` proves
  `E1 = -log(2−16/(3*pi))−h`, `E1>1/40`, and a uniform strip gap for three
  or more maximal cells. The displayed small-diagram enclosures are
  proved in `PrintedEnergyBounds`.

- `ThreeCellEnergy.realEnergy_ell_exact` proves the exact L-shaped energy
  using the quadrant Green minor. `nonrectangle_limit_gap` gives
  `E(M)−Cstrip>3/2500` for every nonempty nonrectangular Ferrers defect.
  `nonrectangle_strip_gap` gives the same bound against every finite strip
  length. The rectangle branch and complete strip rigidity are proved in `RectangleEnergyBounds` and `StripRigidity`.

- `FerrersPrimalBridge.primal_treeCount_eq_dirichlet` constructs every single
  Ferrers-corner primal domain with its connectedness, hull and no-interior
  hypotheses discharged. Multi-corner primal transport is also checked in
  `FiniteCornerProducts.corner_count_eq_greenMinor` and
  `corner_log_count_upper`; `FiniteCornerCharges.corner_log_count_upper_charged`
  includes the finite per-cell corrections.

- `CanonicalCornerPrimal.maximizer_canonicalCorner_model` identifies every
  normalized maximizer with the four Ferrers-corner primal
  construction; the deficit and both sparse bounds are proved.
- `CornerPrimalSymmetry` gives congruence for family reflections and
  transposition, with two-corner normalization and invariant counts/cardinality.
- `SmallShapeCatalogue` proves the six possible N≤17 nonstrip hull triples
  and the complete strip/L catalogue for a Ferrers diagram of at most three cells.
- `ThirteenFaceCounts` proves face counts 2656,2640,2624 for the opposite,
  L-shaped and three-singleton square-hull configurations. Exhaustive maximality
  and isometry classification are proved in `SmallMaximizerClassification`.
- `SmallCornerProfiles.sparse_ferrers_profiles` proves the exhaustive
  diagram profiles for total defect at most three. `AdjacentPairExclusion`
  proves that two nonempty corners in a maximizer must be opposite, for every
  placement and orientation. `SmallTenComparison` connects the
  ten-vertex opposite-singleton count 209 to the canonical count.
- `LogDetTangent.log_det_tangent` and
  `GreenLogDetComparison.finite_green_logdet_bound` prove the exact finite
  matrix comparison. `GreenUnionBound` proves the walk-by-walk
  union inequality; `GreenStripLimits` constructs both infinite strips and
  passes it to the quadrant loss. `GreenSwap` proves all coordinate exchanges.
- `BoundaryGreenBounds` proves all quadrant Green-entry limits from
  nonnegative inverse series, a tent supersolution and inclusion monotonicity.
  `BoundaryFlux` proves the finite/quadrant boundary-flux identity.
  `BoundaryLossIntegral` and `FiniteLongStripError` complete the spectral
  integral loss and quantitative finite-strip bound.

## Additional appendix identities and estimates

The following entries record the additional displayed identities and bounds
beyond the labelled theorem table.

- **Exact strip-limit identity:**
  `StripFourierIdentity.regularized_identity` proves the z>4 formula,
  and `strip_limit_identity` proves
  `Cstrip = (h-alpha)/2 - (1/2)*sum j*v_j^2` at the critical parameter.
  The proof includes symbol/Green/energy identifications, weighted
  exponential differentiation, finite-section determinants, the explicit
  inverse, and the trace calculation. It also proves both critical Fourier-sum
  limits and the strip supremum limit.
- **Appendix A Fourier–Laplace and alias identities:**
  `StripFourierLaplace.coefficient_laplace` proves the integral formula.
  Lean uses the coefficients `v_j` of `-gamma`, so the paper's coefficients
  satisfy `gamma_j=-v_j`. `EpsilonFourierAlias.epsilon_fourier_alias` proves
  `epsilon_r=2r*sum v_(2ra)`, exactly the displayed identity in that convention.
  The proof includes endpoint integrability and the justified interchange
  of the logarithmic series and integral.
- **Additional appendix claims:**
  `StripFourierFourthOrder.coefficient_fourth_order_bound` proves the
  displayed j^-4 coefficient error. `FixedAspectRectangleError` extends the
  fourth-order remainder to every positive fixed or limiting aspect ratio.
  `FourteenFacePolynomials` identifies both N=14 face characteristic
  polynomials and their exact difference `3X`, with determinant difference
  `3t` for every real t.
- **Printed numerical enclosures:**
  `PrintedElementaryConstants` proves the pi, sqrt2, entropy and alpha
  intervals. `NarrowEntropyBounds` gives the stronger
  `1.166243615 < h < 1.166243617`. `PrintedEnergyBounds` imports all nine
  obstruction and six strip two-sided intervals exactly as printed. Their
  derivations are compared in
  [Printed rational intervals](proof-route-correspondence.md#printed-rational-intervals).
- **First-profile displayed calculus:** `FirstProfileModular`
  proves `J_inv`, `K_inv`, `contDiffAt_J`, and `deriv_J_one`.
  `FirstProfileDerivatives.second_derivative_formula` proves Appendix A's
  explicit infinite-series formula for `J''`, with locally uniformly
  summable derivatives. `second_derivative_bounds` proves exactly
  `0 < -J''(u) < 1/3` for every `u>=1`, and `deriv_K_one` proves `K'(1)=0`.
  `FirstProfileQuadratic.exists_quadratic_bound` also supplies the local
  quadratic estimate used in the canonical-count asymptotic.
- **General integer-rigidity inequality:**
  `IntegerRigidityComparison.integer_rigidity` exports the full
  `eq:integer-rigidity` for every connected source and translated minimal hull.
  It uses the comparison-domain, rectangle and interior/boundary-cost
  estimates and assumes no maximizing property.
- **General northeast-boundary reduction:**
  `GeneralQuadrantMinorReduction.determinant_reduction` proves the exact
  full-to-boundary determinant quotient for every finite Ferrers diagram.
  `schur_complement` proves the Green Schur complement equals the
  finite interior Dirichlet inverse; `boundary_det_pos` and `energy_reduction`
  give positivity and the boundary-only energy formula. The quadrant
  Poisson equation and Ferrers neighbour closure discharge all matrix-row
  hypotheses, including empty interiors.
- **Alternate kernel/algebra routes:** the quadrant Green minors and
  exact determinant identities are checked through reflected path counts and
  the general reduction above. The manuscript's unrestricted potential-kernel
  recurrences and unrestricted image formula are proved in
  `PotentialKernelHarmonic` and `PotentialKernelImages`; bounded quadrant
  Poisson uniqueness supplies the identification with the Green kernel.
  `PotentialKernelDiagonal.diagonal_formula` proves the exact diagonal
  odd-harmonic formula for every natural index, including zero. Its local
  proof includes the periodic-square rotation, Poisson cosine integral and
  finite sine-sum evaluation.
  Section 7's explicit trigonometric spectral weights and strict root
  interlacing are proved in `ScalarSpectralResidues` and
  `ScalarSpectralInterlacing`, including the complete path-polynomial
  factorization. The scalar-product theorem also has an independent
  construction in `ScalarProduct`.
