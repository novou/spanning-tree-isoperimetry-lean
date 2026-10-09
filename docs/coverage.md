# Manuscript coverage

**The requested mathematical scope is complete.** The development proves all
positive-cardinality maximum values and equality classes, the sharp stability
constant, the exact scalar counting formula, the global extremal asymptotic,
and the independent appendix identities and estimates listed below.

All final results concern the actual lattice graphs, counts, Green kernels,
and coefficient integrals. Definitions ending in `Target` are theorem
statements, never assumed proofs. Additional dependencies are proved in local
source; Lean and mathlib are the permitted base libraries.

Updated 2026-10-09. The reproducible build and full compiled-environment audit
write their latest counts and declaration-level records to `build/audit.json`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The audit
also checks that the required public conclusions remain in the import closure.
GitHub Actions retains the verification reports with each workflow run.

This table follows mathematical statements, rather than every line of one
particular proof. Some numerical enclosures have different checked derivations;
see [proof-route correspondence](proof-route-correspondence.md).

| Paper file | Kind | Label | Status |
|---|---|---|---|
| `sections/01-introduction.tex` | theorem | `thm:intro-isoperimetric` | Checked: `SpanningTreeIsoperimetry.maximizer_isoperimetric`, all cardinalities |
| `sections/01-introduction.tex` | theorem | `thm:intro-classification` | Checked: `LargeClassification.uniqueClassificationTarget` and `AllCardinalityClassification.maximumValueTarget`, `nonuniquenessTarget`, `maximizer_iff` give actual maximum values and complete equality classes at every positive cardinality |
| `sections/01-introduction.tex` | theorem | `thm:intro-stability` | Checked: `sharp_stability_inequality` in `Stability.lean`; `StabilitySharpness.coefficient_optimal` proves the coefficient is optimal using actual equal-area rectangle counts and asymmetry |
| `sections/01-introduction.tex` | theorem | `thm:intro-enumeration` | Exact product formula checked in `ScalarProduct.cornerStrip_product` |
| `sections/03-isoperimetry.tex` | proposition | `prop:rectangular-comparison` | Checked: `RectangularComparison.rectangular_comparison`, strictness and equality, for every rs ≥ n² |
| `sections/03-isoperimetry.tex` | corollary | `cor:enhanced-hull` | Checked: `InteriorCost.enhanced_hull_bound_all`, including thin rectangles |
| `sections/03-isoperimetry.tex` | lemma | `lem:dual-factorization` | Checked in included `Dual/ForestProduct.lean`, instantiated by `Boundary/MatrixTreeCompletion.lean` |
| `sections/03-isoperimetry.tex` | lemma | `lem:window-charging` | Checked in included `Boundary/SlidingInjection.lean`, `Windows2D.lean`, and their canonical encoding |
| `sections/03-isoperimetry.tex` | proposition | `prop:gap-cost` | Checked: `BoundaryGap.boundary_gap_cost`, with all inputs constructed in `EnhancedBoundary` |
| `sections/03-isoperimetry.tex` | lemma | `lem:local-estimates` | Checked: `InteriorSquareGain` and `WiredPairs`, including actual free-patch and clipping geometry |
| `sections/03-isoperimetry.tex` | proposition | `prop:interior-surcharge` | Checked: `InteriorCost.interior_log_factor_lt`, with actual wired margins, events, and square gain |
| `sections/03-isoperimetry.tex` | lemma | `lem:comparison-domain` | Checked: `ComparisonDomain.comparisonDomain_log_gain`, with actual card/connectivity and closed insertion gains |
| `sections/03-isoperimetry.tex` | proposition | `prop:integer-rigidity` | Checked in full: `IntegerRigidityComparison.integer_rigidity` proves the exact quantitative log-ratio inequality for every connected domain and arbitrary translated minimal hull, with actual comparison-domain cardinality/connectivity also exported. `normalized_maximizer_defects` proves the maximizing-domain consequence |
| `sections/03-isoperimetry.tex` | lemma | `lem:four-corner` | Checked: `FourCorners.four_corner_ferrers_partition`; short-side deficit in `HullArithmetic` |
| `sections/03-isoperimetry.tex` | lemma | `lem:projection-bound` | Checked: `Projection` bound and `ProjectionEquality.edgeCount_projection_eq_iff_hull` |
| `sections/03-isoperimetry.tex` | theorem | `thm:isoperimetric-rigidity` | Checked: `Isoperimetry.lean` hull shape, convexity, no finite holes, four corners, and exact edge count |
| `sections/04-corner-rigidity.tex` | definition | `def:corner-energy` | Checked: concrete series and convergence in `CornerEnergy`, `EnergyConvergence`; finite Green-minor energy and determinant limits in `CornerLimit` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:maximal-cells` | Checked: `Ferrers.maximalCells_card_le_defectCount` and `EnergyConvergence.realEnergy_maximalCells` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:three-cell-obstruction` | Checked: `Ferrers.three_cell_obstruction` and `EnergyConvergence.realEnergy_threeCell` |
| `sections/04-corner-rigidity.tex` | lemma | `lem:repetition` | Checked: `Repetition` wordwise injections and `EnergyConvergence.realEnergy_duplicateRow` / `realEnergy_duplicateColumn` |
| `sections/04-corner-rigidity.tex` | proposition | `prop:strip-rigidity` | Checked: `StripRigidity.strip_energy_minimal`, `strip_energy_eq_iff`, and the uniform gap `nonstrip_energy_gap > 1/4000`, using actual small quadrant minors |
| `sections/04-corner-rigidity.tex` | proposition | `prop:concentration` | Checked: `CornerConcentration.concentration_minimal`, `concentration_eq_iff`, and `concentration_strict_gap`, for any finite family of Ferrers defects with positive total size |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-strip-error` | Checked: `CoarseStripError.finite_strip_error` proves the exact `4k/pi` reciprocal-square bound for both actual strip orientations; `finite_empty_strip_error` covers the empty strip including side length one. `FiniteLongStripError.finite_long_strip_error` proves the fourth-order long-side bound, with the finite inverse, quadrant limit, integral identity and flux sum included |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-transfer` | Checked: `CornerDeterminant.dirichletEnergy_transfer`; per-cell and convexity clauses in `CornerEnergyTransfer` |
| `sections/04-corner-rigidity.tex` | proposition | `prop:canonical-concentration` | Checked: `CanonicalCornerConcentration.canonical_family_optimal`, actual counts and equality iff lattice congruence on the canonical hull, every N≥18 |
| `sections/04-corner-rigidity.tex` | proposition | `prop:analytic-cutoff` | Checked: `MulticornerExclusion.not_isMaximizer` and `SingleCornerExclusion.not_isMaximizer` exclude every actual nonstrip corner configuration for N≥18; `LargeClassification.maximizer_congruent` gives the final canonical conclusion |
| `sections/04-corner-rigidity.tex` | lemma | `lem:finite-classification` | Checked for every1≤N≤17: `SmallMaximumValue.maximum_value_small` and `SmallMaximizerClassification.small_maximizer_iff`; `nonuniqueness_small_iff` proves nonuniqueness exactly at3,8,10,13 within this range |
| `sections/04-corner-rigidity.tex` | theorem | `thm:strip-reduction` | Checked through the stronger complete classification: `LargeClassification.maximizer_iff` for N≥18 and `SmallMaximizerClassification.small_maximizer_iff` below 18, assembled in `AllCardinalityClassification.maximizer_iff` |
| `sections/05-polarization.tex` | lemma | `lem:polarization` | Checked for all four lattice reflection families: `PolarizationDeterminant`, with actual finite-domain trace and spectral proofs |
| `sections/05-polarization.tex` | lemma | `lem:polarization-strict` | Checked: `PolarizationStrict`, actual preferred-domain path and opposite singleton conditions; all four reflection families |
| `sections/05-polarization.tex` | proposition | `prop:separate-corners` | Checked: `CornerSeparationTree.separate_corners_treeCount` and `separate_corners_geometry`, with actual primal counts and every geometry premise discharged |
| `sections/05-polarization.tex` | proposition | `prop:orientation` | Checked: `StripTreeComparisons.orientation_treeCount` and its exact equality condition, including thin hulls |
| `sections/05-polarization.tex` | proposition | `prop:adjacent-hull` | Checked: `StripTreeComparisons.adjacent_hull_treeCount` and exact equality condition; six triples in `StripPolarization` |
| `sections/05-polarization.tex` | proposition | `prop:two-corner-fold` | Checked: `TwoCornerStripTree` actual primal comparison, cardinality and equality exactly at (r,s,b)=(4,4,1), all four orientations |
| `sections/05-polarization.tex` | proposition | `prop:ferrers-corner-fold` | Checked: `FerrersFoldTree.exists_ferrers_primal_fold`, actual connected target, same cardinality, new hull, weak/strict improvement and literal square-hook two-strip alternative |
| `sections/05-polarization.tex` | theorem | `thm:explicit-strip` | Checked: `CanonicalStrips.canonical_strip_optimal` and `strip_family_equality_congruent` for N≥18 within the entire strip family |
| `sections/06-classification.tex` | theorem | `thm:all-N-classification` | Checked: `AllCardinalityClassification.maximumValueTarget`, `nonuniquenessTarget`, and `maximizer_iff`, with actual connected candidates, all small exceptions/equality classes, and unique canonical shape for N≥18 |
| `sections/07-counting.tex` | proposition | `prop:scalar-resolvent` | Checked: actual Green–Hankel and q/P identification in `ScalarResolvent` / `ScalarModular`, and convergent moment expansion for `abs(z) > 6` in `ScalarSeries` |
| `sections/07-counting.tex` | theorem | `thm:scalar-product` | Checked: `ScalarProduct.cornerStrip_product`, with actual rational signed-chain coefficients, positivity, degree drops and all leading Green-minor products |
| `sections/09-stability.tex` | lemma | `lem:geometric-asymmetry` | Checked: `Targets.normalizedAsymmetry_sq_le_of_fits`, for arbitrary translated containing rectangles |
| `sections/09-stability.tex` | theorem | `thm:sharp-stability` | Checked: `sharp_stability_inequality` in `Stability.lean`; `StabilitySharpness.coefficient_optimal` proves the coefficient is optimal using actual equal-area rectangle counts and asymmetry |
| `sections/09-stability.tex` | proposition | `prop:extremal-asymptotic` | Checked: `ExtremalAsymptotic.extremal_count_asymptotic` for the intrinsic global maximum; `maximumCount_eq_proposed` connects it to the full value formula, and `CanonicalCountExpansion.square_constant_limit` identifies the actual square constant |
| `appendices/A-rectangles.tex` | lemma | `lem:epsilon-bound` | Checked: `EpsilonBounds.quarter_div_lt_epsilon` |
| `appendices/A-rectangles.tex` | lemma | `lem:coupled-rectangle-error` | Checked: `CoupledRectangleBounds.refined_rectangle_error_general`, `refined_rectangle_error`, and `coupled_rectangle_error`; actual fourth-order expansion and genuine second-profile comparison |
| `appendices/A-rectangles.tex` | lemma | `lem:singleton-lower` | Checked: `FiniteSingletonSquareLower.singleton_lower_primal`, both5/(3min(r,s)^4) and square12/(5r^4), all primal sides≥2; actual kernels, all small-side cases and strict constants proved |
| `appendices/A-rectangles.tex` | lemma | `lem:short-defect-corrections` | Checked: `FiniteShortDefectError.short_defect_lower_primal`, actual two-cell21/(4r^4) and square20/r^4 bounds for r≥5,r≤s, with no matrix or analytic premise left open |
| `appendices/A-rectangles.tex` | lemma | `lem:normalized-rectangle-error` | Checked: `NormalizedRectangleError.normalized_rectangle_error`; strict source absorption in `source_absorption`, with all analytic inputs discharged |
| `appendices/A-rectangles.tex` | lemma | `lem:aspect-cost` | Checked: `AspectCost.aspect_difference`, `D_strictMonoOn`, `D_convexOn`, and `shifted_difference_antitone`, using the actual residual profile |
| `appendices/A-rectangles.tex` | lemma | `lem:flux-monotonicity` | Checked: `FluxBounds` side antitonicity, length monotonicity, diagonal monotonicity and cubic/fourth-order majorants |
| `appendices/B-boundary-minors.tex` | lemma | `lem:finite-boundary-minors` | Checked: all eight actual boundary-minor floors in `FiniteBoundaryMinors`; actual Ferrers Green-minor identification, domain monotonicity and five terminal comparisons in `FiniteBoundaryMinorBridge` |
| `appendices/B-corner-certificates.tex` | lemma | `lem:refined-envelope` | Checked: `RefinedCornerEnvelope.family_bound`, exact b(k) for every finite nonconcentrated Ferrers family, with actual obstruction kernels/energies and two-tier repetition proved |
| `appendices/B-corner-certificates.tex` | lemma | `lem:strip-supporting-lines` | Checked: `StripSupportingLines.strip_supporting_line`, actual E_k<(k+27)/600 for every k, plus the exact fifth/sixth increment bounds |
| `appendices/B-corner-certificates.tex` | lemma | `lem:large-imbalance-exclusion` | Checked: `LargeImbalanceExclusion.count_lt_canonical`, actual nonconcentrated four-corner source counts strictly below canonical whenever T≥4 and t<T |
| `appendices/B-corner-certificates.tex` | lemma | `lem:rectangular-notch-family` | Checked: `RectangularNotchComparison.square_notch_count` and `rectangle_notch_count` give the exact strict actual-count comparisons in either orientation for b=2,r≥5 and b=3,r≥8 |
| `appendices/B-corner-certificates.tex` | lemma | `lem:single-corner-reduction` | Checked reduction/exclusion: `SingleCornerSmallReduction.tall_fold_alternative` supplies the literal strict fold/square-hook alternative; `SingleCornerSmallExclusion`, `SquareSingleCornerExclusion`, and `SingleCornerExclusion.not_isMaximizer` discharge all remaining actual single-corner families. The complete classification also guarantees a strict competitor for every such nonstrip source |
| `appendices/B-small-corner-families.tex` | lemma | `lem:multicorner-uniform` | Checked: `MulticornerExclusion.count_lt_canonical` proves strict actual tree-count domination for every family with at least two nonempty corner defects on a minimum-side-sum hull, N≥18 |

## Additional closed endpoints

- `SquareResults.square_maximality`, `square_equality_iff`, and
  `square_isMaximizer` give the complete square-cardinality special case in
  the current definitions.
- `canonicalDomain_not_maximal_seventeen` in `CanonicalChecks.lean` proves that the threshold
  cannot be lowered to 17 for the canonical family. Optimality and uniqueness
  at every size at least 18 are now proved in `LargeClassification`.
- `treeCount_eq_laplacian_cofactor` in `MatrixTree.lean` and the included Kirchhoff implementation
  connect the combinatorial count to its actual primal determinant.

- `MaximizerGeometry.exists_isMaximizer` proves existence at every positive
  cardinality via a finite bound on attainable graph counts.

- `UniformStripEnergy.realEnergy_strip_lt` proves `E_k < 81/1250 < 13/200`
  for every length. `stripEnergyLimit_lt` and `realEnergy_strip_tendsto`
  prove a finite monotone strip-energy limit with the same strict upper bound.
  The proof uses actual finite Green minors and locally proved half-plane
  exhaustion; it does not assume a Toeplitz–Hankel determinant limit.
- `GreenExhaustion` identifies every entry of the actual exhausted six-site
  Green matrix and the three/six-point determinant limits.
- `LayerDeterminant.rectangleDirichlet_det_eq_continuant` gives the actual
  rectangle Dirichlet determinant from its layer continuant. The signed
  Euclidean product formula is checked in `ScalarProduct`.

- `QuadrantWalkCount` proves the second-reflection coefficient identity for
  actual quadrant words. `QuadrantGreen` exhausts actual two-site quadrant
  inverse entries to the exact boundary matrix. `SingletonEnergy` proves
  `E1 = -log(2−16/(3*pi))−h`, `E1>1/40`, and a uniform strip gap for three
  or more maximal cells. The remaining displayed small-diagram enclosures are
  proved in `PrintedEnergyBounds`.

- `ThreeCellEnergy.realEnergy_ell_exact` proves the exact L-shaped energy
  using the actual quadrant Green minor. `nonrectangle_limit_gap` gives
  `E(M)−Cstrip>3/2500` for every nonempty nonrectangular Ferrers defect.
  `nonrectangle_strip_gap` gives the same bound against every finite strip
  length. The rectangle branch and complete strip rigidity are now closed in `RectangleEnergyBounds` and `StripRigidity`.

- `FerrersPrimalBridge.primal_treeCount_eq_dirichlet` constructs every single
  Ferrers-corner primal domain with its connectedness, hull and no-interior
  hypotheses discharged. Multi-corner primal transport is also checked in
  `FiniteCornerProducts.corner_count_eq_greenMinor` and
  `corner_log_count_upper`; `FiniteCornerCharges.corner_log_count_upper_charged`
  includes the actual finite per-cell corrections.

- `CanonicalCornerPrimal.maximizer_canonicalCorner_model` identifies every
  normalized actual maximizer with the literal four Ferrers-corner primal
  construction; the deficit and both sparse bounds are proved.
- `CornerPrimalSymmetry` gives actual congruence for family reflections and
  transposition, with two-corner normalization and invariant counts/cardinality.
- `SmallShapeCatalogue` proves the six possible N≤17 nonstrip hull triples
  and the complete strip/L catalogue for a Ferrers diagram of at most three cells.
- `ThirteenFaceCounts` proves actual face counts 2656,2640,2624 for the opposite,
  L-shaped and three-singleton square-hull configurations. Exhaustive maximality
  and isometry classification are now checked in `SmallMaximizerClassification`.
- `SmallCornerProfiles.sparse_ferrers_profiles` proves the exhaustive literal
  diagram profiles for total defect at most three. `AdjacentPairExclusion`
  proves that two nonempty corners in a maximizer must be opposite, for every
  placement and orientation. `SmallTenComparison` connects the actual
  ten-vertex opposite-singleton count 209 to the canonical count.
- `LogDetTangent.log_det_tangent` and
  `GreenLogDetComparison.finite_green_logdet_bound` prove the exact finite
  matrix comparison. `GreenUnionBound` proves the actual walk-by-walk
  union inequality; `GreenStripLimits` constructs both infinite strips and
  passes it to the quadrant loss. `GreenSwap` proves all coordinate exchanges.
- `BoundaryGreenBounds` proves all actual quadrant Green-entry limits from
  nonnegative inverse series, a tent supersolution and inclusion monotonicity.
  `BoundaryFlux` proves the actual finite/quadrant boundary-flux identity.
  `BoundaryLossIntegral` and `FiniteLongStripError` complete the spectral
  integral loss and quantitative finite-strip bound.

## Independent appendix statements

The following entries record the additional displayed identities and bounds
beyond the labelled theorem table.

- **Exact strip-limit identity (now checked):**
  `StripFourierIdentity.regularized_identity` proves the actual z>4 formula,
  and `strip_limit_identity` proves
  `Cstrip = (h-alpha)/2 - (1/2)*sum j*v_j^2` at the critical parameter.
  The proof includes actual symbol/Green/energy identifications, weighted
  exponential differentiation, finite-section determinants, the explicit
  inverse, and the trace calculation. No cited determinant theorem is an
  assumed input. Both critical Fourier-sum limits and the actual strip
  supremum limit are proved. These exports are included in the aggregate.
- **Appendix A Fourier–Laplace and alias identities:**
  `StripFourierLaplace.coefficient_laplace` proves the actual integral formula.
  Lean uses the coefficients `v_j` of `-gamma`, so the paper's coefficients
  satisfy `gamma_j=-v_j`. `EpsilonFourierAlias.epsilon_fourier_alias` proves
  `epsilon_r=2r*sum v_(2ra)`, exactly the displayed identity in that convention.
  The proof includes endpoint integrability and the justified interchange
  of the logarithmic series and integral.
- **Additional appendix claims (now checked):**
  `StripFourierFourthOrder.coefficient_fourth_order_bound` proves the
  displayed j^-4 coefficient error. `FixedAspectRectangleError` extends the
  fourth-order remainder to every positive fixed or limiting aspect ratio.
  `FourteenFacePolynomials` identifies both actual N=14 face characteristic
  polynomials and their exact difference `3X`, with determinant difference
  `3t` for every real t. These were stronger claims than the previously
  checked restricted-range bounds or evaluations at t=4.
- **Printed numerical enclosures (now checked):**
  `PrintedElementaryConstants` proves the literal pi, sqrt2, entropy and alpha
  intervals. `NarrowEntropyBounds` gives the stronger
  `1.166243615 < h < 1.166243617`. `PrintedEnergyBounds` imports all nine
  obstruction and six strip two-sided intervals exactly as printed. Their
  derivations are compared in
  [Printed rational intervals](proof-route-correspondence.md#printed-rational-intervals).
- **First-profile displayed calculus (now checked):** `FirstProfileModular`
  proves actual `J_inv`, `K_inv`, `contDiffAt_J`, and `deriv_J_one`.
  `FirstProfileDerivatives.second_derivative_formula` proves Appendix A's
  explicit infinite-series formula for actual `J''`, with locally uniformly
  summable derivatives. `second_derivative_bounds` proves exactly
  `0 < -J''(u) < 1/3` for every `u>=1`, and `deriv_K_one` proves `K'(1)=0`.
  `FirstProfileQuadratic.exists_quadratic_bound` also supplies the local
  quadratic estimate used in the canonical-count asymptotic.
- **General integer-rigidity inequality (now checked):**
  `IntegerRigidityComparison.integer_rigidity` exports the full
  `eq:integer-rigidity` for every connected source and translated minimal hull.
  It uses the actual comparison-domain, rectangle and interior/boundary-cost
  estimates and assumes no maximizing property.
- **General northeast-boundary reduction (now checked):**
  `GeneralQuadrantMinorReduction.determinant_reduction` proves the exact
  full-to-boundary determinant quotient for every finite Ferrers diagram.
  `schur_complement` proves the actual Green Schur complement equals the
  finite interior Dirichlet inverse; `boundary_det_pos` and `energy_reduction`
  give positivity and the boundary-only energy formula. The actual quadrant
  Poisson equation and Ferrers neighbour closure discharge all matrix-row
  hypotheses, including empty interiors.
- **Alternate kernel/algebra routes:** the actual quadrant Green minors and
  exact determinant identities are checked through reflected path counts and
  the general reduction above. The manuscript's unrestricted potential-kernel
  recurrences and unrestricted image formula are now also closed in
  `PotentialKernelHarmonic` and `PotentialKernelImages`; bounded quadrant
  Poisson uniqueness supplies the identification with the actual Green kernel.
  `PotentialKernelDiagonal.diagonal_formula` now proves the exact diagonal
  odd-harmonic formula for every natural index, including zero. Its local
  proof includes the periodic-square rotation, Poisson cosine integral and
  finite sine-sum evaluation; none is assumed.
  Section 7's explicit trigonometric spectral weights and strict root
  interlacing are closed in `ScalarSpectralResidues` and
  `ScalarSpectralInterlacing`, including the complete path-polynomial
  factorization. All these auxiliary exports are included in the aggregate;
  the scalar-product endpoint also has an independent checked construction.

The final build and axiom report are generated by `python3 scripts/audit.py`.
