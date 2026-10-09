# Manuscript–Lean proof correspondence

This note maps the results and proofs of *Spanning-Tree Maximization Forces Isoperimetry in the Square Lattice* to this Lean project. It describes the common mathematical objects, the corresponding theorems, and the places where the two proofs take different routes.

Section numbers and titles refer to the current paper in either the article or AMS layout. TeX labels provide additional search keys. The full statement index is in [coverage.md](coverage.md). Abbreviated Lean names lie in the `SpanningTreeIsoperimetry` namespace unless prefixed by `Real`. [SpanningTreeIsoperimetry.lean](../SpanningTreeIsoperimetry.lean) is the aggregate import; the included [Foundations/](../Foundations/) directory contains the `SquareMaximality` library.

## Mathematical objects

The paper studies finite connected induced subgraphs of the nearest-neighbor lattice on `Z²`. Its `tau(S)` is the number of spanning trees, and `M_N` is the largest such count among domains with `N` vertices. In [Grid.lean](../SpanningTreeIsoperimetry/Grid.lean), `Domain`, `treeCount`, and `IsMaximizer` denote the lattice domains, their spanning-tree counts, and maximality at fixed cardinality. `R_(r,s)` has `r` by `s` vertices. Equality classes are taken up to lattice translation, rotation, and reflection.

The canonical domain `C_N` is selected by `L = ceil(2 sqrt(N))`, `r = ceil((L−sqrt(L²−4N))/2)`, `s=L−r`, and `k=rs−N`, then deleting `k` consecutive vertices along the longer side at a corner. For positive `N`, the maximum is `tau(C_N)` except at `N=7,14,17`, where it is respectively `16,8960,112456`. Nonuniqueness occurs exactly at `N=3,8,10,13`; `C_N` is the unique maximizing isometry class for every `N≥18`.

The common constants are `h = 4 Catalan/pi`, the square-lattice entropy, and `alpha = log(1+sqrt(2))`, the boundary coefficient. The corner energy `E(M)` subtracts the bulk loss `h|M|` from the quadrant deletion cost. For a straight strip of `k` cells, `E_k = E(I_k)` and `C_strip = sup_k E_k`. Section 4.1 of the paper defines these energies by their nonnegative closed-walk series; [CornerEnergy.lean](../SpanningTreeIsoperimetry/CornerEnergy.lean) and [EnergyConvergence.lean](../SpanningTreeIsoperimetry/EnergyConvergence.lean) provide the formal definitions and convergence.

## Statement map

| Current paper location and result | Lean source and endpoints |
| --- | --- |
| Sections 1 and 3: every maximizer is edge-isoperimetric, with `2N−ceil(2sqrt(N))` induced edges | [Isoperimetry.lean](../SpanningTreeIsoperimetry/Isoperimetry.lean), `maximizer_isoperimetric` |
| Section 6, “Complete classification”: maximum values and all equality classes for every positive cardinality | [AllCardinalityClassification.lean](../SpanningTreeIsoperimetry/AllCardinalityClassification.lean), `maximumValueTarget`, `nonuniquenessTarget`, and `maximizer_iff`; [LargeClassification.lean](../SpanningTreeIsoperimetry/LargeClassification.lean), `uniqueClassificationTarget`, covers `N≥18` |
| Section 7.1: `log(tau(Q_n)/tau(S)) ≥ (alpha/4)n A_n(S)^2`, where `|S|=n²` and `A_n` is normalized translational symmetric difference; the coefficient is optimal | [Stability.lean](../SpanningTreeIsoperimetry/Stability.lean), `sharp_stability_inequality`; [StabilitySharpness.lean](../SpanningTreeIsoperimetry/StabilitySharpness.lean), `coefficient_optimal` |
| Section 7.2: the extremal expansion with remainder `O(N^(-1/2))` | [ExtremalAsymptotic.lean](../SpanningTreeIsoperimetry/ExtremalAsymptotic.lean), `extremal_count_asymptotic`; `maximumCount_eq_proposed` connects the intrinsic maximum to the classification formula |
| Section 8, “Exact counts for corner-strip domains”: scalar resolvent, Hankel minors, signed-chain product | [ScalarResolvent.lean](../SpanningTreeIsoperimetry/ScalarResolvent.lean), [ScalarSeries.lean](../SpanningTreeIsoperimetry/ScalarSeries.lean), and [ScalarProduct.lean](../SpanningTreeIsoperimetry/ScalarProduct.lean), `cornerStrip_product` |
| Appendix B.3, “An upper bound for strip energy”: the exact Fourier identity and uniform upper bound | [StripFourierIdentity.lean](../SpanningTreeIsoperimetry/StripFourierIdentity.lean), `regularized_identity` for every `z>4` and `strip_limit_identity` at four; the first five coefficients and their upper bound are also checked |
| Appendices A.1, A.5, A.6: Fourier identities and rectangular remainders | [StripFourierFourthOrder.lean](../SpanningTreeIsoperimetry/StripFourierFourthOrder.lean), `coefficient_fourth_order_bound`; [StripFourierLaplace.lean](../SpanningTreeIsoperimetry/StripFourierLaplace.lean), `coefficient_laplace`; [EpsilonFourierAlias.lean](../SpanningTreeIsoperimetry/EpsilonFourierAlias.lean), `epsilon_angular_integral` and `epsilon_fourier_alias`; [FourthOrderRectangleError.lean](../SpanningTreeIsoperimetry/FourthOrderRectangleError.lean), `sharpError_four` and `sharpError_three`; [FixedAspectRectangleError.lean](../SpanningTreeIsoperimetry/FixedAspectRectangleError.lean), `limiting_aspect_isBigO` |
| Section 4.5 and Appendices A.7–A.10: finite Green corrections | [CoarseStripError.lean](../SpanningTreeIsoperimetry/CoarseStripError.lean), `finite_strip_error`; [FiniteLongStripError.lean](../SpanningTreeIsoperimetry/FiniteLongStripError.lean), `finite_long_strip_error`; the singleton, short-defect, coupled-rectangle, and profile bounds are indexed in [coverage.md](coverage.md) |
| Appendix B.11, “The exceptional hulls”: small counts, including the parameter identity at `N=14` | [FourteenFacePolynomials.lean](../SpanningTreeIsoperimetry/FourteenFacePolynomials.lean), `opposite_face_charpoly`, `canonical_face_charpoly`, `face_charpoly_difference`, and `faceDeterminant_difference` |
| Appendix B.4, “Exact energies of small diagrams”: elementary intervals and fifteen energy intervals | [PrintedElementaryConstants.lean](../SpanningTreeIsoperimetry/PrintedElementaryConstants.lean) and [PrintedEnergyBounds.lean](../SpanningTreeIsoperimetry/PrintedEnergyBounds.lean) |
| Appendices B.5–B.10: bounds by defect size, finite boundary minors, and uniform corner comparisons | [RefinedCornerEnvelope.lean](../SpanningTreeIsoperimetry/RefinedCornerEnvelope.lean), `family_bound`; [FiniteBoundaryMinors.lean](../SpanningTreeIsoperimetry/FiniteBoundaryMinors.lean); [CanonicalCornerConcentration.lean](../SpanningTreeIsoperimetry/CanonicalCornerConcentration.lean), `canonical_family_optimal`; [MulticornerExclusion.lean](../SpanningTreeIsoperimetry/MulticornerExclusion.lean) and [SingleCornerExclusion.lean](../SpanningTreeIsoperimetry/SingleCornerExclusion.lean), `not_isMaximizer`; the individual comparison lemmas are indexed in [coverage.md](coverage.md) |

## Normalization in the Fourier argument

For `z>4`, `gamma_z(theta)=arcosh(z/2−cos(theta))` and `f_z=exp(−gamma_z)`. The paper denotes the cosine coefficients of `f_z` by `a_j(z)` and those of `log f_z=−gamma_z` by `v_j(z)`; both use `(1/pi) integral_0^pi (function) cos(j theta) dtheta`. The boundary Green matrix has entries `a_|i−j| − a_(i+j+2)`, with indices `0 ≤ i,j < k`. Its sine-integral representation is proved in [RegularizedBoundaryKernel.lean](../SpanningTreeIsoperimetry/RegularizedBoundaryKernel.lean).

[RegularizedMatrixNormalization.lean](../SpanningTreeIsoperimetry/RegularizedMatrixNormalization.lean) identifies the normalized matrix as `exp(−v_0(z)) G_k`. The scalar multiplies every entry, so its determinant is `exp(−k v_0(z)) det G_k`. [RegularizedFiniteSectionLimit.lean](../SpanningTreeIsoperimetry/RegularizedFiniteSectionLimit.lean) proves `h_z = −v_0(z)`, positivity of the limit, and `E_(k,z) = −log det(exp(−v_0(z)) G_k)`.

In Appendix A, the paper's `gamma_j` is a coefficient of **plus** gamma. Lean's `StripFourierCoefficients.coefficient j` is a coefficient of **minus** gamma, hence equals `−gamma_j`. In particular, the printed estimate `|gamma_j + 1/(pi*j²)| ≤ 2/(pi*j⁴)` agrees with `StripFourierFourthOrder.coefficient_fourth_order_bound`.

The positive face coordinates in the Green-function appendix are the translation of Lean's zero-based coordinates by `(1,1)`. An `R × S` face rectangle corresponds to an `(R+1) × (S+1)` primal vertex rectangle.

## Proof-route comparison

### Polarization and finite corner corrections

Section 5 expands products over reflection-pair signs. Lean proves that expansion in [Polarization.lean](../SpanningTreeIsoperimetry/Polarization.lean) and connects it to matrix traces in [PolarizationTrace.lean](../SpanningTreeIsoperimetry/PolarizationTrace.lean). A Hadamard change of basis separates the occupancy mean and difference; polarization replaces the difference by its absolute value. The reflection cover counts each vertex twice, including fixed-axis vertices, and weights each copy by one half. In [PolarizationStrict.lean](../SpanningTreeIsoperimetry/PolarizationStrict.lean), a preferred-side path joins singly occupied reflection pairs of opposite original signs; traversing it outward and back produces a strictly improved even moment.

For the finite corrections in Section 4.5, [CornerEnergyTransfer.lean](../SpanningTreeIsoperimetry/CornerEnergyTransfer.lean) sums the closed-word placements that meet the defect and leave the face rectangle. [CornerDeterminant.lean](../SpanningTreeIsoperimetry/CornerDeterminant.lean) proves, for a Ferrers defect `M` contained in the face rectangle `U`,

```text
E(M) + correction(U,M) = −log det(G_U[M]) − h|M|.
```

The word expansion gives the per-cell transfer bounds and convexity of the strip correction. [CornerLimit.lean](../SpanningTreeIsoperimetry/CornerLimit.lean) proves convergence along rectangular exhaustions.

### Finite boundary minors

**Paper (B.6):** brackets the path-polynomial roots, propagates rational intervals through continuants, and bounds the determinants using small LDL factorizations.

**Lean:** [FiniteGreenPotentials.lean](../SpanningTreeIsoperimetry/FiniteGreenPotentials.lean) verifies integer solutions of the finite Dirichlet systems. [FixedDirichletSystems.lean](../SpanningTreeIsoperimetry/FixedDirichletSystems.lean) identifies these solutions with inverse-matrix columns. Exact determinant calculations in [FiniteBoundaryMinors.lean](../SpanningTreeIsoperimetry/FiniteBoundaryMinors.lean) then prove the same eight lower bounds. [FiniteBoundaryMinorBridge.lean](../SpanningTreeIsoperimetry/FiniteBoundaryMinorBridge.lean) connects the matrix indices to the corner-strip minors.

### Strip bound and exact Fourier identity

**Paper (B.3):** integrating the logarithm of the two-dimensional lattice symbol in one variable identifies the bulk normalization. The shifted Toeplitz–Hankel theorem of Basor–Ehrhardt then gives the normalized Green-determinant limit. At the critical parameter, a uniform coefficient bound permits dominated convergence; monotone loop coefficients exchange the two suprema. This gives

```text
C_strip = (h−alpha)/2 − (1/2) sum_{j≥1} j v_j(4)^2.
```

The first five coefficients give `C_strip < .064859 < 13/200`.

**Lean:** [StripLoopBound.lean](../SpanningTreeIsoperimetry/StripLoopBound.lean) obtains a uniform bound by comparing reflected closed walks with a finite Green-minor correlation. [UniformStripEnergy.lean](../SpanningTreeIsoperimetry/UniformStripEnergy.lean) passes to two three-site blocks in a six-site half-plane boundary matrix and proves

```text
2 E_k + log(det(T_3)^2 / det(T_6)) ≤ h − alpha,
C_strip < 81/1250 < 13/200.
```

Here `T_m` is the Green matrix on `m` consecutive boundary-row sites of the half-plane for `4I−A`, with exterior neighbors killed; `T_3` is either three-site diagonal block of `T_6`. A common bound with a fixed strict margin gives the inequality for `C_strip`.

Lean then proves the Fourier determinant constant locally, following the even-symbol factorization and trace calculation in Basor–Ehrhardt, Propositions 2.3 and 4.1. It normalizes the analytic symbol, factors its finite sections using triangular Toeplitz factors, and develops determinants of identity plus entrywise summable kernels. Write `D_z(t)` for the limiting normalized determinant with deformed symbol `exp(t(log f_z−v_0(z)))`. Lean proves

```text
D_z(0) = 1,
d/dt log D_z(t) = −sum_{j≥1} v_(2j)(z) + t sum_{j≥1} j v_j(z)^2.
```

See [NormalizedLogDerivativeTrace.lean](../SpanningTreeIsoperimetry/NormalizedLogDerivativeTrace.lean), [RegularizedFiniteSectionLimit.lean](../SpanningTreeIsoperimetry/RegularizedFiniteSectionLimit.lean), and [StripFourierIdentity.lean](../SpanningTreeIsoperimetry/StripFourierIdentity.lean). The trace calculation uses summable differences and Hankel products. Integration to `t=1` and the critical limit give the paper's exact identity.

The order of the argument differs: the paper starts from the lattice-symbol integral and obtains the strip bound through the determinant theorem; Lean starts from the finite-Green bound and uses sublinear strip energy to identify the bulk coefficient in its determinant limit.

### Rectangular lower bound and remainders

**Paper (A.1, A.5, A.6):** the lemma in “Hyperbolic normalization” (`lem:epsilon-bound`) compares the logarithmic integral for `epsilon_r` with the integral on the positive half-line and bounds the omitted tail, proving `epsilon_r>1/(4r)` and monotonicity of `epsilon_r/r`. The uniform remainder is derived from Fourier coefficients, alias summation, and derivative variation.

**Lean:** [EpsilonBounds.lean](../SpanningTreeIsoperimetry/EpsilonBounds.lean) integrates the first twenty positive logarithmic terms, bounds the endpoint exponential loss, and proves the same strict `1/(4r)` lower bound by a finite rational sum. The monotonicity conclusion follows from the same decreasing integrand as in the paper.

For the remainders, [RectangularQuadrature.lean](../SpanningTreeIsoperimetry/RectangularQuadrature.lean) proves fourth- and sixth-order trapezoidal identities by integration by parts with normalized Bernoulli polynomials; [TrapezoidalKernelError.lean](../SpanningTreeIsoperimetry/TrapezoidalKernelError.lean) applies the derivative bounds. The resulting inequalities give `FourthOrderRectangleError.sharpError_four` and `sharpError_three`. The Fourier coefficient and alias identities are proved separately in `StripFourierFourthOrder`, `StripFourierLaplace`, and `EpsilonFourierAlias`.

### Reciprocal symmetry of the aspect profiles

**Paper (A.5–A.6):** `u=s/r` is the rectangle's aspect ratio. The functions `J`, `K`, and `K_2` are the aspect profiles in the area-normalized, side-sum-normalized, and next-order rectangular expansions, respectively. Expanding the same integer rectangle in both orientations, then dilating it, proves `J(u)=J(1/u)` and the corresponding symmetry of `K` and `K_2`. Continuity extends the rational-aspect identities.

**Lean:** [FirstProfileModular.lean](../SpanningTreeIsoperimetry/FirstProfileModular.lean) represents `J` through the norm of the Dedekind eta product and uses the modular discriminant transformation. [SecondProfileModular.lean](../SpanningTreeIsoperimetry/SecondProfileModular.lean) uses the weight-four Eisenstein series transformation for `K_2`. Both routes give the reciprocal symmetry and vanishing derivative at one.

### The exceptional fourteen-vertex comparison

**Paper (B.11, “The exceptional hulls”; `subsec:finite-corner-comparisons`):** the two primal domains are the `4×4` rectangle minus two opposite corner vertices and the canonical `3×5` rectangle minus one corner vertex. The former's bounded-face graph consists of two four-cycles sharing one vertex; the latter's is a `2×4` face ladder minus one corner. With `p_G(t)=det(tI−A_G)`, the gluing identity and the corner-ladder recurrence give

```text
p_opposite(t)  = t^7 − 8t^5 + 12t^3,
p_canonical(t)= t^7 − 8t^5 + 12t^3 − 3t.
```

Thus their difference is `3t` for every parameter, and evaluation at four gives `8960 − 8948 = 12`.

**Lean:** [FourteenFacePolynomials.lean](../SpanningTreeIsoperimetry/FourteenFacePolynomials.lean) identifies the bounded-face sets of these two domains, writes their seven-vertex adjacency matrices, and uses sparse determinant expansion. Its polynomial identities hold over every commutative ring; `faceDeterminant_difference` gives the face-determinant difference for every real `t`. Thus the paper's graph gluing and Lean's matrix expansion establish the same parameter identity.

### Printed rational intervals

Appendix B.4 uses the elementary intervals `3.141592653589793 < pi < 3.141592653589794`, `1.1662436 < h < 1.1662437`, and `.8813735 < alpha < .8813736`, followed by fifteen diagram-energy intervals. Lean proves these same displayed enclosures. Their derivations differ as follows:

| Quantity | Paper's derivation | Lean's derivation |
| --- | --- | --- |
| `pi` | Machin formula with twelve alternating terms | `Real.pi_gt_d20` and `Real.pi_lt_d20` from the pinned mathlib, weakened to the printed interval |
| Catalan constant and `h` | Euler's positive transform through index 32, with a `2^(-33)` tail | 800 alternating terms in sixteen blocks, followed by one Euler correction; `CatalanEulerBounds` and `NarrowEntropyBounds` |
| `sqrt(2)` | Squaring rational endpoints | The same squared-endpoint comparison |
| `alpha` and energy logarithms | Eighteen positive logarithm terms with an explicit tail, after dyadic rescaling | Twelve positive logarithm terms for lower bounds and twenty-four exponential terms for upper bounds, with dyadic rescaling |
| Green determinants | Potential-kernel recurrences, boundary reduction and rational polynomial intervals | Proved Green identities and exact rational determinant/polynomial bounds feeding `PrintedEnergyBounds` |

Lean's Catalan correction is `S_800 + a_800/2 ≤ Catalan ≤ S_800 + a_800/2 + (a_800−a_801)/2`, with `S_800 = sum_{j=0}^{799} (−1)^j a_j` and `a_j = 1/(2j+1)^2`. Its exponential upper bounds use terms indexed zero through twenty-three. Relevant sources are [PrintedElementaryConstants.lean](../SpanningTreeIsoperimetry/PrintedElementaryConstants.lean), [CatalanEulerBounds.lean](../SpanningTreeIsoperimetry/CatalanEulerBounds.lean), and [NarrowLogCertificates.lean](../SpanningTreeIsoperimetry/NarrowLogCertificates.lean).

### Exact scalar counts

**Shared mathematical route (Sections 8.2–8.3):** for an `r×s` primal rectangle, put `R=r−1`, `w=s−1`, `B=4I−A_(P_w)`, and `G=f_(R−1)(B) f_R(B)^(-1)`, where `f_j` are the path continuants. The scalar resolvent is `F(z)=e_1^T G(zI−B)^(-1)e_1=q(z)/P(z)`. Its moments give a Hankel Gram determinant equal to the leading boundary Green minor. Orthogonalization makes multiplication by the path operator tridiagonal; the Jacobi resolvent then identifies the signed Euclidean quotients. Their positive leading coefficients `b_j` give the Section 8.3 product (`eq:scalar-product`)

```text
T_k = T_0 product_{j=0}^{k−1} b_j^(−(2k−2j−1)),  0≤k≤w,
```

where `T_k` is the tree count after deleting a corner strip of length `k`. See [JacobiReduction.lean](../SpanningTreeIsoperimetry/JacobiReduction.lean), [SignedJacobiChain.lean](../SpanningTreeIsoperimetry/SignedJacobiChain.lean), and [ScalarProduct.lean](../SpanningTreeIsoperimetry/ScalarProduct.lean).

For the modular numerator in Section 8.2, [ScalarModular.lean](../SpanningTreeIsoperimetry/ScalarModular.lean) uses endpoint cyclicity and invertibility of the layer continuant to prove coprimality. A Bézout coefficient gives the modular inverse, and an adjugate recurrence identifies the proper numerator with the stated remainder. Coprimality descends to rational coefficients, where a rational Bézout coefficient gives the numerator used in the counting product.

Both use the path operator `4I−A`. The paper orthogonalizes the monomials in the moment inner product, obtaining Jacobi subdiagonal entries `+1` and superdiagonal entries `+beta_j`. Lean orthogonalizes the coordinate basis by an LDL factorization of the same Green matrix; its resulting entries are `−1` and `−beta_j` (`JacobiReduction.UnitSubdiagonal` is defined with `−1`). Alternating signs on the basis vectors conjugate one Jacobi matrix to the other. This fixes the endpoint vector and preserves the scalar resolvent, characteristic polynomials, squared norms, and leading Green-minor determinants.

The proposition in Section 8.2 (`prop:scalar-resolvent`) distinguishes the rational identity off the spectrum from its Laurent series at infinity, which converges for `|z|>6`. Lean's `ScalarSeries.rational_scalar_resolvent_hasSum` gives the real-variable convergent identity. The product includes the empty minor `k=0` and the full boundary minor `k=w`.

## Verification

The toolchain is fixed by [lean-toolchain](../lean-toolchain), and dependency revisions by [lake-manifest.json](../lake-manifest.json). [lakefile.toml](../lakefile.toml) declares the included `Foundations` library and mathlib. The pinned versions are Lean 4.34.1 and mathlib v4.34.1. The setup instructions for a fresh checkout are in the project's [README](../README.md#build-and-verification).

From the Lean project root, run

```sh
python3 scripts/audit.py
```

[audit.py](../scripts/audit.py) builds the project and runs [Audit.lean](../scripts/Audit.lean) to inspect theorem declarations and their axiom dependencies. The audit requires the listed public endpoints and permits `propext`, `Classical.choice`, and `Quot.sound`. Run it as the sole build process, with the proof sources fixed for the duration.
