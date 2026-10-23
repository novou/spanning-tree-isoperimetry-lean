module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Spanning-tree maximization in the square lattice

Independent statement of the principal results of *Spanning-Tree Maximization
Forces Isoperimetry in the Square Lattice*. All mathematical objects below
are defined from Mathlib. The theorem bodies are the challenge holes.

Coordinates denote vertices, so `rectangle r s` has `r*s` vertices. Congruence
allows translations, coordinate exchange and independent coordinate signs.
The scalar counting construction uses rational polynomial arithmetic, and
the corner energy uses the actual four nearest-neighbor direction words.
-/

namespace SpanningTreeChallenge

open scoped BigOperators Matrix symmDiff Topology Classical
open Filter Asymptotics Polynomial

noncomputable section

/-- Integer lattice vertices, given by ordered pairs of integer coordinates. -/
abbrev Vertex := ℤ × ℤ
/-- Finite sets of integer lattice vertices. -/
abbrev Domain := Finset Vertex

/-- The nearest-neighbor graph on the square lattice, with Manhattan distance one. -/
def lattice : SimpleGraph Vertex where
  Adj u v := (u.1 = v.1 ∧ |u.2 - v.2| = 1) ∨
    (u.2 = v.2 ∧ |u.1 - v.1| = 1)
  symm := ⟨by
    intro u v h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩
    · exact Or.inr ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩⟩
  loopless := ⟨by intro u; simp⟩

/-- The graph induced by the square lattice on the vertex set S. -/
def domainGraph (S : Domain) : SimpleGraph (S : Set Vertex) := lattice.induce S

/-- Tree subgraphs of the induced lattice graph on S, using its full vertex set. -/
def SpanningTrees (S : Domain) :=
  {T : SimpleGraph (S : Set Vertex) // T ≤ domainGraph S ∧ T.IsTree}

/-- The number of spanning trees of the induced lattice graph on S. -/
def treeCount (S : Domain) : ℕ := Nat.card (SpanningTrees S)

/-- S is connected and maximizes the tree count among connected domains of its cardinality. -/
def IsMaximizer (S : Domain) : Prop :=
  (domainGraph S).Connected ∧ ∀ T : Domain, T.card = S.card →
    (domainGraph T).Connected → treeCount T ≤ treeCount S

/-- The r-by-s vertex rectangle with coordinates 0 ≤ x < r and 0 ≤ y < s. -/
def rectangle (r s : ℕ) : Domain :=
  Finset.Ico (0 : ℤ) r ×ˢ Finset.Ico (0 : ℤ) s

/-- The r-by-s rectangle after deletion of the initial corner strip {0} × {0,…,k−1}. -/
def cornerStrip (r s k : ℕ) : Domain := rectangle r s \ rectangle 1 k

/-- Translation of v by the integer vector a. -/
def translate (a v : Vertex) : Vertex := (a.1 + v.1, a.2 + v.2)

/-- The affine coordinate map given by optional exchange, scaling by sx,sy, and translation by a. -/
def rigidMotion (a : Vertex) (swap : Bool) (sx sy : ℤ) (v : Vertex) : Vertex :=
  let p := if swap then (v.2, v.1) else v
  (a.1 + sx * p.1, a.2 + sy * p.2)

/-- Equality up to lattice translation, coordinate exchange, and independent sign changes. -/
def Congruent (S T : Domain) : Prop :=
  ∃ a : Vertex, ∃ swap : Bool, ∃ sx sy : ℤ,
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    S.image (rigidMotion a swap sx sy) = T

/-- The integer ceiling of twice the square root of N, the least enclosing rectangle side sum. -/
def minimumSideSum (N : ℕ) : ℕ := ⌈2 * Real.sqrt (N : ℝ)⌉₊

/-- The largest nonnegative T satisfying T(T+e) ≤ d, computed by an integer square root. -/
def selectorIndex (d e : ℕ) : ℕ := (Nat.sqrt (e ^ 2 + 4 * d) - e) / 2

/-- The selected short side r, long side s, and deleted strip length k for cardinality N. -/
def canonicalParameters (N : ℕ) : ℕ × ℕ × ℕ :=
  let L := minimumSideSum N
  let m := L / 2
  let e := L % 2
  let d := m * (m + e) - N
  let T := selectorIndex d e
  (m - T, m + e + T, d - T * (T + e))

/-- The canonical corner-strip domain with the parameters selected for N. -/
def canonicalDomain (N : ℕ) : Domain :=
  let p := canonicalParameters N
  cornerStrip p.1 p.2.1 p.2.2

/-- The canonical tree count, replaced by 16, 8960, and 112456 at N=7,14,17 respectively. -/
def proposedMaximum (N : ℕ) : ℕ :=
  if N = 7 then 16 else if N = 14 then 8960 else if N = 17 then 112456
  else treeCount (canonicalDomain N)

/-- The opposite-corner representative at N=7,10,13,14,17, defaulting to the N=17 shape. -/
def oppositeDomain (N : ℕ) : Domain :=
  if N = 7 then rectangle 3 3 \ {(0, 0), (2, 2)}
  else if N = 10 then rectangle 3 4 \ {(0, 0), (2, 3)}
  else if N = 13 then rectangle 4 4 \ {(0, 0), (1, 0), (3, 3)}
  else if N = 14 then rectangle 4 4 \ {(0, 0), (3, 3)}
  else rectangle 4 5 \ {(0, 0), (0, 1), (3, 4)}

/-- The cardinalities 7,10,13,14,17 admitting opposite-corner forms in the classification. -/
def ExceptionalSize (N : ℕ) : Prop := N = 7 ∨ N = 10 ∨ N = 13 ∨ N = 14 ∨ N = 17

/-- The listed canonical, alternate-strip, and opposite-corner forms for the small classification. -/
def SmallForm (N : ℕ) (S : Domain) : Prop :=
  (N ≠ 7 ∧ N ≠ 14 ∧ N ≠ 17 ∧ Congruent S (canonicalDomain N)) ∨
  (N = 3 ∧ Congruent S (cornerStrip 2 2 1)) ∨
  (N = 8 ∧ Congruent S (cornerStrip 3 3 1)) ∨
  (N = 10 ∧ Congruent S (cornerStrip 3 4 2)) ∨
  (ExceptionalSize N ∧ Congruent S (oppositeDomain N))

/-- The listed small forms for N ≤ 17, and the canonical congruence class for N ≥ 18. -/
def MaximizerForm (N : ℕ) (S : Domain) : Prop :=
  if N ≤ 17 then SmallForm N S else Congruent S (canonicalDomain N)

/-- Two maximizing N-vertex domains exist in distinct lattice congruence classes. -/
def HasNonisometricMaximizers (N : ℕ) : Prop :=
  ∃ S T : Domain, S.card = N ∧ T.card = N ∧
    IsMaximizer S ∧ IsMaximizer T ∧ ¬Congruent S T

/-- The number of undirected edges in the induced lattice graph on S. -/
def edgeCount (S : Domain) : ℕ := Nat.card (domainGraph S).edgeSet

/-- The minimum translated n-by-n square symmetric-difference cardinality, divided by n². -/
def normalizedAsymmetry (n : ℕ) (S : Domain) : ℝ :=
  ((sInf {k : ℕ | ∃ a : Vertex,
    k = (S ∆ (rectangle n n).image (translate a)).card} : ℕ) : ℝ) / (n : ℝ) ^ 2

/-- The boundary coefficient log(1+√2). -/
def alpha : ℝ := Real.log (1 + Real.sqrt 2)

/-- Catalan’s constant, given by the alternating odd reciprocal-square series. -/
def catalanConstant : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

/-- The square-lattice spanning-tree entropy, equal to 4 Catalan/π. -/
def entropy : ℝ := 4 * catalanConstant / Real.pi

/-- Length-ℓ sequences of four nearest-neighbor direction labels. -/
abbrev Word (ℓ : ℕ) := Fin ℓ → Fin 4
/-- Nonnegative integer coordinates for cells in the quadrant. -/
abbrev Point := ℕ × ℕ
/-- Finite sets of quadrant cells. -/
abbrev Diagram := Finset Point

/-- The four steps (1,0), (−1,0), (0,1), (0,−1), indexed in that order. -/
def direction : Fin 4 → Vertex := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The displacement after the first min(i,ℓ) steps of w. -/
def position {ℓ : ℕ} (w : Word ℓ) (i : ℕ) : Vertex :=
  ∑ t : Fin ℓ, if t.val < i then direction (w t) else 0

/-- All partial-sum positions of w, including its initial and terminal positions. -/
def visited {ℓ : ℕ} (w : Word ℓ) : Finset Vertex :=
  (Finset.range (ℓ + 1)).image (position w)

/-- Every word’s visited set contains its initial position. -/
theorem visited_nonempty {ℓ : ℕ} (w : Word ℓ) : (visited w).Nonempty := by
  refine ⟨0, Finset.mem_image.mpr ⟨0, by simp, ?_⟩⟩
  simp [position]

/-- Direction words whose total displacement is zero. -/
abbrev ClosedWord (ℓ : ℕ) := {w : Word ℓ // position w ℓ = (0, 0)}

/-- The least first coordinate attained by the nonempty finite set V. -/
def minimumX (V : Finset Vertex) (hV : V.Nonempty) : ℤ :=
  (V.image Prod.fst).min' (hV.image Prod.fst)

/-- The least second coordinate attained by the nonempty finite set V. -/
def minimumY (V : Finset Vertex) (hV : V.Nonempty) : ℤ :=
  (V.image Prod.snd).min' (hV.image Prod.snd)

/-- Subtract the coordinate minima of V from p and truncate negative coordinates to zero. -/
def normalizePoint (V : Finset Vertex) (hV : V.Nonempty) (p : Vertex) : Point :=
  ((p.1 - minimumX V hV).toNat, (p.2 - minimumY V hV).toNat)

/-- The visited set of w translated so that each coordinate minimum is zero. -/
def normalizedVisited {ℓ : ℕ} (w : Word ℓ) : Diagram :=
  (visited w).image (normalizePoint (visited w) (visited_nonempty w))

/-- Translation of the quadrant point p by the nonnegative vector t. -/
def shift (t p : Point) : Point := (t.1 + p.1, t.2 + p.2)

/-- Points t of M for which the translated pattern t+P intersects M. -/
def hitStarts (M P : Diagram) : Diagram :=
  M.filter (fun t => ∃ p ∈ P, shift t p ∈ M)

/-- The number of starts in M whose translated pattern does not intersect M. -/
def defectCount (M P : Diagram) : ℕ := M.card - (hitStarts M P).card

/-- The k-cell horizontal diagram {(x,0) | 0 ≤ x < k}. -/
def horizontalStrip (k : ℕ) : Diagram := Finset.range k ×ˢ {(0 : ℕ)}

/-- The sum of defects over closed length-ℓ words, using their normalized visited patterns. -/
def defectSum (M : Diagram) (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, defectCount M (normalizedVisited w.val)

/-- The quadrant strip energy ∑_{ℓ≥1} defectSum(I_k,ℓ)/(ℓ·4^ℓ). -/
def stripEnergy (k : ℕ) : ℝ :=
  ∑' n : ℕ, (defectSum (horizontalStrip k) (n + 1) : ℝ) /
    ((n + 1 : ℝ) * 4 ^ (n + 1))

/-- The supremum of stripEnergy k over all nonnegative strip lengths k. -/
def stripEnergyLimit : ℝ := ⨆ k : ℕ, stripEnergy k

/-- The square-shape constant (5/4)log 2 − π/12 + ∑_{m≥1} log(1−exp(−2πm)). -/
def squareConstant : ℝ :=
  (5 / 4) * Real.log 2 - Real.pi * (1 : ℝ) / 12 +
    ∑' n : ℕ, Real.log (1 - Real.exp (-2 * Real.pi * (1 : ℝ) * (n + 1)))

/-- The supremum of tree counts over all connected N-vertex lattice domains. -/
def maximumCount (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Domain, S.card = N ∧
    (domainGraph S).Connected ∧ treeCount S = k}

/-- The approximation entropy·N − alpha·minimumSideSum N − (log N)/4 + squareConstant − stripEnergy k_N. -/
def mainTerm (N : ℕ) : ℝ :=
  entropy * N - alpha * minimumSideSum N - (1 / 4) * Real.log (N : ℝ) +
    squareConstant - stripEnergy (canonicalParameters N).2.2

/-- The jth cosine coefficient of −2 arsinh(sin(θ/2)), with normalization 1/π on [0,π]. -/
def fourierCoefficient (j : ℕ) : ℝ :=
  (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi,
    -(2 * Real.arsinh (Real.sin (θ / 2))) * Real.cos ((j : ℝ) * θ))

/-- Path continuants f₀=1, f₁=t, and fₙ₊₂=t fₙ₊₁−fₙ. -/
def continuant {K : Type*} [CommRing K] (t : K) : ℕ → K
  | 0 => 1
  | 1 => t
  | n + 2 => t * continuant t (n + 1) - continuant t n

/-- The rational characteristic polynomial P_w(X)=f_w(X−4) of the w-site path operator. -/
def pathPolynomial (w : ℕ) : Polynomial ℚ := continuant (X - C 4) w

/-- The first extended-gcd coefficient of f,P, scaled by gcd(f,P)(0)⁻¹. -/
def normalizedGcdA {K : Type*} [Field K] (f P : Polynomial K) : Polynomial K :=
  C ((EuclideanDomain.gcd f P).coeff 0)⁻¹ * EuclideanDomain.gcdA f P

/-- The normalized extended-gcd inverse coefficient for f_R(X) modulo P_w(X). -/
def inverseCoefficient (R w : ℕ) : Polynomial ℚ :=
  normalizedGcdA (continuant (X : Polynomial ℚ) R) (pathPolynomial w)

/-- The remainder of f_{R−1}(X) times the inverse coefficient modulo P_w(X). -/
def greenPolynomial (R w : ℕ) : Polynomial ℚ :=
  (continuant (X : Polynomial ℚ) (R - 1) * inverseCoefficient R w) %ₘ pathPolynomial w

/-- The reduced resolvent numerator q=(greenPolynomial · P_{w−1}) mod P_w. -/
def scalarNumerator (R w : ℕ) : Polynomial ℚ :=
  (greenPolynomial R w * pathPolynomial (w - 1)) %ₘ pathPolynomial w

/-- The w-site Dirichlet path matrix B=4I−A_path. -/
def pathOperator (w : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  (4 : ℝ) • 1 - (SimpleGraph.pathGraph w).adjMatrix ℝ

/-- Matrix path continuants F₀=I, F₁=B, and Fₙ₊₂=B Fₙ₊₁−Fₙ for B=pathOperator w. -/
def operatorContinuant (w : ℕ) : ℕ → Matrix (Fin w) (Fin w) ℝ
  | 0 => 1
  | 1 => pathOperator w
  | n + 2 => pathOperator w * operatorContinuant w (n + 1) - operatorContinuant w n

/-- The ratio F_{R−1}(B) F_R(B)⁻¹, the first rectangular boundary Green block for positive R,w. -/
def boundaryGreen (R w : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  operatorContinuant w (R - 1) * (operatorContinuant w R)⁻¹

/-- The nth endpoint moment (G Bⁿ)₀₀ for the w-site path operator B. -/
def moment {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (n : ℕ) : ℝ :=
  (G * pathOperator w ^ n) ⟨0, hw⟩ ⟨0, hw⟩

/-- The k-by-k moment matrix with entry m_{i+j} at indices 0 ≤ i,j < k. -/
def hankel {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j => moment hw G (i.1 + j.1)

/-- The signed Euclidean chain r₀=P, r₁=q, and rₙ₊₂=−(rₙ mod rₙ₊₁). -/
def signedRemainders (P q : Polynomial ℚ) : ℕ → Polynomial ℚ
  | 0 => P
  | 1 => q
  | n + 2 => -(signedRemainders P q n % signedRemainders P q (n + 1))

/-- The leading coefficient b_n of the nth quotient in the signed chain of P_w and q_{R,w}. -/
def scalarCoefficient (R w n : ℕ) : ℚ :=
  (signedRemainders (pathPolynomial w) (scalarNumerator R w) n /
    signedRemainders (pathPolynomial w) (scalarNumerator R w) (n + 1)).leadingCoeff

/-- The prefix product b₀⋯b_{k−1}, with empty product one. -/
def prefixProduct (b : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => b n * prefixProduct b n

/-- The rational updates T₀=T and T_{k+1}=T_k/(b_k · (b₀⋯b_{k−1})²). -/
def countRecurrence (T : ℚ) (b : ℕ → ℚ) : ℕ → ℚ
  | 0 => T
  | n + 1 => countRecurrence T b n / (b n * prefixProduct b n ^ 2)

/-! Principal theorem obligations. -/

/-- Every tree-count maximizer attains the square-lattice edge-isoperimetric bound. -/
theorem maximizer_isoperimetric {S : Domain} (hS : IsMaximizer S) :
    edgeCount S = 2 * S.card - minimumSideSum S.card := by
  sorry

/-- The displayed count formula is attained and bounds every connected N-vertex domain. -/
theorem maximum_value (N : ℕ) (hN : 0 < N) :
    (∃ S : Domain, S.card = N ∧ (domainGraph S).Connected ∧
      treeCount S = proposedMaximum N) ∧
    ∀ S : Domain, S.card = N → (domainGraph S).Connected →
      treeCount S ≤ proposedMaximum N := by
  sorry

/-- The maximizing domains are exactly the listed lattice congruence classes. -/
theorem maximizer_iff {S : Domain} (hS : 0 < S.card) :
    IsMaximizer S ↔ MaximizerForm S.card S := by
  sorry

/-- Nonisometric maximizers occur exactly at cardinalities 3,8,10,13. -/
theorem nonuniqueness_iff (N : ℕ) (hN : 0 < N) :
    HasNonisometricMaximizers N ↔ N = 3 ∨ N = 8 ∨ N = 10 ∨ N = 13 := by
  sorry

/-- For N ≥ 18, the canonical domain is a maximizer and represents its unique congruence class. -/
theorem unique_large (N : ℕ) (hN : 18 ≤ N) :
    IsMaximizer (canonicalDomain N) ∧ ∀ S : Domain, S.card = N →
      IsMaximizer S → Congruent S (canonicalDomain N) := by
  sorry

/-- Every connected n²-vertex domain satisfies stability with coefficient α/4. -/
theorem sharp_stability {n : ℕ} (hn : 0 < n) (S : Domain)
    (hcard : S.card = n ^ 2) (hconn : (domainGraph S).Connected) :
    Real.log ((treeCount (rectangle n n) : ℝ) / treeCount S) ≥
      (alpha / 4) * n * normalizedAsymmetry n S ^ 2 := by
  sorry

/-- Every coefficient valid uniformly in the square-cardinality stability inequality is at most α/4. -/
theorem coefficient_optimal {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ S : Domain, S.card = n ^ 2 →
      (domainGraph S).Connected → C * n * normalizedAsymmetry n S ^ 2 ≤
        Real.log ((treeCount (rectangle n n) : ℝ) / treeCount S)) :
    C ≤ alpha / 4 := by
  sorry

/-- The endpoint resolvent of the rectangular Green block equals the rational function q/P_w. -/
theorem scalar_resolvent {R w : ℕ} (hR : 0 < R) (hw : 0 < w) (z : ℝ) :
    (boundaryGreen R w *
      (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩ =
      (scalarNumerator R w).eval₂ (algebraMap ℚ ℝ) z /
        (pathPolynomial w).eval₂ (algebraMap ℚ ℝ) z := by
  sorry

/-- For |z| > 6, the moment Laurent series converges to the rational scalar resolvent. -/
theorem scalar_series {R w : ℕ} (hR : 0 < R) (hw : 0 < w)
    (z : ℝ) (hz : 6 < |z|) :
    HasSum (fun n : ℕ => moment hw (boundaryGreen R w) n / z ^ (n + 1))
      ((scalarNumerator R w).eval₂ (algebraMap ℚ ℝ) z /
        (pathPolynomial w).eval₂ (algebraMap ℚ ℝ) z) := by
  sorry

/-- Every leading boundary Green minor equals the corresponding moment Hankel determinant. -/
theorem hankel_minor {R w k : ℕ} (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    ((boundaryGreen R w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      (hankel hw (boundaryGreen R w) k).det := by
  sorry

/-- The rational signed chain has exact degree drops and positive linear-quotient coefficients. -/
theorem scalar_chain {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    IsCoprime (pathPolynomial w) (continuant (X : Polynomial ℚ) R) ∧
    (scalarNumerator R w).natDegree < w ∧
    (∀ n : ℕ, n ≤ w →
      (signedRemainders (pathPolynomial w) (scalarNumerator R w) n).natDegree = w - n) ∧
    (∀ n : ℕ, n < w → 0 < scalarCoefficient R w n ∧
      (signedRemainders (pathPolynomial w) (scalarNumerator R w) n /
        signedRemainders (pathPolynomial w) (scalarNumerator R w) (n + 1)).natDegree = 1) := by
  sorry

/-- Each corner-strip tree count equals its rectangle count times the signed-chain product. -/
theorem cornerStrip_product {R w k : ℕ} (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    (treeCount (cornerStrip (R + 1) (w + 1) k) : ℝ) =
      (treeCount (rectangle (R + 1) (w + 1)) : ℝ) *
        ∏ j ∈ Finset.range k, ((scalarCoefficient R w j : ℝ)⁻¹) ^ (2 * k - 2 * j - 1) := by
  sorry

/-- The rational recurrence gives the exact tree count after each allowed strip deletion. -/
theorem cornerStrip_recurrence {R w k : ℕ} (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    countRecurrence (treeCount (rectangle (R + 1) (w + 1)) : ℚ)
      (scalarCoefficient R w) k = (treeCount (cornerStrip (R + 1) (w + 1) k) : ℚ) := by
  sorry

/-- The intrinsic maximum has the displayed expansion with error O(N⁻¹ᐟ²). -/
theorem extremal_count_asymptotic :
    (fun N : ℕ => Real.log (maximumCount N : ℝ) - mainTerm N) =O[atTop]
      (fun N : ℕ => 1 / Real.sqrt (N : ℝ)) := by
  sorry

/-- The supremum of strip energies equals the exact critical Fourier expression. -/
theorem strip_fourier_identity :
    stripEnergyLimit = (entropy - alpha) / 2 -
      (1 / 2) * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * fourierCoefficient (n + 1) ^ 2 := by
  sorry

/-- The supremum of quadrant strip energies is strictly below 13/200. -/
theorem strip_energy_bound : stripEnergyLimit < (13 : ℝ) / 200 := by
  sorry

end
end SpanningTreeChallenge
