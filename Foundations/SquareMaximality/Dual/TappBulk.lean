module

public import SquareMaximality.Dual.TappBulkGeometry
public import SquareMaximality.Rectangle.Bulk

@[expose] public section

set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The Tapp bulk-product contradiction

The finite scan geometry is separated in `TappBulkGeometry`.  Here its
positive-density family of prefix multipliers is combined with the exact
prefix product and the square-grid entropy limit.
-/

namespace SquareMaximality
namespace Dual

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Uniform upper bound for every prefix multiplier of every finite square. -/
def SquarePrefixMultiplierUpperBound (B : ℝ) : Prop :=
  ∀ (n k : ℕ), k < Fintype.card (Fin n × Fin n) →
    wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k ≤ B

/-- Uniform upper bound along every translated copy of one fixed scan
current inside every containing finite square. -/
def SquareScanMultiplierUpperBound
    (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) (M : ℝ) : Prop :=
  ∀ (n : ℕ) (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y),
    wordsPrefixMultiplier (squareGrid n) (squareGridCoord n)
      (squareScanIndex z hx hy hX hY d) ≤ M

/-- The scan bound forces its proposed constant to be positive. -/
theorem one_le_of_squareScanMultiplierUpperBound
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hscan : SquareScanMultiplierUpperBound z X Y hx hy M) :
    1 ≤ M := by
  let n := X + Y
  have hX : X ≤ n := by simp [n]
  have hY : Y ≤ n := by simp [n]
  let d : SquareScanShift n X Y :=
    (⟨0, by simp [n]⟩, ⟨0, by simp [n]⟩)
  exact (wordsPrefixMultiplier_one_le (squareGrid n) (squareGridCoord n)
    (squareScanIndex z hx hy hX hY d)).trans
      (hscan n hX hY d)

/-- Finite marked-factor estimate behind the bulk contradiction. -/
theorem tauRect_le_scan_product
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hfour : SquarePrefixMultiplierUpperBound 4)
    (hscan : SquareScanMultiplierUpperBound z X Y hx hy M)
    {n : ℕ} (hX : X ≤ n) (hY : Y ≤ n) :
    (tauRect n n : ℝ) ≤
      M ^ ((n - X + 1) * (n - Y + 1)) *
        4 ^ (n * n - (n - X + 1) * (n - Y + 1)) := by
  let marked := squareScanIndices z hx hy hX hY
  let N := Fintype.card (Fin n × Fin n)
  have hmarked : marked ⊆ Finset.range N :=
    squareScanIndices_subset_range z hx hy hX hY
  have hM : 0 ≤ M := (one_le_of_squareScanMultiplierUpperBound z hx hy hscan).trans' zero_le_one
  have hfactor (k : ℕ) (hk : k ∈ Finset.range N) :
      wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k ≤
        if k ∈ marked then M else 4 := by
    split_ifs with hkm
    · rcases (mem_squareScanIndices_iff z hx hy hX hY k).mp hkm with ⟨d, rfl⟩
      exact hscan n hX hY d
    · exact hfour n k (Finset.mem_range.mp hk)
  have hprod :
      ∏ k ∈ Finset.range N,
          wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k ≤
        ∏ k ∈ Finset.range N, if k ∈ marked then M else 4 := by
    exact Finset.prod_le_prod₀
      (fun k _hk => (zero_le_one.trans
        (wordsPrefixMultiplier_one_le (squareGrid n) (squareGridCoord n) k)))
      hfactor
  have hn : 0 < n := by omega
  rw [product_squareGrid_prefixMultipliers hn] at hprod
  calc
    (tauRect n n : ℝ) ≤
        ∏ k ∈ Finset.range N, if k ∈ marked then M else 4 := hprod
    _ = M ^ marked.card * 4 ^ (N - marked.card) := by
      change (∏ k ∈ Finset.range N,
        (marked.piecewise (fun _ => M) (fun _ => 4)) k) = _
      rw [Finset.prod_piecewise]
      rw [Finset.inter_eq_right.mpr hmarked]
      simp only [Finset.prod_const]
      rw [Finset.card_sdiff_of_subset hmarked, Finset.card_range]
    _ = M ^ ((n - X + 1) * (n - Y + 1)) *
        4 ^ (n * n - (n - X + 1) * (n - Y + 1)) := by
      rw [show marked.card = (n - X + 1) * (n - Y + 1) from
        card_squareScanIndices z hx hy hX hY]
      simp [N]

/-- Logarithmic per-area form of the finite marked-factor estimate. -/
theorem log_tauRect_per_area_le_scan_mix
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hfour : SquarePrefixMultiplierUpperBound 4)
    (hscan : SquareScanMultiplierUpperBound z X Y hx hy M)
    {n : ℕ} (hX : X ≤ n) (hY : Y ≤ n) :
    Real.log (tauRect n n : ℝ) / ((n : ℝ) ^ 2) ≤
      (((n - X + 1) * (n - Y + 1) : ℕ) : ℝ) / ((n : ℝ) ^ 2) *
          Real.log M +
      (((n * n - (n - X + 1) * (n - Y + 1) : ℕ) : ℝ) /
          ((n : ℝ) ^ 2)) * Real.log 4 := by
  have hn : 0 < n := by omega
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one
    (one_le_of_squareScanMultiplierUpperBound z hx hy hscan)
  have htau : (0 : ℝ) < tauRect n n := by
    exact_mod_cast tauRect_pos hn hn
  have hfinite := tauRect_le_scan_product z hx hy hfour hscan hX hY
  have hlog := Real.log_le_log htau hfinite
  rw [Real.log_mul
      (pow_ne_zero _ hM.ne') (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)),
    Real.log_pow, Real.log_pow] at hlog
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  calc
    Real.log (tauRect n n : ℝ) / ((n : ℝ) ^ 2) ≤
        ((((n - X + 1) * (n - Y + 1) : ℕ) : ℝ) * Real.log M +
          ((n * n - (n - X + 1) * (n - Y + 1) : ℕ) : ℝ) *
            Real.log 4) / ((n : ℝ) ^ 2) :=
      (div_le_div_iff_of_pos_right hnSq).mpr hlog
    _ = (((n - X + 1) * (n - Y + 1) : ℕ) : ℝ) /
          ((n : ℝ) ^ 2) * Real.log M +
        (((n * n - (n - X + 1) * (n - Y + 1) : ℕ) : ℝ) /
          ((n : ℝ) ^ 2)) * Real.log 4 := by ring

/-! ## Reduction of the global factor-four bound to local finite facts -/

/-- Boundary steps (left edge or top edge of a square) have multiplier one.
This is the exact elementary boundary hook needed by the global constructor. -/
def SquareBoundaryPrefixMultiplierOne : Prop :=
  ∀ (n k : ℕ) (hk : k < Fintype.card (Fin n × Fin n)),
    let p := (wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩
    p.1.1 = 0 ∨ p.2.1 + 1 = n →
      wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k = 1

/-- At an interior step, the old-prefix resistance across the northwest
two-edge path is at most two.  Rayleigh monotonicity can discharge precisely
this finite hook. -/
def SquareCompleteStepResistanceUpperBound : Prop :=
  ∀ (n k : ℕ) (hk : k < Fintype.card (Fin n × Fin n)),
    let p := (wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩
    ∀ (hpx : 0 < p.1.1) (hpy : p.2.1 + 1 < n),
      let hsquare := squareGrid_containsUnitSquare p hpx hpy
      twoForestResistance (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)
        (unitSquareSWVertex hsquare) (unitSquareNECornerVertex hsquare) ≤ 2

/-- Boundary multiplier-one and the length-two resistance bound imply the
uniform factor-four estimate required by the bulk squeeze. -/
theorem squarePrefixMultiplierUpperBound_four_of_local
    (hboundary : SquareBoundaryPrefixMultiplierOne)
    (hcomplete : SquareCompleteStepResistanceUpperBound) :
    SquarePrefixMultiplierUpperBound 4 := by
  intro n k hk
  let p := (wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩
  by_cases hpx : 0 < p.1.1
  · by_cases hpy : p.2.1 + 1 < n
    · let hsquare := squareGrid_containsUnitSquare p hpx hpy
      have hcoord : squareGridCoord n
          ((wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩) =
          (p.1.1 - 1 + 1, p.2.1) := by
        change (p.1.1, p.2.1) = (p.1.1 - 1 + 1, p.2.1)
        congr 1
        omega
      have heq := wordsPrefixMultiplier_eq_two_add_twoForestResistance
        (squareGrid n) (squareGridCoord n) k hk (p.1.1 - 1, p.2.1)
        (squareGrid_le_faceLattice n) hsquare hcoord
      have hres := hcomplete n k hk hpx hpy
      rw [heq]
      linarith
    · have htop : p.2.1 + 1 = n := by omega
      rw [hboundary n k hk (Or.inr htop)]
      norm_num
  · have hleft : p.1.1 = 0 := Nat.eq_zero_of_not_pos hpx
    rw [hboundary n k hk (Or.inl hleft)]
    norm_num

/-- A cofinal square side chosen so that the fixed scan window fits for
every value of the free parameter. -/
private def bulkSide (X Y n : ℕ) : ℕ := n + (X + Y + 1)

private theorem bulkSide_pos (X Y n : ℕ) : 0 < bulkSide X Y n := by
  simp [bulkSide]

private theorem tendsto_bulkSide_cast (X Y : ℕ) :
    Tendsto (fun n : ℕ => (bulkSide X Y n : ℝ)) atTop atTop := by
  change Tendsto (Nat.cast ∘ bulkSide X Y) atTop atTop
  refine tendsto_natCast_atTop_atTop.comp ?_
  change Tendsto (fun n : ℕ => n + (X + Y + 1)) atTop atTop
  exact tendsto_add_atTop_nat (X + Y + 1)

/-- The translated scan currents occupy asymptotic density one in the
cofinal square family. -/
theorem tendsto_squareScan_density_one (X Y : ℕ) :
    Tendsto (fun n : ℕ =>
      (((bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
        ((bulkSide X Y n : ℝ) ^ 2)) atTop (𝓝 1) := by
  have hside := tendsto_bulkSide_cast X Y
  have hcorrX : Tendsto (fun n : ℕ =>
      ((1 : ℝ) - (X : ℝ)) / (bulkSide X Y n : ℝ)) atTop (𝓝 0) :=
    hside.const_div_atTop _
  have hcorrY : Tendsto (fun n : ℕ =>
      ((1 : ℝ) - (Y : ℝ)) / (bulkSide X Y n : ℝ)) atTop (𝓝 0) :=
    hside.const_div_atTop _
  have hratioX : Tendsto (fun n : ℕ =>
      ((bulkSide X Y n - X + 1 : ℕ) : ℝ) /
        (bulkSide X Y n : ℝ)) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := hconst.add hcorrX
    have heq : (fun n : ℕ =>
        ((bulkSide X Y n - X + 1 : ℕ) : ℝ) /
          (bulkSide X Y n : ℝ)) =
        fun n => (1 : ℝ) +
          ((1 : ℝ) - (X : ℝ)) / (bulkSide X Y n : ℝ) := by
      funext n
      have hX : X ≤ bulkSide X Y n := by unfold bulkSide; omega
      have hs : (bulkSide X Y n : ℝ) ≠ 0 := by
        exact_mod_cast (bulkSide_pos X Y n).ne'
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hX]
      field_simp
      ring
    rw [heq]
    simpa only [add_zero] using h
  have hratioY : Tendsto (fun n : ℕ =>
      ((bulkSide X Y n - Y + 1 : ℕ) : ℝ) /
        (bulkSide X Y n : ℝ)) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := hconst.add hcorrY
    have heq : (fun n : ℕ =>
        ((bulkSide X Y n - Y + 1 : ℕ) : ℝ) /
          (bulkSide X Y n : ℝ)) =
        fun n => (1 : ℝ) +
          ((1 : ℝ) - (Y : ℝ)) / (bulkSide X Y n : ℝ) := by
      funext n
      have hY : Y ≤ bulkSide X Y n := by unfold bulkSide; omega
      have hs : (bulkSide X Y n : ℝ) ≠ 0 := by
        exact_mod_cast (bulkSide_pos X Y n).ne'
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hY]
      field_simp
      ring
    rw [heq]
    simpa only [add_zero] using h
  have hprod := hratioX.mul hratioY
  have heq : (fun n : ℕ =>
      (((bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
        ((bulkSide X Y n : ℝ) ^ 2)) =
      fun n =>
        (((bulkSide X Y n - X + 1 : ℕ) : ℝ) /
          (bulkSide X Y n : ℝ)) *
        (((bulkSide X Y n - Y + 1 : ℕ) : ℝ) /
          (bulkSide X Y n : ℝ)) := by
    funext n
    norm_num only [Nat.cast_mul]
    ring
  rw [heq]
  simpa only [one_mul] using hprod

/-- The unmarked complement of the scan family has asymptotic density zero. -/
theorem tendsto_squareScan_complement_density_zero
    {X Y : ℕ} (hXpos : 0 < X) (hYpos : 0 < Y) :
    Tendsto
      (fun n : ℕ =>
        (((bulkSide X Y n * bulkSide X Y n -
            (bulkSide X Y n - X + 1) *
              (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2)))
      atTop (𝓝 0) := by
  have hdensity := tendsto_squareScan_density_one X Y
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hdiff := hconst.sub hdensity
  have heq :
      (fun n : ℕ =>
        (((bulkSide X Y n * bulkSide X Y n -
            (bulkSide X Y n - X + 1) *
              (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2))) =
      (fun n : ℕ => (1 : ℝ) -
        (((bulkSide X Y n - X + 1) *
            (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2)) := by
    funext n
    have hxle : bulkSide X Y n - X + 1 ≤ bulkSide X Y n := by
      unfold bulkSide
      omega
    have hyle : bulkSide X Y n - Y + 1 ≤ bulkSide X Y n := by
      unfold bulkSide
      omega
    have hprodle :
        (bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) ≤
          bulkSide X Y n * bulkSide X Y n := Nat.mul_le_mul hxle hyle
    rw [Nat.cast_sub hprodle]
    norm_num only [Nat.cast_mul]
    have hs : (bulkSide X Y n : ℝ) ≠ 0 := by
      exact_mod_cast (bulkSide_pos X Y n).ne'
    field_simp
  rw [heq]
  simpa only [sub_self] using hdiff

/-- The entropy-product contradiction: a density-one family of scan
multipliers bounded by `M`, with a fixed bound `4` on all remaining prefix
multipliers, forces the lattice entropy multiplier itself to be at most `M`.
Matrix--Tree is the only graph-theoretic input. -/
theorem exp_squareLatticeEntropy_le_of_scan_bounds
    (hMatrixTree : RectangleCofactorInput)
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hfour : SquarePrefixMultiplierUpperBound 4)
    (hscan : SquareScanMultiplierUpperBound z X Y hx hy M) :
    Real.exp squareLatticeEntropy ≤ M := by
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one
    (one_le_of_squareScanMultiplierUpperBound z hx hy hscan)
  have hleft : Tendsto (fun n : ℕ =>
      Real.log (tauRect (bulkSide X Y n) (bulkSide X Y n) : ℝ) /
        ((bulkSide X Y n : ℝ) ^ 2)) atTop (𝓝 squareLatticeEntropy) := by
    have hbulk := Rectangle.Bulk.tendsto_log_tauRect_square_per_area hMatrixTree
    have hshift := hbulk.comp (tendsto_add_atTop_nat (X + Y))
    have hsideEq (n : ℕ) : bulkSide X Y n = (n + (X + Y)) + 1 := by
      unfold bulkSide
      omega
    simp_rw [hsideEq]
    change Tendsto
      ((fun m : ℕ =>
        Real.log (tauRect (m + 1) (m + 1) : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2)) ∘
          fun n : ℕ => n + (X + Y)) atTop (𝓝 squareLatticeEntropy)
    exact hshift
  have hdensity := tendsto_squareScan_density_one X Y
  have hcomplement := tendsto_squareScan_complement_density_zero
    (by omega : 0 < X) (by omega : 0 < Y)
  have hright : Tendsto (fun n : ℕ =>
      (((bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2) * Real.log M +
      (((bulkSide X Y n * bulkSide X Y n -
          (bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2)) * Real.log 4)
        atTop (𝓝 (Real.log M)) := by
    have h := (hdensity.mul_const (Real.log M)).add
      (hcomplement.mul_const (Real.log 4))
    simpa only [one_mul, zero_mul, add_zero] using h
  have hineq (n : ℕ) :
      Real.log (tauRect (bulkSide X Y n) (bulkSide X Y n) : ℝ) /
          ((bulkSide X Y n : ℝ) ^ 2) ≤
        (((bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
            ((bulkSide X Y n : ℝ) ^ 2) * Real.log M +
        (((bulkSide X Y n * bulkSide X Y n -
            (bulkSide X Y n - X + 1) * (bulkSide X Y n - Y + 1) : ℕ) : ℝ) /
            ((bulkSide X Y n : ℝ) ^ 2)) * Real.log 4 := by
    exact log_tauRect_per_area_le_scan_mix z hx hy hfour hscan
      (by unfold bulkSide; omega) (by unfold bulkSide; omega)
  have hentropyLog : squareLatticeEntropy ≤ Real.log M :=
    le_of_tendsto_of_tendsto' hleft hright hineq
  calc
    Real.exp squareLatticeEntropy ≤ Real.exp (Real.log M) :=
      Real.exp_le_exp.mpr hentropyLog
    _ = M := Real.exp_log hM

/-- Local boundary and length-two resistance facts are sufficient for the
entropy-product conclusion. -/
theorem exp_squareLatticeEntropy_le_of_local_scan_bounds
    (hMatrixTree : RectangleCofactorInput)
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hboundary : SquareBoundaryPrefixMultiplierOne)
    (hcomplete : SquareCompleteStepResistanceUpperBound)
    (hscan : SquareScanMultiplierUpperBound z X Y hx hy M) :
    Real.exp squareLatticeEntropy ≤ M :=
  exp_squareLatticeEntropy_le_of_scan_bounds hMatrixTree z hx hy
    (squarePrefixMultiplierUpperBound_four_of_local hboundary hcomplete) hscan

/-- Contrapositive form: no uniform scan-current bound can lie strictly
below the entropy multiplier. -/
theorem not_squareScanMultiplierUpperBound_of_lt_exp_entropy
    (hMatrixTree : RectangleCofactorInput)
    (z : Boundary.LatticePoint) {X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) {M : ℝ}
    (hfour : SquarePrefixMultiplierUpperBound 4)
    (hM : M < Real.exp squareLatticeEntropy) :
    ¬SquareScanMultiplierUpperBound z X Y hx hy M := by
  intro hscan
  exact (not_le_of_gt hM)
    (exp_squareLatticeEntropy_le_of_scan_bounds
      hMatrixTree z hx hy hfour hscan)

end

end Dual
end SquareMaximality
