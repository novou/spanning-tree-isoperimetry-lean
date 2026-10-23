module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact local bounds from Appendix B

The finite grid has ordinary vertex degrees, with no exterior edges.  The
potential below is the integer potential printed in the manuscript.  All
finite assertions are checked by Lean's kernel using exact arithmetic.

This module does not identify the resulting matrix with a random spanning
tree's transfer-current kernel; that identification needs the electrical and
spanning-tree theorems elsewhere in the formalization.
-/

namespace SpanningTreeIsoperimetry.LocalBounds

open scoped BigOperators Matrix

abbrev Grid5 := Fin 5 × Fin 5

/-- Adjacency in the free nearest-neighbor grid on `{0, …, 4}²`. -/
def gridAdjacent (p q : Grid5) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

instance (p q : Grid5) : Decidable (gridAdjacent p q) :=
  inferInstanceAs (Decidable ((_ ∧ (_ ∨ _)) ∨ (_ ∧ (_ ∨ _))))

/-- The free-grid Laplacian, expressed as a sum over actual neighbors. -/
def gridLaplacian (f : Grid5 → ℤ) (p : Grid5) : ℤ :=
  ∑ q : Grid5, if gridAdjacent p q then f p - f q else 0

/-- Rows are indexed by `y` and columns by `x`.  The first and last rows agree,
so the table also agrees with the paper's descending order of row labels. -/
def eastPotential (p : Grid5) : ℤ :=
  (![![350, 322, 241, 72, 0],
      ![378, 375, 329, -25, -72],
      ![409, 471, 725, -429, -191],
      ![378, 375, 329, -25, -72],
      ![350, 322, 241, 72, 0]] : Matrix (Fin 5) (Fin 5) ℤ) p.2 p.1

def northPotential (p : Grid5) : ℤ := eastPotential (p.2, p.1)

def eastSource (p : Grid5) : ℤ :=
  (if p = (2, 2) then 1 else 0) - (if p = (3, 2) then 1 else 0)

def northSource (p : Grid5) : ℤ :=
  (if p = (2, 2) then 1 else 0) - (if p = (2, 3) then 1 else 0)

/-- All 25 equations `L₅ V_E = 2200 b_E`, checked exactly. -/
theorem eastPotential_laplacian :
    ∀ p : Grid5, gridLaplacian eastPotential p = 2200 * eastSource p := by
  decide

/-- The transposed potential solves the north-current equations. -/
theorem northPotential_laplacian :
    ∀ p : Grid5, gridLaplacian northPotential p = 2200 * northSource p := by
  decide

theorem eastPotential_grounded : eastPotential (4, 4) = 0 := by decide

theorem northPotential_grounded : northPotential (4, 4) = 0 := by decide

/-- Index `0` is the east edge and index `1` is the north edge. -/
def edgeHead : Fin 2 → Grid5 := ![(3, 2), (2, 3)]

def currentPotential (j : Fin 2) (p : Grid5) : ℚ :=
  ((![(eastPotential p : ℚ), (northPotential p : ℚ)] : Fin 2 → ℚ) j) / 2200

/-- Pairings of the two source vectors with the normalized potentials. -/
def currentMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => currentPotential j (2, 2) - currentPotential j (edgeHead i)

def localTransferMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![577 / 1100, 9 / 50; 9 / 50, 577 / 1100]

theorem currentMatrix_eq : currentMatrix = localTransferMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [currentMatrix, currentPotential, edgeHead, eastPotential,
      northPotential, localTransferMatrix]

theorem localTransferMatrix_det_complement :
    Matrix.det (1 - localTransferMatrix) = (9373 : ℚ) / 48400 := by
  norm_num [Matrix.det_fin_two, localTransferMatrix]

theorem localTransferMatrix_det_complement_gt :
    (3 : ℚ) / 16 < Matrix.det (1 - localTransferMatrix) := by
  rw [localTransferMatrix_det_complement]
  norm_num

/-- The probability factor preceding the exponential vacancy cost. -/
theorem vacancy_factor_lt_sixth : ((13 : ℚ) / 16) ^ 2 / 4 < 1 / 6 := by
  norm_num

/-- Four positive terms in the logarithm series at `v = 5/7`. -/
def logSixFourTerms : ℚ :=
  2 * ((5 / 7) + (5 / 7) ^ 3 / 3 + (5 / 7) ^ 5 / 5 + (5 / 7) ^ 7 / 7)

theorem logSixFourTerms_gt : (7 : ℚ) / 6 + 3 / 5 < logSixFourTerms := by
  norm_num [logSixFourTerms]

/-- The paper's four-term lower bound follows from the positive logarithm
series already formalized in mathlib. -/
theorem logSixFourTerms_le_log : (logSixFourTerms : ℝ) ≤ Real.log 6 := by
  have hs := Real.hasSum_log_one_add (a := (5 : ℝ)) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 4) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ, logSixFourTerms] at hb ⊢
  exact hb

theorem log_six_gt_strict_constants : (7 : ℝ) / 6 + 3 / 5 < Real.log 6 := by
  have hq : (7 : ℝ) / 6 + 3 / 5 < (logSixFourTerms : ℝ) := by
    norm_num [logSixFourTerms]
  exact hq.trans_le logSixFourTerms_le_log

/-- Once the separate enclosure `h < 7/6` is available, the improved vacancy
constant `3/5` follows from a fully justified logarithm bound. -/
theorem vacancy_cost_gt_three_fifths_of_entropy_lt (h : ℝ) (hh : h < 7 / 6) :
    (3 : ℝ) / 5 < Real.log 6 - h := by
  linarith [log_six_gt_strict_constants]

/-- A separate positive-series estimate for the paper's boundary constant
`α = log (1 + √2)`.  This does not assume a decimal enclosure for `α`. -/
theorem seven_eighths_lt_boundary_constant :
    (7 : ℝ) / 8 < Real.log (1 + Real.sqrt 2) := by
  have hs := Real.hasSum_log_one_add (a := (7 : ℝ) / 5) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 4) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have hlog : (7 : ℝ) / 8 < Real.log ((12 : ℝ) / 5) := by
    linarith
  have hsqrt : (7 : ℝ) / 5 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  exact hlog.trans (Real.log_lt_log (by norm_num) (by linarith))

/-- Positive terms of Catalan's alternating series. -/
noncomputable def catalanTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) + 1) ^ 2

theorem catalanTerm_summable : Summable catalanTerm := by
  change Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2)
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  simpa [Function.comp_def, catalanTerm, Nat.cast_add, Nat.cast_mul] using hs.comp_injective hinj

theorem catalanTerm_antitone : Antitone catalanTerm := by
  intro m n hmn
  dsimp [catalanTerm]
  gcongr

/-- Catalan's constant, using its usual convergent alternating series. -/
noncomputable def catalanConstant : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n * catalanTerm n

/-- The entropy constant is defined as in the manuscript. -/
noncomputable def entropyConstant : ℝ := 4 * catalanConstant / Real.pi

/-- Twenty-one alternating terms give a sufficient rational upper bound.
The alternating-series remainder is justified in Lean, not taken as an input. -/
theorem catalanConstant_lt : catalanConstant < (733 : ℝ) / 800 := by
  have hb := Antitone.tendsto_le_alternating_series
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 10
  change catalanConstant ≤ _ at hb
  norm_num [Finset.sum_range_succ, catalanTerm] at hb
  linarith

theorem entropyConstant_lt_seven_sixths : entropyConstant < (7 : ℝ) / 6 := by
  rw [entropyConstant, div_lt_iff₀ Real.pi_pos]
  nlinarith [catalanConstant_lt, Real.pi_gt_d6]

theorem vacancy_cost_gt_three_fifths :
    (3 : ℝ) / 5 < Real.log 6 - entropyConstant :=
  vacancy_cost_gt_three_fifths_of_entropy_lt entropyConstant entropyConstant_lt_seven_sixths

/-- The scalar conversion used after the graph inequalities in the interior
vacancy argument. The graph inequalities themselves are not assumptions of
this theorem and are not established here. -/
theorem vacancy_factor_with_entropy (k : ℝ) :
    ((13 : ℝ) / 16) ^ 2 / 4 * Real.exp (-entropyConstant * (k - 1)) <
      Real.exp (-entropyConstant * k - 3 / 5) := by
  have hlog : -Real.log 6 < -entropyConstant - (3 : ℝ) / 5 := by
    linarith [vacancy_cost_gt_three_fifths]
  have hexp : (1 : ℝ) / 6 < Real.exp (-entropyConstant - 3 / 5) := by
    calc
      (1 : ℝ) / 6 = Real.exp (-Real.log 6) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
        norm_num
      _ < _ := Real.exp_lt_exp.mpr hlog
  have hfactor : ((13 : ℝ) / 16) ^ 2 / 4 < Real.exp (-entropyConstant - 3 / 5) :=
    lt_trans (by norm_num) hexp
  calc
    ((13 : ℝ) / 16) ^ 2 / 4 * Real.exp (-entropyConstant * (k - 1)) <
        Real.exp (-entropyConstant - 3 / 5) * Real.exp (-entropyConstant * (k - 1)) :=
      mul_lt_mul_of_pos_right hfactor (Real.exp_pos _)
    _ = Real.exp (-entropyConstant * k - 3 / 5) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem strict_constants :
    2 * (entropyConstant - Real.log (1 + Real.sqrt 2)) < (3 : ℝ) / 5 ∧
      (3 : ℝ) / 5 < Real.log (1 + Real.sqrt 2) := by
  constructor <;>
    linarith [entropyConstant_lt_seven_sixths, seven_eighths_lt_boundary_constant]

/-- The rational gaps in the strict-constants chain in Appendix B. -/
theorem strict_constant_rational_chain :
    (7 : ℚ) / 12 < 3 / 5 ∧ (3 : ℚ) / 5 < 7 / 8 := by
  norm_num

/-- Arithmetic propagation of the separately stated enclosures for `h` and
`α`. This is a reusable implication, not a proof of those analytic enclosures. -/
theorem strict_constants_of_enclosures (h α : ℝ)
    (hh : h < 7 / 6) (hα : 7 / 8 < α) :
    2 * (h - α) < 7 / 12 ∧ (7 : ℝ) / 12 < 3 / 5 ∧
      (3 : ℝ) / 5 < 7 / 8 ∧ (7 : ℝ) / 8 < α := by
  constructor
  · linarith
  constructor
  · norm_num
  exact ⟨by norm_num, hα⟩

end SpanningTreeIsoperimetry.LocalBounds
