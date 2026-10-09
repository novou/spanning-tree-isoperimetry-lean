import SpanningTreeIsoperimetry.CornerEnergy
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.PSeries

/-!
# Finiteness of the critical corner-energy series

The count uses the two independent signs of the rotated coordinates `x+y`
and `x-y`. The finite encoding and the elementary central-binomial estimate
follow the same mathematical route as the author's public preliminary Lean
development (`ClosedWalk/Basic`, `Counts`, and `EntropySeries`), adapted here
to this project's concrete `Fin 4` words and energy definition.
-/

namespace SpanningTreeIsoperimetry.CornerEnergy

open scoped BigOperators ENNReal Topology
open Ferrers

def directionSignEquiv : Fin 4 ≃ Bool × Bool where
  toFun := ![(true, true), (false, false), (true, false), (false, true)]
  invFun
    | (true, true) => 0
    | (false, false) => 1
    | (true, false) => 2
    | (false, true) => 3
  left_inv d := by fin_cases d <;> rfl
  right_inv s := by rcases s with ⟨a, b⟩; cases a <;> cases b <;> rfl

def firstSignSet {ℓ : ℕ} (w : Word ℓ) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => (directionSignEquiv (w i)).1)

def secondSignSet {ℓ : ℕ} (w : Word ℓ) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => (directionSignEquiv (w i)).2)

@[simp] theorem mem_firstSignSet {ℓ : ℕ} {w : Word ℓ} {i : Fin ℓ} :
    i ∈ firstSignSet w ↔ (directionSignEquiv (w i)).1 := by simp [firstSignSet]

@[simp] theorem mem_secondSignSet {ℓ : ℕ} {w : Word ℓ} {i : Fin ℓ} :
    i ∈ secondSignSet w ↔ (directionSignEquiv (w i)).2 := by simp [secondSignSet]

def wordOfSignSets {ℓ : ℕ} (s : Finset (Fin ℓ) × Finset (Fin ℓ)) : Word ℓ :=
  fun i => directionSignEquiv.symm (decide (i ∈ s.1), decide (i ∈ s.2))

def wordSignSetsEquiv (ℓ : ℕ) : Word ℓ ≃ Finset (Fin ℓ) × Finset (Fin ℓ) where
  toFun w := (firstSignSet w, secondSignSet w)
  invFun := wordOfSignSets
  left_inv w := by
    funext i
    apply directionSignEquiv.injective
    simp [wordOfSignSets]
  right_inv s := by ext i <;> simp [wordOfSignSets]

def signValue : Bool → ℤ | true => 1 | false => -1

theorem sum_signValue_eq_card {ℓ : ℕ} (f : Fin ℓ → Bool) :
    (∑ i, signValue (f i)) =
      2 * ((Finset.univ.filter (fun i => f i)).card : ℤ) - ℓ := by
  rw [show (∑ i, signValue (f i)) = ∑ i, if f i then (1 : ℤ) else -1 by
    apply Finset.sum_congr rfl
    intro i _
    cases f i <;> rfl]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin ℓ))) (fun i => f i)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem position_length {ℓ : ℕ} (w : Word ℓ) : position w ℓ = ∑ i, direction (w i) := by
  simp [position]

theorem first_sign_sum_eq {ℓ : ℕ} (w : Word ℓ) :
    (∑ i, signValue (directionSignEquiv (w i)).1) =
      (position w ℓ).1 + (position w ℓ).2 := by
  have hd (d : Fin 4) : signValue (directionSignEquiv d).1 = (direction d).1 + (direction d).2 := by
    fin_cases d <;> rfl
  simp_rw [hd]
  rw [position_length, Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

theorem second_sign_sum_eq {ℓ : ℕ} (w : Word ℓ) :
    (∑ i, signValue (directionSignEquiv (w i)).2) =
      (position w ℓ).1 - (position w ℓ).2 := by
  have hd (d : Fin 4) : signValue (directionSignEquiv d).2 = (direction d).1 - (direction d).2 := by
    fin_cases d <;> rfl
  simp_rw [hd]
  rw [position_length, Prod.fst_sum, Prod.snd_sum, Finset.sum_sub_distrib]

theorem closed_iff_sign_card {ℓ : ℕ} (w : Word ℓ) :
    position w ℓ = (0, 0) ↔ 2 * (firstSignSet w).card = ℓ ∧ 2 * (secondSignSet w).card = ℓ := by
  have hfirst := sum_signValue_eq_card (fun i => (directionSignEquiv (w i)).1)
  have hsecond := sum_signValue_eq_card (fun i => (directionSignEquiv (w i)).2)
  rw [first_sign_sum_eq] at hfirst
  rw [second_sign_sum_eq] at hsecond
  change (position w ℓ).1 + (position w ℓ).2 = 2 * ((firstSignSet w).card : ℤ) - ℓ at hfirst
  change (position w ℓ).1 - (position w ℓ).2 = 2 * ((secondSignSet w).card : ℤ) - ℓ at hsecond
  constructor
  · intro hw
    rw [hw] at hfirst hsecond
    dsimp at hfirst hsecond
    constructor <;> omega
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext <;> dsimp <;> omega

def closedEvenEquiv (n : ℕ) : ClosedWord (2 * n) ≃
    {s : Finset (Fin (2 * n)) // s.card = n} × {s : Finset (Fin (2 * n)) // s.card = n} :=
  ((wordSignSetsEquiv (2 * n)).subtypeEquiv (fun w => by
    change position w (2 * n) = (0, 0) ↔
      (firstSignSet w).card = n ∧ (secondSignSet w).card = n
    rw [closed_iff_sign_card]
    omega)).trans Equiv.subtypeProdEquivProd

theorem closedWord_card_even (n : ℕ) : Fintype.card (ClosedWord (2 * n)) = (Nat.centralBinom n) ^ 2 := by
  rw [Fintype.card_congr (closedEvenEquiv n), Fintype.card_prod]
  simp only [Fintype.card_finset_len, Fintype.card_fin, Nat.centralBinom]
  ring

instance closedWord_odd_isEmpty (n : ℕ) : IsEmpty (ClosedWord (2 * n + 1)) := ⟨by
  intro w
  have h := (closed_iff_sign_card w.val).mp w.property
  omega⟩

@[simp] theorem closedWord_card_odd (n : ℕ) : Fintype.card (ClosedWord (2 * n + 1)) = 0 := by
  simp

noncomputable def normalizedCentralBinom (n : ℕ) : ℝ := Nat.centralBinom n / (4 : ℝ) ^ n

theorem normalizedCentralBinom_succ (n : ℕ) :
    normalizedCentralBinom (n + 1) =
      ((2 * n + 1 : ℝ) / (2 * (n + 1))) * normalizedCentralBinom n := by
  have hrec : (n + 1 : ℝ) * Nat.centralBinom (n + 1) =
      (2 * (2 * n + 1) : ℝ) * Nat.centralBinom n := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold normalizedCentralBinom
  rw [pow_succ]
  field_simp
  nlinarith

theorem normalizedCentralBinom_sq_le (n : ℕ) :
    normalizedCentralBinom n ^ 2 ≤ 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => norm_num [normalizedCentralBinom]
  | succ n ih =>
    rw [normalizedCentralBinom_succ]
    have hn : (0 : ℝ) ≤ n := by positivity
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    calc
      (((2 * n + 1 : ℝ) / (2 * (n + 1))) * normalizedCentralBinom n) ^ 2 ≤
          ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 * (1 / (n + 1 : ℝ)) := by
        rw [mul_pow]
        gcongr
      _ ≤ 1 / (n + 2 : ℝ) := by
        field_simp
        nlinarith [sq_nonneg (n : ℝ)]
      _ = 1 / ((n + 1 : ℕ) + 1 : ℝ) := by push_cast; ring

/-- Closed-word mass at positive length, before inserting the defect count. -/
noncomputable def closedWordTerm (n : ℕ) : ℝ :=
  Fintype.card (ClosedWord (n + 1)) / ((n + 1 : ℝ) * 4 ^ (n + 1))

@[simp] theorem closedWordTerm_even (n : ℕ) : closedWordTerm (2 * n) = 0 := by
  simp [closedWordTerm]

theorem closedWordTerm_odd (n : ℕ) :
    closedWordTerm (2 * n + 1) = normalizedCentralBinom (n + 1) ^ 2 / (2 * (n + 1 : ℝ)) := by
  unfold closedWordTerm normalizedCentralBinom
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, closedWord_card_even]
  have hpow : (4 : ℝ) ^ (2 * (n + 1)) = ((4 : ℝ) ^ (n + 1)) ^ 2 := by
    rw [show 2 * (n + 1) = (n + 1) * 2 by omega, pow_mul]
  push_cast
  rw [hpow]
  field_simp
  ring

theorem closedWordTerm_nonneg (n : ℕ) : 0 ≤ closedWordTerm n := by
  unfold closedWordTerm
  positivity

theorem closedWordTerm_odd_le (n : ℕ) : closedWordTerm (2 * n + 1) ≤ 1 / (n + 1 : ℝ) ^ 2 := by
  rw [closedWordTerm_odd]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  calc
    normalizedCentralBinom (n + 1) ^ 2 / (2 * (n + 1 : ℝ)) ≤
        (1 / (n + 2 : ℝ)) / (2 * (n + 1 : ℝ)) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        normalizedCentralBinom_sq_le (n + 1)
    _ ≤ 1 / (n + 1 : ℝ) ^ 2 := by
      field_simp
      nlinarith

theorem closedWordTerm_summable : Summable closedWordTerm := by
  apply Summable.even_add_odd
  · simp
  · have hp : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
      have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
    exact Summable.of_nonneg_of_le (fun n => closedWordTerm_nonneg (2 * n + 1))
      closedWordTerm_odd_le hp

theorem defectSum_le_card_mul_closedWord (M : Diagram) (ℓ : ℕ) :
    defectSum M ℓ ≤ M.card * Fintype.card (ClosedWord ℓ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
    (fun w _ => defectCount_le_card M (normalizedVisited w.val))
  simpa [defectSum, mul_comm] using h

noncomputable def realEnergyTerm (M : Diagram) (n : ℕ) : ℝ :=
  (defectSum M (n + 1) : ℝ) / ((n + 1 : ℝ) * 4 ^ (n + 1))

theorem realEnergyTerm_nonneg (M : Diagram) (n : ℕ) : 0 ≤ realEnergyTerm M n := by
  unfold realEnergyTerm
  positivity

theorem realEnergyTerm_le_closedWordTerm (M : Diagram) (n : ℕ) :
    realEnergyTerm M n ≤ (M.card : ℝ) * closedWordTerm n := by
  unfold realEnergyTerm closedWordTerm
  rw [← mul_div_assoc]
  gcongr
  exact_mod_cast defectSum_le_card_mul_closedWord M (n + 1)

theorem realEnergyTerm_summable (M : Diagram) : Summable (realEnergyTerm M) :=
  Summable.of_nonneg_of_le (realEnergyTerm_nonneg M) (realEnergyTerm_le_closedWordTerm M)
    (closedWordTerm_summable.mul_left (M.card : ℝ))

theorem toReal_energyTerm (M : Diagram) (n : ℕ) : (energyTerm M n).toReal = realEnergyTerm M n := by
  simp [energyTerm, energyWeight, realEnergyTerm, ENNReal.toReal_add, div_eq_mul_inv, mul_comm]

theorem energyTerm_eq_ofReal (M : Diagram) (n : ℕ) :
    energyTerm M n = ENNReal.ofReal (realEnergyTerm M n) := by
  rw [← toReal_energyTerm]
  exact (ENNReal.ofReal_toReal (energyTerm_ne_top M n)).symm

/-- The critical corner-energy series is finite for every finite diagram. -/
theorem energy_ne_top (M : Diagram) : energy M ≠ ⊤ := by
  unfold energy
  simp_rw [energyTerm_eq_ofReal]
  exact (realEnergyTerm_summable M).tsum_ofReal_ne_top

/-- The real corner energy is defined only after finiteness of its concrete
nonnegative closed-word series has been proved. -/
noncomputable def realEnergy (M : Diagram) : ℝ := (energy M).toReal

theorem realEnergy_eq_tsum (M : Diagram) : realEnergy M = ∑' n, realEnergyTerm M n := by
  rw [realEnergy, energy, ENNReal.tsum_toReal_eq (fun n => energyTerm_ne_top M n)]
  simp_rw [toReal_energyTerm]

theorem realEnergy_hasSum (M : Diagram) : HasSum (realEnergyTerm M) (realEnergy M) := by
  rw [realEnergy_eq_tsum]
  exact (realEnergyTerm_summable M).hasSum

theorem partialRealEnergy_tendsto (M : Diagram) :
    Filter.Tendsto (partialRealEnergy M) Filter.atTop (𝓝 (realEnergy M)) := by
  convert (realEnergy_hasSum M).tendsto_sum_nat using 1
  funext L
  exact partialRealEnergy_eq M L

@[simp] theorem ofReal_realEnergy (M : Diagram) : ENNReal.ofReal (realEnergy M) = energy M :=
  ENNReal.ofReal_toReal (energy_ne_top M)

theorem realEnergy_nonneg (M : Diagram) : 0 ≤ realEnergy M := ENNReal.toReal_nonneg

@[simp] theorem realEnergy_empty : realEnergy ∅ = 0 := by simp [realEnergy]

@[simp] theorem realEnergy_strip_zero : realEnergy (horizontalStrip 0) = 0 := by simp [realEnergy]

theorem realEnergy_duplicateRow {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    realEnergy M ≤ realEnergy (duplicateRow M j) :=
  ENNReal.toReal_mono (energy_ne_top _) (energy_duplicateRow hM j)

theorem realEnergy_duplicateColumn {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    realEnergy M ≤ realEnergy (duplicateColumn M j) :=
  ENNReal.toReal_mono (energy_ne_top _) (energy_duplicateColumn hM j)

theorem realEnergy_maximalCells (M : Diagram) :
    (maximalCells M).card * realEnergy {(0, 0)} ≤ realEnergy M := by
  have h := ENNReal.toReal_mono (energy_ne_top M) (energy_maximalCells M)
  simpa only [realEnergy, ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

theorem realEnergy_threeCell {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) :
    realEnergy threeCell + ((maximalCells M).card - 2 : ℕ) * realEnergy {(0, 0)} ≤ realEnergy M := by
  have h := ENNReal.toReal_mono (energy_ne_top M) (energy_threeCell hM hne hrect)
  have hprod : (↑((maximalCells M).card - 2) : ℝ≥0∞) * energy {(0, 0)} ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (energy_ne_top _)
  rw [ENNReal.toReal_add (energy_ne_top _) hprod] at h
  simpa only [realEnergy, ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

theorem realEnergy_strip_monotone : Monotone (fun k => realEnergy (horizontalStrip k)) := by
  intro j k hjk
  exact ENNReal.toReal_mono (energy_ne_top _) (energy_strip_monotone hjk)

theorem realEnergy_strip_concave (k : ℕ) :
    realEnergy (horizontalStrip (k + 2)) + realEnergy (horizontalStrip k) ≤
      2 * realEnergy (horizontalStrip (k + 1)) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (energy_ne_top _)) (energy_strip_concave k)
  rw [ENNReal.toReal_add (energy_ne_top _) (energy_ne_top _)] at h
  simpa [realEnergy, ENNReal.toReal_mul] using h

theorem realEnergy_strip_concentration {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * realEnergy (horizontalStrip 1) + realEnergy (horizontalStrip (a + b)) ≤
      realEnergy (horizontalStrip a) + realEnergy (horizontalStrip b) + realEnergy (horizontalStrip 2) := by
  have h := ENNReal.toReal_mono
    (by simp [energy_ne_top]) (energy_strip_concentration ha hb)
  have htwice : (2 : ℝ≥0∞) * energy (horizontalStrip 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (energy_ne_top _)
  rw [ENNReal.toReal_add htwice (energy_ne_top _)] at h
  simpa [realEnergy, ENNReal.toReal_mul, ENNReal.toReal_add, energy_ne_top,
    ENNReal.add_ne_top] using h

theorem realEnergy_strip_concentration_gap {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * realEnergy (horizontalStrip 1) - realEnergy (horizontalStrip 2) ≤
      realEnergy (horizontalStrip a) + realEnergy (horizontalStrip b) -
        realEnergy (horizontalStrip (a + b)) := by
  linarith [realEnergy_strip_concentration ha hb]

end SpanningTreeIsoperimetry.CornerEnergy
