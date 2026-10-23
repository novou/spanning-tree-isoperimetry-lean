module

public import SpanningTreeIsoperimetry.EnergyConvergence

@[expose] public section

/-!
# Explicit closed-word witnesses for strict strip inequalities

The word travels east `j` steps, south once, north once, and west `j` steps.
After normalization, its only point on the horizontal axis is `(j,0)`.
Its strictly positive series weight supplies strictness in the real energy.
The construction and proofs in this module are written for the present
concrete word and energy definitions.
-/

namespace SpanningTreeIsoperimetry.CornerEnergy

open scoped BigOperators
open Ferrers

def stripWitnessWord (j : ℕ) : Word (2 * j + 2) := fun i =>
  if i.val < j then 0 else if i.val = j then 3 else if i.val = j + 1 then 2 else 1

def stripWitnessPosition (j i : ℕ) : Vertex :=
  if i ≤ j then (i, 0) else if i = j + 1 then (j, -1) else ((2 * j + 2 : ℤ) - i, 0)

theorem stripWitnessPosition_succ (j i : ℕ) (hi : i < 2 * j + 2) :
    stripWitnessPosition j (i + 1) =
      stripWitnessPosition j i + direction (stripWitnessWord j ⟨i, hi⟩) := by
  by_cases hij : i < j
  · have hle : i ≤ j := by omega
    have hle' : i + 1 ≤ j := by omega
    simp [stripWitnessPosition, stripWitnessWord, hij, hle, hle', direction,
      Nat.cast_add, Prod.mk_add_mk]
  · by_cases heq : i = j
    · subst i
      simp [stripWitnessPosition, stripWitnessWord, direction, Prod.mk_add_mk]
    · by_cases heq' : i = j + 1
      · subst i
        simp [stripWitnessPosition, stripWitnessWord, direction, Prod.mk_add_mk]
        omega
      · have hi₀ : ¬i ≤ j := by omega
        have hi₁ : ¬i + 1 ≤ j := by omega
        have hi₂ : i + 1 ≠ j + 1 := by omega
        simp [stripWitnessPosition, stripWitnessWord, direction, hij, heq, heq',
          hi₀, hi₁, Prod.mk_add_mk]
        ring

theorem stripWitness_position (j i : ℕ) (hi : i ≤ 2 * j + 2) :
    position (stripWitnessWord j) i = stripWitnessPosition j i := by
  induction i with
  | zero => simp [stripWitnessPosition]; rfl
  | succ i ih =>
    rw [position_succ _ (by omega), ih (by omega)]
    exact (stripWitnessPosition_succ j i (by omega)).symm

theorem stripWitness_closed (j : ℕ) : position (stripWitnessWord j) (2 * j + 2) = (0, 0) := by
  rw [stripWitness_position j (2 * j + 2) le_rfl]
  simp [stripWitnessPosition, show ¬2 * j + 2 ≤ j by omega,
    show 2 * j + 2 ≠ j + 1 by omega]

def stripWitness (j : ℕ) : ClosedWord (2 * j + 2) := ⟨stripWitnessWord j, stripWitness_closed j⟩

theorem stripWitness_bottom (j : ℕ) : position (stripWitnessWord j) (j + 1) = ((j : ℤ), -1) := by
  rw [stripWitness_position j (j + 1) (by omega)]
  simp [stripWitnessPosition]

theorem stripWitness_visit_bounds {j : ℕ} {p : Vertex} (hp : p ∈ visited (stripWitnessWord j)) :
    0 ≤ p.1 ∧ -1 ≤ p.2 ∧ (p.2 = -1 → p.1 = j) := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  have hib : i ≤ 2 * j + 2 := by have := Finset.mem_range.mp hi; omega
  rw [stripWitness_position j i hib]
  unfold stripWitnessPosition
  split_ifs <;> simp
  all_goals omega

theorem stripWitness_minimumX (j : ℕ) :
    minimumX (visited (stripWitnessWord j)) (visited_nonempty _) = 0 := by
  apply le_antisymm
  · have hzero : (0 : Vertex) ∈ visited (stripWitnessWord j) := by
      exact Finset.mem_image.mpr ⟨0, by simp, position_zero _⟩
    exact minimumX_le _ hzero
  · apply Finset.le_min'
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (stripWitness_visit_bounds hp).1

theorem stripWitness_minimumY (j : ℕ) :
    minimumY (visited (stripWitnessWord j)) (visited_nonempty _) = -1 := by
  apply le_antisymm
  · have hbottom : ((j : ℤ), -1) ∈ visited (stripWitnessWord j) := by
      refine Finset.mem_image.mpr ⟨j + 1, ?_, stripWitness_bottom j⟩
      simp only [Finset.mem_range]
      omega
    exact minimumY_le _ hbottom
  · apply Finset.le_min'
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact (stripWitness_visit_bounds hp).2.1

theorem stripWitness_axis_mem (j : ℕ) : (j, 0) ∈ normalizedVisited (stripWitnessWord j) := by
  have hbottom : ((j : ℤ), -1) ∈ visited (stripWitnessWord j) := by
    refine Finset.mem_image.mpr ⟨j + 1, ?_, stripWitness_bottom j⟩
    simp only [Finset.mem_range]
    omega
  refine Finset.mem_image.mpr ⟨((j : ℤ), -1), hbottom, ?_⟩
  simp [normalizePoint, stripWitness_minimumX, stripWitness_minimumY]

theorem stripWitness_axis_unique {j : ℕ} {p : Point}
    (hp : p ∈ normalizedVisited (stripWitnessWord j)) (hy : p.2 = 0) : p.1 = j := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have hc := normalizePoint_cast (visited_nonempty (stripWitnessWord j)) hq
  rw [stripWitness_minimumX, stripWitness_minimumY] at hc
  have hqy : q.2 = -1 := by rw [hy] at hc; norm_num at hc; omega
  have hqx := (stripWitness_visit_bounds hq).2.2 hqy
  simp [normalizePoint, stripWitness_minimumX, hqx]

theorem stripWitness_defect (j k : ℕ) :
    defectCount (horizontalStrip k) (normalizedVisited (stripWitnessWord j)) = min k j :=
  defectCount_horizontalStrip (stripWitness_axis_mem j)
    (fun _ hp hy => (stripWitness_axis_unique hp hy).ge) k

theorem defectSum_strip_strict_increase (k : ℕ) :
    defectSum (horizontalStrip k) (2 * (k + 1) + 2) <
      defectSum (horizontalStrip (k + 1)) (2 * (k + 1) + 2) := by
  unfold defectSum
  apply Finset.sum_lt_sum
  · intro w _
    exact strip_defect_monotone (normalizedVisited_isNormalized w.val) (by omega)
  · refine ⟨stripWitness (k + 1), Finset.mem_univ _, ?_⟩
    change defectCount (horizontalStrip k) (normalizedVisited (stripWitnessWord (k + 1))) <
      defectCount (horizontalStrip (k + 1)) (normalizedVisited (stripWitnessWord (k + 1)))
    rw [stripWitness_defect, stripWitness_defect]
    omega

theorem defectSum_strip_strict_concave (k : ℕ) :
    defectSum (horizontalStrip (k + 2)) (2 * (k + 1) + 2) +
      defectSum (horizontalStrip k) (2 * (k + 1) + 2) <
        2 * defectSum (horizontalStrip (k + 1)) (2 * (k + 1) + 2) := by
  have h :
      (∑ w : ClosedWord (2 * (k + 1) + 2),
        (defectCount (horizontalStrip (k + 2)) (normalizedVisited w.val) +
          defectCount (horizontalStrip k) (normalizedVisited w.val))) <
      ∑ w : ClosedWord (2 * (k + 1) + 2),
        2 * defectCount (horizontalStrip (k + 1)) (normalizedVisited w.val) := by
    apply Finset.sum_lt_sum
    · intro w _
      exact strip_defect_concave (normalizedVisited_isNormalized w.val) k
    · refine ⟨stripWitness (k + 1), Finset.mem_univ _, ?_⟩
      change defectCount (horizontalStrip (k + 2)) (normalizedVisited (stripWitnessWord (k + 1))) +
          defectCount (horizontalStrip k) (normalizedVisited (stripWitnessWord (k + 1))) <
        2 * defectCount (horizontalStrip (k + 1)) (normalizedVisited (stripWitnessWord (k + 1)))
      rw [stripWitness_defect, stripWitness_defect, stripWitness_defect]
      omega
  simpa only [defectSum, Finset.sum_add_distrib, Finset.mul_sum] using h

theorem realEnergyTerm_strip_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    realEnergyTerm (horizontalStrip j) n ≤ realEnergyTerm (horizontalStrip k) n := by
  unfold realEnergyTerm
  gcongr
  exact_mod_cast defectSum_strip_monotone (n + 1) hjk

theorem realEnergyTerm_strip_strict_increase (k : ℕ) :
    realEnergyTerm (horizontalStrip k) (2 * (k + 1) + 1) <
      realEnergyTerm (horizontalStrip (k + 1)) (2 * (k + 1) + 1) := by
  unfold realEnergyTerm
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast defectSum_strip_strict_increase k

theorem realEnergy_strip_strict_increase (k : ℕ) :
    realEnergy (horizontalStrip k) < realEnergy (horizontalStrip (k + 1)) := by
  rw [realEnergy_eq_tsum, realEnergy_eq_tsum]
  exact Summable.tsum_lt_tsum (fun n => realEnergyTerm_strip_mono (by omega) n)
    (realEnergyTerm_strip_strict_increase k) (realEnergyTerm_summable _)
      (realEnergyTerm_summable _)

theorem realEnergy_strip_strictMono : StrictMono (fun k => realEnergy (horizontalStrip k)) :=
  strictMono_nat_of_lt_succ realEnergy_strip_strict_increase

theorem realEnergyTerm_strip_concave (k n : ℕ) :
    realEnergyTerm (horizontalStrip (k + 2)) n + realEnergyTerm (horizontalStrip k) n ≤
      2 * realEnergyTerm (horizontalStrip (k + 1)) n := by
  unfold realEnergyTerm
  rw [← add_div, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast defectSum_strip_concave k (n + 1)

theorem realEnergyTerm_strip_strict_concave (k : ℕ) :
    realEnergyTerm (horizontalStrip (k + 2)) (2 * (k + 1) + 1) +
      realEnergyTerm (horizontalStrip k) (2 * (k + 1) + 1) <
        2 * realEnergyTerm (horizontalStrip (k + 1)) (2 * (k + 1) + 1) := by
  unfold realEnergyTerm
  rw [← add_div, ← mul_div_assoc]
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast defectSum_strip_strict_concave k

/-- The strict discrete concavity asserted in Section 4.3. Each strict
inequality is witnessed by the explicit word of length `2(k+1)+2`. -/
theorem realEnergy_strip_strict_concave (k : ℕ) :
    realEnergy (horizontalStrip (k + 2)) + realEnergy (horizontalStrip k) <
      2 * realEnergy (horizontalStrip (k + 1)) := by
  have hsA := realEnergyTerm_summable (horizontalStrip (k + 2))
  have hsB := realEnergyTerm_summable (horizontalStrip k)
  have hsC := realEnergyTerm_summable (horizontalStrip (k + 1))
  have h := Summable.tsum_lt_tsum (fun n => realEnergyTerm_strip_concave k n)
    (realEnergyTerm_strip_strict_concave k) (hsA.add hsB) (hsC.mul_left 2)
  rw [hsA.tsum_add hsB, tsum_mul_left] at h
  simpa only [← realEnergy_eq_tsum] using h

/-- The four-step witness at `j=1` makes the fixed concentration gap positive. -/
theorem realEnergy_strip_gap_pos :
    0 < 2 * realEnergy (horizontalStrip 1) - realEnergy (horizontalStrip 2) := by
  have h := realEnergy_strip_strict_concave 0
  simp only [zero_add, realEnergy_strip_zero, add_zero] at h
  linarith

theorem realEnergy_strip_concentration_strict {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    realEnergy (horizontalStrip (a + b)) <
      realEnergy (horizontalStrip a) + realEnergy (horizontalStrip b) := by
  have hgap := realEnergy_strip_concentration_gap ha hb
  linarith [realEnergy_strip_gap_pos]

end SpanningTreeIsoperimetry.CornerEnergy
