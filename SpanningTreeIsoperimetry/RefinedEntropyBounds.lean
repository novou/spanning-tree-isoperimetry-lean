import SpanningTreeIsoperimetry.CornerNumericBounds

/-! Exact entropy enclosures using bounded blocks of the actual alternating
Catalan series. Every rational block comparison is checked by Lean. -/
namespace SpanningTreeIsoperimetry.RefinedEntropyBounds
open LocalBounds
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def signedTerm (n : ℕ) : ℝ := (-1)^n*catalanTerm n
def catalanBlock (j : ℕ) : ℝ := ∑ i ∈ Finset.range 50, signedTerm (j*50+i)

def blockLower (j : Fin 16) : ℝ := ![915915609164,37485949,6943692,2430428,1124965,611098,368475,239155,163964,117283,86776,66000,51364,40755,32879,26909] j/1000000000000
def blockUpper (j : Fin 16) : ℝ := ![915915609165,37485950,6943693,2430429,1124966,611099,368476,239156,163965,117284,86777,66001,51365,40756,32880,26910] j/1000000000000

set_option maxHeartbeats 12000000 in
theorem catalanBlock_bounds (j : Fin 16) :
    blockLower j≤catalanBlock j.val ∧ catalanBlock j.val≤blockUpper j := by
  fin_cases j <;> norm_num [blockLower,blockUpper,catalanBlock,signedTerm,catalanTerm,Finset.sum_range_succ]

private theorem sum_blocks (f : ℕ → ℝ) (b n : ℕ) :
    (∑ i ∈ Finset.range (n*b),f i)=∑ j ∈ Finset.range n,∑ i ∈ Finset.range b,f (j*b+i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem catalan_upper : catalanConstant<(91596579 : ℝ)/100000000 := by
  have hb := Antitone.tendsto_le_alternating_series
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 400
  change catalanConstant≤∑ i ∈ Finset.range (800+1),signedTerm i at hb
  rw [Finset.sum_range_succ] at hb
  have hs : (∑ i ∈ Finset.range 800,signedTerm i)≤∑ j : Fin 16,blockUpper j := by
    rw [show 800=16*50 by norm_num,sum_blocks]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum (fun j _ => (catalanBlock_bounds j).2)
  have hn : (∑ j : Fin 16,blockUpper j)+signedTerm 800<(91596579 : ℝ)/100000000 := by
    norm_num [Fin.sum_univ_succ,blockUpper,signedTerm,catalanTerm]
  linarith

theorem catalan_lower : (91596509 : ℝ)/100000000<catalanConstant := by
  have hb := Antitone.alternating_series_le_tendsto
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 250
  change (∑ i ∈ Finset.range 500,signedTerm i)≤catalanConstant at hb
  have hs : (∑ j : Fin 10,blockLower (Fin.castLE (by decide : 10≤16) j))≤
      ∑ i ∈ Finset.range 500,signedTerm i := by
    rw [show 500=10*50 by norm_num,sum_blocks,← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum (fun j _ => (catalanBlock_bounds (Fin.castLE (by decide : 10≤16) j)).1)
  have hn : (91596509 : ℝ)/100000000<
      ∑ j : Fin 10,blockLower (Fin.castLE (by decide : 10≤16) j) := by
    norm_num [Fin.sum_univ_succ,blockLower]
  linarith

theorem entropy_upper : SquareMaximality.squareLatticeEntropy<(11662439 : ℝ)/10000000 := by
  rw [← entropy_eq_foundation,entropyConstant,div_lt_iff₀ Real.pi_pos]
  nlinarith [catalan_upper,Real.pi_gt_d20]

theorem entropy_lower : (11662429 : ℝ)/10000000<SquareMaximality.squareLatticeEntropy := by
  rw [← entropy_eq_foundation,entropyConstant,lt_div_iff₀ Real.pi_pos]
  nlinarith [catalan_lower,Real.pi_lt_d20]

end
end SpanningTreeIsoperimetry.RefinedEntropyBounds
