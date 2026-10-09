import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! A one-step Euler correction of the checked Catalan blocks.
No new long rational block expansion is needed. -/
namespace SpanningTreeIsoperimetry.CatalanEulerBounds
open LocalBounds RefinedEntropyBounds
open scoped BigOperators
noncomputable section

theorem alternating_difference_sum (a : ℕ → ℝ) (n : ℕ) :
    (∑ i∈Finset.range n,(-1 : ℝ)^i*(a i-a (i+1)))=
      2*(∑ i∈Finset.range n,(-1 : ℝ)^i*a i)-a 0+(-1 : ℝ)^n*a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,pow_succ]
    ring

theorem alternating_difference_hasSum {a : ℕ → ℝ} {S : ℝ}
    (hs : HasSum (fun n => (-1 : ℝ)^n*a n) S) :
    HasSum (fun n => (-1 : ℝ)^n*(a n-a (n+1))) (2*S-a 0) := by
  have hshift := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one,pow_zero,one_mul] at hshift
  have hnext : HasSum (fun n => (-1 : ℝ)^n*a (n+1)) (a 0-S) := by
    convert hshift.neg using 1
    · funext n
      simp only [pow_succ]
      ring
    · ring
  convert hs.sub hnext using 1
  · funext n
    ring
  · ring

/-- The first Euler average narrows the ordinary alternating tail to one
half of its first difference. -/
theorem euler_bounds {a : ℕ → ℝ} {S : ℝ}
    (hs : HasSum (fun n => (-1 : ℝ)^n*a n) S)
    (hm : Antitone (fun n => a n-a (n+1))) (n : ℕ) :
    (∑ i∈Finset.range (2*n),(-1 : ℝ)^i*a i)+a (2*n)/2≤S ∧
      S≤(∑ i∈Finset.range (2*n),(-1 : ℝ)^i*a i)+a (2*n)/2+
        (a (2*n)-a (2*n+1))/2 := by
  have hd := alternating_difference_hasSum hs
  have hl := Antitone.alternating_series_le_tendsto hd.tendsto_sum_nat hm n
  have hu := Antitone.tendsto_le_alternating_series hd.tendsto_sum_nat hm n
  rw [alternating_difference_sum] at hl
  rw [Finset.sum_range_succ,alternating_difference_sum] at hu
  have hpow : (-1 : ℝ)^(2*n)=1 := by simp
  rw [hpow] at hl hu
  simp only [one_mul] at hl hu
  constructor <;> linarith

def delta (n : ℕ) : ℝ := catalanTerm n-catalanTerm (n+1)

theorem delta_formula (n : ℕ) : delta n=
    2/((2*(n : ℝ)+1)^2*(2*n+3))+2/((2*(n : ℝ)+1)*(2*n+3)^2) := by
  unfold delta catalanTerm
  push_cast
  have h1 : (2*(n : ℝ)+1)≠0 := by positivity
  have h3 : (2*(n : ℝ)+3)≠0 := by positivity
  have hn : 2*((n : ℝ)+1)+1=2*(n : ℝ)+3 := by ring
  rw [hn]
  field_simp
  <;> ring

theorem delta_antitone : Antitone delta := by
  intro m n hmn
  rw [delta_formula,delta_formula]
  apply add_le_add
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr

theorem catalan_euler_bounds :
    (∑ i∈Finset.range 800,signedTerm i)+catalanTerm 800/2≤catalanConstant ∧
      catalanConstant≤(∑ i∈Finset.range 800,signedTerm i)+catalanTerm 800/2+delta 800/2 := by
  exact euler_bounds catalanTerm_summable.alternating.hasSum delta_antitone 400

private theorem sum_blocks (f : ℕ → ℝ) (b n : ℕ) :
    (∑ i∈Finset.range (n*b),f i)=∑ j∈Finset.range n,∑ i∈Finset.range b,f (j*b+i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem block_sum_bounds :
    (∑ j : Fin 16,blockLower j)≤(∑ i∈Finset.range 800,signedTerm i) ∧
      (∑ i∈Finset.range 800,signedTerm i)≤∑ j : Fin 16,blockUpper j := by
  rw [show 800=16*50 by norm_num,sum_blocks,← Fin.sum_univ_eq_sum_range]
  constructor
  · exact Finset.sum_le_sum (fun j _ => (catalanBlock_bounds j).1)
  · exact Finset.sum_le_sum (fun j _ => (catalanBlock_bounds j).2)

end
end SpanningTreeIsoperimetry.CatalanEulerBounds
