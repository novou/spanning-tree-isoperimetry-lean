module

public import SpanningTreeIsoperimetry.FiniteSectionPadding
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-! Existence of the determinant limit for an absolutely summable real
matrix kernel. This is only the finite-section continuity ingredient. -/
namespace SpanningTreeIsoperimetry.AbsolutelySummableDeterminant
open FiniteDeterminantContinuity FiniteSectionPadding Filter
open scoped Topology BigOperators
noncomputable section

def entryNorm (K : ℕ → ℕ → ℝ) (p : ℕ×ℕ) : ℝ := |K p.1 p.2|
def totalMass (K : ℕ → ℕ → ℝ) : ℝ := ∑' p,entryNorm K p

def tailEntry (K : ℕ → ℕ → ℝ) (n : ℕ) (p : ℕ×ℕ) : ℝ :=
  if n≤p.1 ∨ n≤p.2 then entryNorm K p else 0

def tailMass (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑' p,tailEntry K n p

theorem tailEntry_nonneg (K : ℕ → ℕ → ℝ) (n : ℕ) (p : ℕ×ℕ) : 0≤tailEntry K n p := by
  unfold tailEntry entryNorm
  split_ifs <;> positivity

theorem tailEntry_le (K : ℕ → ℕ → ℝ) (n : ℕ) (p : ℕ×ℕ) : tailEntry K n p≤entryNorm K p := by
  unfold tailEntry entryNorm
  split_ifs <;> simp [abs_nonneg]

theorem tailEntry_summable (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K)) (n : ℕ) :
    Summable (tailEntry K n) :=
  Summable.of_nonneg_of_le (tailEntry_nonneg K n) (tailEntry_le K n) hK

theorem tailMass_tendsto_zero (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K)) :
    Tendsto (tailMass K) atTop (𝓝 0) := by
  have ht := tendsto_tsum_of_dominated_convergence hK
    (f := tailEntry K) (g := fun _ : ℕ×ℕ => (0 : ℝ))
    (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (max p.1 p.2+1)] with n hn
      simp only [tailEntry,if_neg (show ¬(n≤p.1 ∨ n≤p.2) by omega)])
    (Filter.Eventually.of_forall (fun n p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (tailEntry_nonneg K n p)]
      exact tailEntry_le K n p))
  change Tendsto (fun n => ∑' p,tailEntry K n p) atTop (𝓝 0)
  simpa only [tsum_zero] using ht

theorem mass_pad_le (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K)) (N n : ℕ) :
    mass (pad K N n)≤totalMass K := by
  have hs := hK.sum_le_tsum (Finset.range N ×ˢ Finset.range N) (fun p _ => abs_nonneg (K p.1 p.2))
  rw [Finset.sum_product] at hs
  simp_rw [← Fin.sum_univ_eq_sum_range] at hs
  apply le_trans _ hs
  unfold mass rowMass pad
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  change |if i < n ∧ j < n then K i j else 0|≤|K i j|
  split_ifs <;> simp [abs_nonneg]

theorem mass_pad_difference_le (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K))
    {n m : ℕ} (hnm : n≤m) (N : ℕ) :
    mass (pad K N n-pad K N m)≤tailMass K n := by
  have hs := (tailEntry_summable K hK n).sum_le_tsum
    (Finset.range N ×ˢ Finset.range N) (fun p _ => tailEntry_nonneg K n p)
  rw [Finset.sum_product] at hs
  simp_rw [← Fin.sum_univ_eq_sum_range] at hs
  apply le_trans _ hs
  unfold mass rowMass
  simp only [Matrix.sub_apply]
  dsimp only [pad]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  change |(if i < n ∧ j < n then K i j else 0)-(if i < m ∧ j < m then K i j else 0)|≤tailEntry K n (i,j)
  by_cases hn : i < n ∧ j < n
  · have hm : i < m ∧ j < m := by omega
    have htail : ¬(n ≤ i ∨ n ≤ j) := by omega
    simp only [if_pos hn,if_pos hm,sub_self,abs_zero,tailEntry,htail,ite_false,le_refl]
  · have htail : n ≤ i ∨ n ≤ j := by omega
    rw [if_neg hn]
    unfold tailEntry entryNorm
    simp only [htail,ite_true,Prod.fst,Prod.snd]
    split_ifs <;> simp [abs_nonneg]

/-- An explicit tail bound, uniform in both finite-section dimensions. -/
theorem sections_difference_le_tail (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K))
    {n m : ℕ} (hnm : n≤m) :
    |(1+finiteSection K n).det-(1+finiteSection K m).det|≤
      tailMass K n*Real.exp (2*totalMass K) := by
  have hb := sections_difference_le K (N := m) hnm (le_refl m)
  have hd := mass_pad_difference_le K hK hnm m
  have hA := mass_pad_le K hK m n
  have hB := mass_pad_le K hK m m
  exact hb.trans (mul_le_mul hd (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_pos _).le (tsum_nonneg (tailEntry_nonneg K n)))

theorem sections_cauchy (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K)) :
    CauchySeq (fun n => (1+finiteSection K n).det) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => tailMass K n*Real.exp (2*totalMass K))
  · intro n m hnm
    simpa only [Real.dist_eq] using sections_difference_le_tail K hK hnm
  · simpa only [zero_mul] using (tailMass_tendsto_zero K hK).mul_const (Real.exp (2*totalMass K))

/-- Actual finite determinants converge for every entrywise absolutely
summable perturbation of the identity. No determinant value is assumed. -/
theorem exists_section_limit (K : ℕ → ℕ → ℝ) (hK : Summable (entryNorm K)) :
    ∃ d : ℝ,Tendsto (fun n => (1+finiteSection K n).det) atTop (𝓝 d) :=
  cauchySeq_tendsto_of_complete (sections_cauchy K hK)

end
end SpanningTreeIsoperimetry.AbsolutelySummableDeterminant
