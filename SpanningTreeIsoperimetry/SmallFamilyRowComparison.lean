module

public import SpanningTreeIsoperimetry.SmallFamilyRowTargets
public import SpanningTreeIsoperimetry.SmallFamilyCountComparison
public import SpanningTreeIsoperimetry.CanonicalStrips

@[expose] public section

/-! Every proved first-table source row gives a strict actual count
improvement, uniformly over all admissible hull sizes. -/
namespace SpanningTreeIsoperimetry.SmallFamilyRowComparison
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds SmallFamilyPatternData
  SmallFamilyRowData SmallFamilyRowTargets SmallFamilyCountComparison
  SmallFamilyProfiles CrossHullCountComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem row_bound_lt_canonical {N r a k : ℕ} (hN : 18≤N)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c)) (hcard : totalDefect M=k)
    (hsize : k<r) (harea : r*(r+a)=N+k) (hsum : r+(r+a)=minimumSideSum N)
    (hrow : RowBound r a k M) :
    treeCount (cornerPrimal (r-1) (r+a-1) M)<treeCount (canonicalDomain N) := by
  obtain ⟨i,⟨hi,ha,hk⟩,hsource⟩ := hrow
  let z : Fin 20 := ⟨i.val,hi⟩
  have hiz : index z=i := Fin.ext rfl
  have haz : rowGap z=a := by
    have hh := (gap_cast z).symm.trans (show gap (index z)=(a : ℝ) by simpa only [hiz] using ha)
    exact_mod_cast hh
  have hkz : rowDeficit (index z)=k := by simpa only [hiz] using hk
  have hrmin := minimum_side z hN (by simpa only [hkz] using hsize) (by simpa only [haz,hkz] using harea)
  have hf := target_fits z hrmin
  have htshort := target_short_deficit z hrmin
  have htarget := target_bound z hrmin (by omega : 2≤r-rowShift z)
    (by omega : rowTarget z≤r+rowGap z+rowShift z-1)
  have hrfit : totalDefect M≤r-1 := by omega
  have hsfit : totalDefect M≤r+a-1 := by omega
  have hsource' : MulticornerEndpointChecks.quadrantFloor (index z)+
      SmallFamilyMonotonicity.weightedLoss Finset.univ (coeff (index z)) shifts r≤
      finiteSourceEnergy M hM hrfit hsfit := by
    rw [← sourceEnergy_eq_finite hM hrfit hsfit]
    simpa only [hiz,rowLower] using hsource
  have hrel := target_relation z
  rw [hkz,haz] at hrel
  have hrshift : r=(r-rowShift z)+rowShift z := by omega
  have harea' : r*(r+a)+rowTarget z=
      (r-rowShift z)*(r+a+rowShift z)+totalDefect M := by
    rw [hcard,← hrel,hrshift]
    simp only [Nat.add_sub_cancel_right]
    ring
  have hpositive (q : Fin 20) : 0<rowShift q := by
    fin_cases q <;> norm_num [rowShift]
  have hstrict := count_lt_of_profile (R := r-rowShift z) (r := r) (s := r+a)
    (S := r+a+rowShift z) (a := a) (h := rowShift z) (j := rowTarget z)
    hf.1 (hpositive z) hrshift rfl rfl
    (by simpa only [haz] using hf.2.2.2) M hM hrfit hsfit
    (by simpa only [haz] using (show rowTarget z≤r+rowGap z+rowShift z-1 by omega))
    harea' (index z) (by simpa only [haz] using gap_cast z) (shift_cast z)
    (row_shift_zero z) (row_remainder_coefficient z hrmin) (cost_bound z hrmin)
    (by simpa only [haz] using htarget) hsource'
  have hcanon := CanonicalStrips.strip_le_canonical (by omega : 0<N)
    (show 1≤r-rowShift z by omega) (show r-rowShift z≤r+a+rowShift z by omega)
    htshort (show (r-rowShift z)*(r+a+rowShift z)=N+rowTarget z by omega)
    (show r-rowShift z+(r+a+rowShift z)=minimumSideSum N by omega)
  exact hstrict.trans_le hcanon

end
end SpanningTreeIsoperimetry.SmallFamilyRowComparison
