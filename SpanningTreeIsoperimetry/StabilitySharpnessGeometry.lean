import SpanningTreeIsoperimetry.Stability

/-! Exact-area rectangular witnesses and their optimal translational
asymmetry, including the minimization over every lattice translate. -/
namespace SpanningTreeIsoperimetry.StabilitySharpnessGeometry
open Filter
open scoped symmDiff Topology

theorem intersection_card_le (r s n : ℕ) (a : Vertex) :
    (rectangle r s ∩ translatedSquare n a).card≤r*n := by
  have hsub : rectangle r s ∩ translatedSquare n a ⊆
      Finset.Ico (0 : ℤ) r ×ˢ Finset.Ico a.2 (a.2+n) := by
    intro v hv
    obtain ⟨hr,hs⟩ := Finset.mem_inter.mp hv
    rw [mem_rectangle] at hr
    rw [mem_translatedSquare] at hs
    exact Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hr.1,hr.2.1⟩,
      Finset.mem_Ico.mpr ⟨hs.2.2.1,hs.2.2.2⟩⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_product,Int.card_Ico,sub_zero,add_sub_cancel_left,Int.toNat_natCast] using hc

theorem symmDiff_lower {r s n : ℕ} (harea : r*s=n^2) (a : Vertex) :
    2*(n^2-r*n)≤(rectangle r s ∆ translatedSquare n a).card := by
  have he : (rectangle r s).card=(translatedSquare n a).card := by simp [harea]
  have hi := intersection_card_le r s n a
  rw [card_symmDiff_of_card_eq he,Finset.card_sdiff,Finset.inter_comm,card_rectangle,harea]
  omega

theorem symmDiff_zero {r s n : ℕ} (hr : r≤n) (hs : n≤s) (harea : r*s=n^2) :
    (rectangle r s ∆ translatedSquare n (0,0)).card=2*(n^2-r*n) := by
  have he : (rectangle r s).card=(translatedSquare n (0,0)).card := by simp [harea,pow_two]
  rw [card_symmDiff_of_card_eq he,Finset.card_sdiff,translatedSquare_zero,
    rectangle_inter_rectangle,min_eq_right hr,min_eq_left hs,card_rectangle,card_rectangle,harea]

theorem minimum_symmDiff {r s n : ℕ} (hr : r≤n) (hs : n≤s) (harea : r*s=n^2) :
    sInf {k : ℕ | ∃ a : Vertex, k=(rectangle r s ∆ translatedSquare n a).card}=2*(n^2-r*n) := by
  let A := {k : ℕ | ∃ a : Vertex, k=(rectangle r s ∆ translatedSquare n a).card}
  have hA : A.Nonempty := ⟨(rectangle r s ∆ translatedSquare n (0,0)).card,⟨(0,0),rfl⟩⟩
  apply le_antisymm
  · calc
      sInf A≤(rectangle r s ∆ translatedSquare n (0,0)).card := Nat.sInf_le ⟨(0,0),rfl⟩
      _ = _ := symmDiff_zero hr hs harea
  · obtain ⟨a,ha⟩ := Nat.sInf_mem hA
    change 2*(n^2-r*n)≤sInf A
    rw [ha]
    exact symmDiff_lower harea a

theorem rectangle_asymmetry {r s n : ℕ} (hn : 0<n) (hr : r≤n) (hs : n≤s)
    (harea : r*s=n^2) : normalizedAsymmetry n (rectangle r s)=2*((n : ℝ)-r)/n := by
  have hrn : r*n≤n^2 := by simpa only [pow_two] using Nat.mul_le_mul_right n hr
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold normalizedAsymmetry
  change ((sInf {k : ℕ | ∃ a : Vertex,k=(rectangle r s ∆ translatedSquare n a).card} : ℕ) : ℝ)/
    (n : ℝ)^2=2*((n : ℝ)-r)/n
  rw [minimum_symmDiff hr hs harea]
  push_cast [Nat.cast_sub hrn]
  field_simp [hn0] <;> ring

def shortSide (a : ℕ) : ℕ := a^2
def longSide (a : ℕ) : ℕ := (a+1)^2
def squareSide (a : ℕ) : ℕ := a*(a+1)
def witness (a : ℕ) : Domain := rectangle (shortSide a) (longSide a)

theorem witness_area (a : ℕ) : shortSide a*longSide a=(squareSide a)^2 := by
  unfold shortSide longSide squareSide
  ring

theorem witness_perimeter (a : ℕ) : shortSide a+longSide a=2*squareSide a+1 := by
  unfold shortSide longSide squareSide
  ring

theorem witness_order (a : ℕ) : shortSide a≤squareSide a ∧ squareSide a≤longSide a := by
  unfold shortSide longSide squareSide
  constructor <;> nlinarith

theorem witness_card (a : ℕ) : (witness a).card=(squareSide a)^2 := by
  rw [witness,card_rectangle,witness_area]

theorem witness_connected {a : ℕ} (ha : 0<a) : (domainGraph (witness a)).Connected := by
  apply (treeCount_pos_iff_connected _).mp
  rw [witness,rectangle_treeCount_eq_foundation]
  exact SquareMaximality.tauRect_pos (by unfold shortSide; positivity) (by unfold longSide; positivity)

theorem witness_asymmetry {a : ℕ} (ha : 0<a) :
    normalizedAsymmetry (squareSide a) (witness a)=2/((a : ℝ)+1) := by
  rw [witness,rectangle_asymmetry (by unfold squareSide; positivity)
    (witness_order a).1 (witness_order a).2 (witness_area a)]
  unfold squareSide shortSide
  push_cast
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
  have ha1 : (a : ℝ)+1≠0 := by positivity
  field_simp [ha0,ha1]
  ring

theorem witness_weight (a : ℕ) :
    (squareSide a : ℝ)*normalizedAsymmetry (squareSide a) (witness a)^2=4*(a : ℝ)/(a+1) := by
  by_cases ha : a=0
  · simp [ha,squareSide]
  · rw [witness_asymmetry (Nat.pos_of_ne_zero ha)]
    unfold squareSide
    push_cast
    have ha1 : (a : ℝ)+1≠0 := by positivity
    field_simp [ha1]
    ring

theorem witness_aspect_le_three {a : ℕ} (ha : 2≤a) : longSide a≤3*shortSide a := by
  have hm : 2*a≤a^2 := by simpa only [pow_two] using Nat.mul_le_mul_right a ha
  unfold longSide shortSide
  nlinarith

end SpanningTreeIsoperimetry.StabilitySharpnessGeometry
