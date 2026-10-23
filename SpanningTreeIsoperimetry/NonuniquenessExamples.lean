module

public import SpanningTreeIsoperimetry.SmallMaximizers

@[expose] public section

/-! Actual noncongruent maximizing pairs at 3, 8, 10 and 13 vertices.
Separation uses the lattice-isometry invariant maximum coordinate distance. -/
namespace SpanningTreeIsoperimetry.NonuniquenessExamples
open CornerPrimalDomains StripTreeComparisons
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def coordinateDistance (p q : Vertex) : ℤ := max |p.1-q.1| |p.2-q.2|

theorem coordinateDistance_rigid (a p q : Vertex) (sw : Bool) (sx sy : ℤ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) :
    coordinateDistance (rigidMotion a sw sx sy p) (rigidMotion a sw sx sy q)=coordinateDistance p q := by
  cases sw <;> rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
    simp [coordinateDistance,rigidMotion,neg_add_eq_sub,abs_sub_comm,max_comm]

theorem not_congruent_of_distance {A B : Domain} {p q : Vertex} {d : ℕ}
    (hp : p∈A) (hq : q∈A) (hB : B⊆rectangle d d) (hd : (d : ℤ)≤coordinateDistance p q) :
    ¬Congruent A B := by
  rintro ⟨a,sw,sx,sy,hx,hy,he⟩
  have hpB : rigidMotion a sw sx sy p∈B := he ▸ Finset.mem_image_of_mem _ hp
  have hqB : rigidMotion a sw sx sy q∈B := he ▸ Finset.mem_image_of_mem _ hq
  have hb1 := mem_rectangle.mp (hB hpB)
  have hb2 := mem_rectangle.mp (hB hqB)
  have hdx : |(rigidMotion a sw sx sy p).1-(rigidMotion a sw sx sy q).1|<(d : ℤ) :=
    abs_lt.mpr ⟨by omega,by omega⟩
  have hdy : |(rigidMotion a sw sx sy p).2-(rigidMotion a sw sx sy q).2|<(d : ℤ) :=
    abs_lt.mpr ⟨by omega,by omega⟩
  have ht : coordinateDistance (rigidMotion a sw sx sy p) (rigidMotion a sw sx sy q)<d :=
    max_lt hdx hdy
  rw [coordinateDistance_rigid a p q sw sx sy hx hy] at ht
  omega

theorem minimumSideSum_three : minimumSideSum 3=4 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 4≠0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem minimumSideSum_eight : minimumSideSum 8=6 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 6≠0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤8)
  have hn := Real.sqrt_nonneg (8 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem canonical_three : canonicalDomain 3=cornerStrip 1 3 0 := by
  simp only [canonicalDomain,canonicalParameters,minimumSideSum_three]
  norm_num [selectorIndex,Nat.sqrt]

theorem canonical_eight : canonicalDomain 8=cornerStrip 2 4 0 := by
  simp only [canonicalDomain,canonicalParameters,minimumSideSum_eight]
  norm_num [selectorIndex,Nat.sqrt]

theorem alternative_three_maximizer : IsMaximizer (cornerStrip 2 2 1) := by
  have hc := CanonicalStrips.cornerStrip_connected_of_short_deficit
    (by decide : 1≤2) (by decide : 2≤2) (by decide : 1<2)
  have hcard : (cornerStrip 2 2 1).card=3 := by decide +kernel
  apply (SmallMaximizers.isMaximizer_iff_count hc (by rw [hcard]; decide)).mpr
  rw [hcard]
  norm_num [proposedMaximum]
  rw [canonical_three]
  exact (adjacent_hull_treeCount_eq_iff (by decide : 1≤2) (by decide : 2≤2)
    (by decide : 1<2) (by decide : 2-2+1≤1)).mpr (by decide)

theorem alternative_eight_maximizer : IsMaximizer (cornerStrip 3 3 1) := by
  have hc := CanonicalStrips.cornerStrip_connected_of_short_deficit
    (by decide : 1≤3) (by decide : 3≤3) (by decide : 1<3)
  have hcard : (cornerStrip 3 3 1).card=8 := by decide +kernel
  apply (SmallMaximizers.isMaximizer_iff_count hc (by rw [hcard]; decide)).mpr
  rw [hcard]
  norm_num [proposedMaximum]
  rw [canonical_eight]
  exact (adjacent_hull_treeCount_eq_iff (by decide : 1≤3) (by decide : 3≤3)
    (by decide : 1<3) (by decide : 3-3+1≤1)).mpr (by decide)

theorem alternative_ten_maximizer : IsMaximizer (cornerStrip 3 4 2) := by
  have hc := CanonicalStrips.cornerStrip_connected_of_short_deficit
    (by decide : 1≤3) (by decide : 3≤4) (by decide : 2<3)
  have hcard : (cornerStrip 3 4 2).card=10 := by decide +kernel
  apply (SmallMaximizers.isMaximizer_iff_count hc (by rw [hcard]; decide)).mpr
  rw [hcard]
  norm_num [proposedMaximum]
  rw [SmallTenComparison.canonicalDomain_ten]
  exact (adjacent_hull_treeCount_eq_iff (by decide : 1≤3) (by decide : 3≤4)
    (by decide : 2<3) (by decide : 4-3+1≤2)).mpr (by decide)

theorem nonunique_three : HasNonisometricMaximizers 3 := by
  refine ⟨canonicalDomain 3,cornerStrip 2 2 1,canonicalDomain_card (by decide),by decide +kernel,
    SmallMaximizers.canonical_small_maximizer (by decide) (by decide) (by decide) (by decide) (by decide),
    alternative_three_maximizer,?_⟩
  apply not_congruent_of_distance (p := (0,0)) (q := (0,2)) (d := 2)
  · rw [canonical_three]; decide +kernel
  · rw [canonical_three]; decide +kernel
  · exact Finset.sdiff_subset
  · norm_num [coordinateDistance]

theorem nonunique_eight : HasNonisometricMaximizers 8 := by
  refine ⟨canonicalDomain 8,cornerStrip 3 3 1,canonicalDomain_card (by decide),by decide +kernel,
    SmallMaximizers.canonical_small_maximizer (by decide) (by decide) (by decide) (by decide) (by decide),
    alternative_eight_maximizer,?_⟩
  apply not_congruent_of_distance (p := (1,0)) (q := (1,3)) (d := 3)
  · rw [canonical_eight]; decide +kernel
  · rw [canonical_eight]; decide +kernel
  · exact Finset.sdiff_subset
  · norm_num [coordinateDistance]

theorem cornerPrimal_subset (R S : ℕ) (M : Corner → Ferrers.Diagram) :
    cornerPrimal R S M⊆rectangle (R+1) (S+1) := by
  rw [cornerPrimal,FerrersPrimalBridge.primalDomain_eq]
  exact Finset.sdiff_subset

theorem nonunique_ten : HasNonisometricMaximizers 10 := by
  refine ⟨canonicalDomain 10,cornerPrimal 2 3 SmallTenComparison.singletonPair,
    canonicalDomain_card (by decide),SmallTenComparison.opposite_ten_card,
    SmallMaximizers.canonical_small_maximizer (by decide) (by decide) (by decide) (by decide) (by decide),
    SmallMaximizers.opposite_ten_maximizer,?_⟩
  apply not_congruent_of_distance (p := (1,0)) (q := (1,4)) (d := 4)
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · exact (cornerPrimal_subset _ _ _).trans (rectangle_mono (by decide) le_rfl)
  · norm_num [coordinateDistance]

theorem nonunique_thirteen : HasNonisometricMaximizers 13 := by
  refine ⟨canonicalDomain 13,cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily,
    canonicalDomain_card (by decide),SmallPrimalComparisons.small_primal_cardinalities.1,
    SmallMaximizers.canonical_small_maximizer (by decide) (by decide) (by decide) (by decide) (by decide),
    SmallMaximizers.opposite_thirteen_maximizer,?_⟩
  apply not_congruent_of_distance (p := (1,0)) (q := (1,4)) (d := 4)
  · rw [CanonicalThirteen.canonicalDomain_thirteen]; decide +kernel
  · rw [CanonicalThirteen.canonicalDomain_thirteen]; decide +kernel
  · exact cornerPrimal_subset _ _ _
  · norm_num [coordinateDistance]

theorem listed_sizes_nonunique {N : ℕ} (h : N=3 ∨ N=8 ∨ N=10 ∨ N=13) :
    HasNonisometricMaximizers N := by
  rcases h with rfl|rfl|rfl|rfl
  · exact nonunique_three
  · exact nonunique_eight
  · exact nonunique_ten
  · exact nonunique_thirteen

end
end SpanningTreeIsoperimetry.NonuniquenessExamples
