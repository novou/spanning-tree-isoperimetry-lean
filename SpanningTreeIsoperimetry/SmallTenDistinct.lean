import SpanningTreeIsoperimetry.SmallMaximizerClassification

/-! The three maximizing isometry classes at ten vertices are distinct.
The two nonrectangular classes have different lattice-distance distributions. -/
namespace SpanningTreeIsoperimetry.SmallTenDistinct
open CornerPrimalDomains NonuniquenessExamples
open scoped Classical
noncomputable section

def latticeDistance (p q : Vertex) : ℤ := |p.1-q.1|+|p.2-q.2|

def distancePairs (A : Domain) (d : ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun pq => latticeDistance pq.1 pq.2=d)).card

theorem latticeDistance_rigid (a p q : Vertex) (sw : Bool) (sx sy : ℤ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) :
    latticeDistance (rigidMotion a sw sx sy p) (rigidMotion a sw sx sy q)=
      latticeDistance p q := by
  cases sw <;> rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
    simp [latticeDistance,rigidMotion,neg_add_eq_sub,abs_sub_comm] <;> ring

theorem distancePairs_congruent {A B : Domain} (h : Congruent A B) (d : ℤ) :
    distancePairs A d=distancePairs B d := by
  obtain ⟨a,sw,sx,sy,hx,hy,rfl⟩ := h
  let f := rigidMotion a sw sx sy
  have hf : Function.Injective f := (rigidEquiv a sw sx sy hx hy).injective
  have hff : Function.Injective (Prod.map f f) := by
    intro p q he
    exact Prod.ext (hf (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))
  unfold distancePairs
  rw [← Finset.prodMap_image_product,Finset.filter_image]
  simp only [Prod.map_fst,Prod.map_snd]
  simp only [f,latticeDistance_rigid a _ _ sw sx sy hx hy]
  exact (Finset.card_image_of_injective _ hff).symm

theorem alternatives_not_congruent :
    ¬Congruent (cornerStrip 3 4 2) (cornerPrimal 2 3 SmallTenComparison.singletonPair) := by
  intro h
  have he := distancePairs_congruent h 2
  have hA : distancePairs (cornerStrip 3 4 2) 2=30 := by decide +kernel
  have hB : distancePairs (cornerPrimal 2 3 SmallTenComparison.singletonPair) 2=32 :=
    by decide +kernel
  omega

theorem canonical_not_strip : ¬Congruent (canonicalDomain 10) (cornerStrip 3 4 2) := by
  apply not_congruent_of_distance (p := (1,0)) (q := (1,4)) (d := 4)
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · exact Finset.sdiff_subset.trans (rectangle_mono (by decide) le_rfl)
  · norm_num [coordinateDistance]

theorem canonical_not_opposite :
    ¬Congruent (canonicalDomain 10) (cornerPrimal 2 3 SmallTenComparison.singletonPair) := by
  apply not_congruent_of_distance (p := (1,0)) (q := (1,4)) (d := 4)
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · rw [SmallTenComparison.canonicalDomain_ten]; decide +kernel
  · exact (cornerPrimal_subset _ _ _).trans (rectangle_mono (by decide) le_rfl)
  · norm_num [coordinateDistance]

end
end SpanningTreeIsoperimetry.SmallTenDistinct
