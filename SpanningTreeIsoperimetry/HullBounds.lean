import SpanningTreeIsoperimetry.FoundationsBridge
import SpanningTreeIsoperimetry.StabilityGeometry
import SquareMaximality.Theorem

/-! Closed bulk hull bound, with the actual current spanning-tree count.
The complete planar, correlation, and entropy proofs are included locally.
This is the bulk estimate; the additional interior-component surcharge is
developed separately. -/
namespace SpanningTreeIsoperimetry

theorem translatedRectangle_eq_foundation (r s : ℕ) (a : Vertex) :
    (rectangle r s).image (translate a) =
      SquareMaximality.rectangle a.1 a.2 r s := by
  ext ⟨x,y⟩
  constructor
  · intro hv
    obtain ⟨⟨u,v⟩,hw,heq⟩ := Finset.mem_image.mp hv
    simp only [mem_rectangle] at hw
    simp [SquareMaximality.rectangle]
    simp [translate] at heq
    omega
  · intro hv
    simp [SquareMaximality.rectangle] at hv
    refine Finset.mem_image.mpr ⟨(x-a.1,y-a.2),?_,?_⟩
    · simp only [mem_rectangle]
      omega
    · simp [translate]

theorem fitsRectangle_of_foundationHull {S : Domain} {a b : ℤ} {r s : ℕ}
    (h : SquareMaximality.IsRectHull S a b r s) : FitsRectangle S r s := by
  refine ⟨(a,b),?_⟩
  simpa only [translatedRectangle_eq_foundation] using h.2.2.1

/-- An arbitrary translated minimal hull incurs the full entropy cost for
every missing vertex. All inputs of the foundation's modular hull proof are
instantiated by their included proofs here. -/
theorem hull_bulk_bound {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected)
    (hHull : SquareMaximality.IsRectHull S a b r s) :
    Real.log (treeCount S : ℝ) - Real.log (treeCount (rectangle r s) : ℝ) ≤
      -LocalBounds.entropyConstant * ((r*s-S.card : ℕ) : ℝ) := by
  let inputs := SquareMaximality.StagedEqualityInputs.toEqualityInputs
    SquareMaximality.fullyFormalizedStagedEqualityInputs
  have h := inputs.hullPenalty.bound
    (by simpa only [← domainGraph_eq_foundation] using hconn) hHull
  rw [SquareMaximality.rectangle_sdiff_card_of_subset hHull.2.2.1] at h
  rw [rectangle_treeCount_eq_foundation, treeCount_eq_foundation, entropy_eq_foundation]
  exact h

theorem exists_hull_bulk_bound {S : Domain}
    (hconn : (domainGraph S).Connected) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ FitsRectangle S r s ∧ S.card ≤ r*s ∧
      Real.log (treeCount S : ℝ) - Real.log (treeCount (rectangle r s) : ℝ) ≤
        -LocalBounds.entropyConstant * ((r*s-S.card : ℕ) : ℝ) := by
  have hnonempty : S.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v.val,v.property⟩
  obtain ⟨a,b,r,s,hHull⟩ := SquareMaximality.exists_isRectHull_of_nonempty S hnonempty
  refine ⟨r,s,hHull.1,hHull.2.1,fitsRectangle_of_foundationHull hHull,?_,
    hull_bulk_bound hconn hHull⟩
  have hcard := Finset.card_le_card hHull.2.2.1
  simpa only [SquareMaximality.rectangle_card] using hcard

end SpanningTreeIsoperimetry
