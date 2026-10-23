module

public import SpanningTreeIsoperimetry.FoundationsBridge
public import SpanningTreeIsoperimetry.FourCorners
public import SpanningTreeIsoperimetry.EnhancedBoundary

@[expose] public section

/-! The strengthened boundary-vacancy estimate in the current graph model. -/
namespace SpanningTreeIsoperimetry

theorem standardHull_to_foundation {A : Domain} {r s : ℕ} (h : IsStandardHull A r s) :
    SquareMaximality.IsRectHull A 0 0 r s := by
  obtain ⟨yl,hyl⟩ := h.left
  obtain ⟨xb,hxb⟩ := h.bottom
  have hleft := mem_rectangle.mp (h.subset hyl)
  have hbottom := mem_rectangle.mp (h.subset hxb)
  have hrz : (0 : ℤ) < r := hleft.2.1
  have hsz : (0 : ℤ) < s := hbottom.2.2.2
  have hr : 0 < r := by exact_mod_cast hrz
  have hs : 0 < s := by exact_mod_cast hsz
  refine ⟨hr,hs,?_,?_,?_,?_,?_⟩
  · simpa only [← rectangle_eq_foundation] using h.subset
  · exact ⟨(0,yl),hyl,rfl⟩
  · obtain ⟨y,hy⟩ := h.right
    exact ⟨((r:ℤ)-1,y),hy,by simp⟩
  · exact ⟨(xb,0),hxb,rfl⟩
  · obtain ⟨x,hx⟩ := h.top
    exact ⟨(x,(s:ℤ)-1),hx,by simp⟩

/-- The actual union of eight-neighbor vacancy components meeting the boundary,
using the explicit encoding and component construction proved in Foundations. -/
noncomputable def boundaryVacancyUnion (R S : ℕ) (A : Domain) : Domain :=
  SquareMaximality.Boundary.canonicalBoundary R S A

/-- The full boundary estimate of manuscript `prop:gap-cost`, including thin hulls. -/
theorem boundary_gap_cost {A : Domain} {R S : ℕ}
    (hHull : IsStandardHull A (R+1) (S+1)) (hconn : (domainGraph A).Connected) :
    LocalBounds.entropyConstant * (boundaryVacancyUnion R S A).card +
        Real.log (1 + Real.sqrt 2) * EnhancedBoundary.boundaryGapCount R S A ≤
      Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ) -
        Real.log (treeCount (rectangle (R+1) (S+1) \ boundaryVacancyUnion R S A) : ℝ) := by
  rw [entropy_eq_foundation, rectangle_treeCount_eq_foundation,
    treeCount_eq_foundation, rectangle_eq_foundation]
  exact EnhancedBoundary.boundary_gap_cost_all (standardHull_to_foundation hHull)
    (by simpa only [← domainGraph_eq_foundation] using hconn)

end SpanningTreeIsoperimetry
