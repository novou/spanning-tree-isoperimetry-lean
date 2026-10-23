module

public import SpanningTreeIsoperimetry.MaximizerGeometry

@[expose] public section

/-! One-dimensional rectangular endpoint cases. -/
namespace SpanningTreeIsoperimetry

theorem rectangle_full_hull {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    SquareMaximality.IsRectHull (rectangle r s) 0 0 r s := by
  refine ⟨hr,hs,?_,⟨(0,0),?_,rfl⟩,⟨((r : ℤ)-1,0),?_,by simp⟩,
    ⟨(0,0),?_,rfl⟩,⟨(0,(s : ℤ)-1),?_,by simp⟩⟩
  · rw [← rectangle_eq_foundation]
  all_goals simp only [mem_rectangle]
  all_goals omega

theorem rectangle_one_width_tree {s : ℕ} (hs : 0<s) :
    (domainGraph (rectangle 1 s)).IsTree := by
  have hc : (domainGraph (rectangle 1 s)).Connected := by
    rw [domainGraph_eq_foundation,rectangle_eq_foundation]
    exact SquareMaximality.standardRectangle_connected (by omega) hs
  have he := MaximizerGeometry.edgeCount_eq_of_convex_hull hc
    (rectangle_full_hull (by omega) hs) (rectangle_rowConvex 1 s) (rectangle_columnConvex 1 s)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hc,?_⟩
  rw [he,Nat.card_coe_set_eq,Set.ncard_coe_finset,card_rectangle]
  simp only [one_mul]
  omega

theorem rectangle_one_height_tree {r : ℕ} (hr : 0<r) :
    (domainGraph (rectangle r 1)).IsTree := by
  have hc : (domainGraph (rectangle r 1)).Connected := by
    rw [domainGraph_eq_foundation,rectangle_eq_foundation]
    exact SquareMaximality.standardRectangle_connected hr (by omega)
  have he := MaximizerGeometry.edgeCount_eq_of_convex_hull hc
    (rectangle_full_hull hr (by omega)) (rectangle_rowConvex r 1) (rectangle_columnConvex r 1)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hc,?_⟩
  rw [he,Nat.card_coe_set_eq,Set.ncard_coe_finset,card_rectangle]
  simp only [mul_one]
  omega

theorem treeCount_rectangle_one_width {s : ℕ} (hs : 0<s) : treeCount (rectangle 1 s)=1 :=
  treeCount_eq_one_of_tree (rectangle_one_width_tree hs)

theorem treeCount_rectangle_one_height {r : ℕ} (hr : 0<r) : treeCount (rectangle r 1)=1 :=
  treeCount_eq_one_of_tree (rectangle_one_height_tree hr)

@[simp] theorem cornerStrip_zero (r s : ℕ) : cornerStrip r s 0=rectangle r s := by
  simp [cornerStrip,rectangle]

end SpanningTreeIsoperimetry
