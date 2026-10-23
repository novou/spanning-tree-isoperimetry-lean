module

public import SquareMaximality.Dual.Rayleigh

@[expose] public section

/-!
# One Matrix--Tree input suffices

The development originally exposed separate cofactor interfaces for simple
rectangles and for edge-labelled multigraphs.  The latter is the usual
finite Matrix--Tree theorem in the generality needed by the manuscript.
This file proves that it also supplies the rectangular interface, by giving
each edge of the rectangular simple graph its own label.
-/

set_option autoImplicit false

namespace SquareMaximality

open SimpleGraph

/-- The generic labelled Matrix--Tree theorem implies its rectangular
specialization.  The generic interface is proved in
`Inputs/MatrixTreeTheorem.lean` and instantiated by the public theorem. -/
theorem rectangleCofactorInput_of_labeledMatrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    RectangleCofactorInput := by
  classical
  intro r s hr hs root
  let G : SimpleGraph (Fin r × Fin s) := pathGraph r □ pathGraph s
  have hG : G.Connected := by
    exact (standardRectangleGridIso r s).connected_iff.mp
      (standardRectangle_connected hr hs)
  have hcount :
      (Dual.simpleEdgeLabeledGraph G).spanningTreeCount = tauRect r s := by
    calc
      (Dual.simpleEdgeLabeledGraph G).spanningTreeCount =
          Dual.spanningForestCount G :=
        Dual.simpleEdgeLabeledGraph_spanningTreeCount G hG
      _ = treeCount G := Dual.spanningForestCount_eq_treeCount hG
      _ = treeCount (inducedGrid (rectangle 0 0 r s)) :=
        (treeCount_congr (standardRectangleGridIso r s)).symm
      _ = tauRect r s := rfl
  have hcofactor := hMatrixTree (Fin r × Fin s) G.edgeSet
    (Dual.simpleEdgeLabeledGraph G) root
  rw [hcount, Dual.simpleEdgeLabeledGraph_reducedLaplacian] at hcofactor
  exact hcofactor

end SquareMaximality
