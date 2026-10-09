import SquareMaximality.Dual.Rayleigh
import SquareMaximality.Dual.TappBulkGeometry

/-!
# Embedding half-plane windows into square prefixes

This is the finite bridge between Rayleigh monotonicity and the rectangular
bulk-entropy contradiction.  A fixed canonical half-plane window is
translated into every scan position of a sufficiently large square.  Its
two terminals become the west and north neighbours of the current
words-on-a-page vertex.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

/-- Translate a canonical half-plane window into an `n x n` square at one
scan shift. -/
def halfPlaneWindowToSquareGrid
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (_hx : z.1 + 1 < X) (_hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    {w // w ∈ halfPlaneWindowVertices z X Y} ↪ (Fin n × Fin n) where
  toFun w :=
    (⟨w.1.1 + d.1.1, by
        have hw := (mem_halfPlaneWindowVertices.mp w.2).1
        omega⟩,
      ⟨w.1.2 + d.2.1, by
        have hw := (mem_halfPlaneWindowVertices.mp w.2).2.1
        omega⟩)
  inj' u v huv := by
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg (fun p : Fin n × Fin n ↦ p.1.1) huv
      simp only at h
      omega
    · have h := congrArg (fun p : Fin n × Fin n ↦ p.2.1) huv
      simp only at h
      omega

@[simp] theorem halfPlaneWindowToSquareGrid_coord
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y)
    (w : {w // w ∈ halfPlaneWindowVertices z X Y}) :
    squareGridCoord n (halfPlaneWindowToSquareGrid z hx hy hX hY d w) =
      (w.1.1 + d.1.1, w.1.2 + d.2.1) :=
  rfl

/-- Every translated window vertex occurs strictly before the corresponding
scan current. -/
theorem halfPlaneWindowToSquareGrid_mem_prefix
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y)
    (w : {w // w ∈ halfPlaneWindowVertices z X Y}) :
    halfPlaneWindowToSquareGrid z hx hy hX hY d w ∈
      wordsPrefixVertices (squareGridCoord n)
        (squareScanIndex z hx hy hX hY d) := by
  unfold squareScanIndex
  apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n)
    (squareGridIndex (squareScanCurrent z hx hy hX hY d))
    (squareGridIndex_lt (squareScanCurrent z hx hy hX hY d))
  rw [squareGridOrderIso_at_index]
  simp only [halfPlaneWindowToSquareGrid_coord, squareScanCurrent_coord]
  exact wordsOnPageKey_translate_lt
    (u := w.1) (v := (z.1 + 1, z.2)) d.1.1 d.2.1
    (mem_halfPlaneWindowVertices.mp w.2).2.2

/-- The translated window is a graph embedding into the old square prefix
at the scan current. -/
noncomputable def halfPlaneWindowGraphHomToSquarePrefix
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    InjectiveGraphHom (halfPlaneWindowGraph z X Y)
      (wordsPrefixGraph (squareGrid n) (squareGridCoord n)
        (squareScanIndex z hx hy hX hY d)) where
  toEmbedding := halfPlaneWindowToSquareGrid z hx hy hX hY d
  map_adj := by
    intro u v huv
    refine ⟨?_, halfPlaneWindowToSquareGrid_mem_prefix
      z hx hy hX hY d u,
      halfPlaneWindowToSquareGrid_mem_prefix z hx hy hX hY d v⟩
    apply (squareGrid_adj_iff_faceLattice _ _).mpr
    rw [halfPlaneWindowToSquareGrid_coord,
      halfPlaneWindowToSquareGrid_coord, faceLattice_translate_adj_iff]
    exact huv

/-- The translated southwest terminal is the west neighbour of the scan
current. -/
theorem halfPlaneWindowToSquareGrid_sw
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    halfPlaneWindowToSquareGrid z hx hy hX hY d
        (halfPlaneWindowSW z X Y (by omega) (by omega)) =
      unitSquareSWVertex
        (squareScanCurrent_containsUnitSquare z hx hy hX hY d) := by
  apply (squareGridCoord n).injective
  rw [unitSquareSWVertex_coord]
  rfl

/-- The translated northeast terminal is the north neighbour of the scan
current. -/
theorem halfPlaneWindowToSquareGrid_ne
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    halfPlaneWindowToSquareGrid z hx hy hX hY d
        (halfPlaneWindowNE z X Y hx hy) =
      unitSquareNECornerVertex
        (squareScanCurrent_containsUnitSquare z hx hy hX hY d) := by
  apply (squareGridCoord n).injective
  rw [halfPlaneWindowToSquareGrid_coord,
    unitSquareNECornerVertex_coord]
  simp only [halfPlaneWindowNE]
  apply Prod.ext <;> simp <;> omega

end Dual
end SquareMaximality
