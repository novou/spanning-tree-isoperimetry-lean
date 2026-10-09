import SquareMaximality.Dual.TappWindowScan
import SquareMaximality.Dual.TappPrefixBounds
import SquareMaximality.Inputs.MatrixTreeBridge

/-!
# Closing Tapp's finite Rayleigh step

This module combines the componentwise finite Rayleigh theorem in
`Dual.Rayleigh` with the translated-window geometry and the already proved
square bulk-entropy limit.  The only external theorem parameter is the
generic labelled Matrix--Tree/cofactor interface, proved in
`Inputs.MatrixTreeTheorem`.

The factor-four bound is discharged from first principles: at a complete
square step the old prefix contains a two-edge northwest path, and the
Dirichlet objective of a unit two-edge path is at most two.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

noncomputable section

private theorem pathThree_dirichletEnergy (f : Fin 3 → ℝ) :
    dirichletEnergy (SimpleGraph.pathGraph 3) f =
      (f 0 - f 1) ^ 2 + (f 1 - f 2) ^ 2 := by
  have hpairs : adjacencyPairFinset (SimpleGraph.pathGraph 3) =
      {(0, 1), (1, 0), (1, 2), (2, 1)} := by
    classical
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [adjacencyPairFinset, SimpleGraph.pathGraph_adj]
  rw [dirichletEnergy_eq_pairSum, hpairs]
  simp
  ring

private theorem pathThree_dirichletObjective_le_two (f : Fin 3 → ℝ) :
    dirichletObjective (SimpleGraph.pathGraph 3) 0 2 f ≤ 2 := by
  unfold dirichletObjective
  rw [pathThree_dirichletEnergy]
  nlinarith [sq_nonneg (f 0 - f 1 - 1),
    sq_nonneg (f 1 - f 2 - 1)]

/-- A concrete two-edge path gives the sharp elementary resistance bound
`R(a,b) ≤ 2`, even when the ambient graph has unrelated components. -/
theorem twoForestResistance_le_two_of_two_edge_path
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (a m b : V) (ham : P.Adj a m) (hmb : P.Adj m b)
    (hab : a ≠ b) (hnotadj : ¬P.Adj a b) :
    twoForestResistance P a b ≤ 2 := by
  classical
  have hamne : a ≠ m := ham.ne
  have hmbne : m ≠ b := hmb.ne
  have hreach : P.Reachable a b := ham.reachable.trans hmb.reachable
  let a' : ReachableVertex P a := ⟨a, SimpleGraph.Reachable.refl a⟩
  let m' : ReachableVertex P a := ⟨m, ham.reachable⟩
  let b' : ReachableVertex P a := ⟨b, hreach⟩
  let emb : Fin 3 ↪ ReachableVertex P a :=
    { toFun := ![a', m', b']
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [a', m', b'] }
  let e : InjectiveGraphHom (SimpleGraph.pathGraph 3)
      (reachableComponentGraph P a) :=
    { toEmbedding := emb
      map_adj := by
        intro u v huv
        rw [SimpleGraph.pathGraph_adj] at huv
        fin_cases u <;> fin_cases v <;>
          simp_all [emb, a', m', b'] <;>
          first | exact ham | exact ham.symm | exact hmb | exact hmb.symm }
  have hab' : a' ≠ b' := fun h ↦ hab (congrArg Subtype.val h)
  have hnotadj' : ¬(reachableComponentGraph P a).Adj a' b' := hnotadj
  let f := effectivePotential (reachableComponentGraph P a) a' b' hab'
  have hcomponent :
      twoForestResistance (reachableComponentGraph P a) a' b' ≤ 2 := by
    calc
      twoForestResistance (reachableComponentGraph P a) a' b' =
          dirichletObjective (reachableComponentGraph P a) a' b' f :=
        (dirichletObjective_effectivePotential
          (twoForestCofactorInput_of_matrixTree hMatrixTree)
          (reachableComponentGraph P a) (reachableComponentGraph_connected P a)
          a' b' hab' hnotadj').symm
      _ = dirichletObjective (reachableComponentGraph P a)
          (e.toEmbedding 0) (e.toEmbedding 2) f := rfl
      _ ≤ dirichletObjective (SimpleGraph.pathGraph 3) 0 2 (e.pullback f) :=
        e.objective_le_pullback 0 2 f
      _ ≤ 2 := pathThree_dirichletObjective_le_two _
  rw [twoForestResistance_eq_reachableComponent P a b hreach]
  exact hcomponent

private theorem faceLattice_not_adj_diagonal
    (z : Boundary.LatticePoint) :
    ¬Boundary.faceLattice.Adj z (z.1 + 1, z.2 + 1) := by
  simp [Boundary.faceLattice, Boundary.natManhattanDist, Nat.dist]

/-- The local length-two hook required by the bulk factor-four bound follows
from the actual northwest path in every complete square prefix. -/
theorem squareCompleteStepResistanceUpperBound_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    SquareCompleteStepResistanceUpperBound := by
  classical
  intro n k hk
  dsimp only
  intro hpx hpy
  let p := (wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩
  let hsquare := squareGrid_containsUnitSquare p hpx hpy
  let sw := unitSquareSWVertex hsquare
  let nw := unitSquareNWCornerVertex hsquare
  let ne := unitSquareNECornerVertex hsquare
  let P := wordsPrefixGraph (squareGrid n) (squareGridCoord n) k
  have hpone : 1 ≤ p.1.1 := by
    change 0 < p.1.1 at hpx
    exact hpx
  have hcoord : squareGridCoord n
      ((wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩) =
      (p.1.1 - 1 + 1, p.2.1) := by
    change (p.1.1, p.2.1) = (p.1.1 - 1 + 1, p.2.1)
    rw [Nat.sub_add_cancel hpone]
  have hswMem : sw ∈ wordsPrefixVertices (squareGridCoord n) k := by
    apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n) k hk
    rw [unitSquareSWVertex_coord hsquare, hcoord]
    rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, by omega⟩
  have hnwMem : nw ∈ wordsPrefixVertices (squareGridCoord n) k := by
    apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n) k hk
    rw [unitSquareNWCornerVertex_coord hsquare, hcoord]
    rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
    left
    omega
  have hneMem : ne ∈ wordsPrefixVertices (squareGridCoord n) k := by
    apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n) k hk
    rw [unitSquareNECornerVertex_coord hsquare, hcoord]
    rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
    left
    omega
  have hswNW : P.Adj sw nw :=
    ⟨unitSquareSW_NW_adj hsquare, hswMem, hnwMem⟩
  have hnwNE : P.Adj nw ne :=
    ⟨unitSquareNW_NE_adj hsquare, hnwMem, hneMem⟩
  have hswne : sw ≠ ne := by
    intro h
    have hc := congrArg (squareGridCoord n) h
    rw [unitSquareSWVertex_coord hsquare,
      unitSquareNECornerVertex_coord hsquare] at hc
    have hxcoord := congrArg Prod.fst hc
    simp only at hxcoord
    omega
  have hnotadj : ¬P.Adj sw ne := by
    intro hadj
    have hlat := squareGrid_le_faceLattice n hadj.1
    change Boundary.faceLattice.Adj
      (squareGridCoord n sw) (squareGridCoord n ne) at hlat
    dsimp only [sw, ne] at hlat
    rw [unitSquareSWVertex_coord hsquare,
      unitSquareNECornerVertex_coord hsquare] at hlat
    exact faceLattice_not_adj_diagonal (p.1.1 - 1, p.2.1) hlat
  exact twoForestResistance_le_two_of_two_edge_path
    hMatrixTree P sw nw ne hswNW hnwNE hswne hnotadj

/-- All square prefix multipliers are at most four, with no remaining local
graph-theory assumption. -/
theorem squarePrefixMultiplierUpperBound_four_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    SquarePrefixMultiplierUpperBound 4 :=
  squarePrefixMultiplierUpperBound_four_of_complete
    (squareCompleteStepResistanceUpperBound_of_matrixTree hMatrixTree)

/-- A fixed canonical half-plane window bounds every translated scan
multiplier from above. -/
theorem squareScanMultiplierUpperBound_of_window
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) :
    SquareScanMultiplierUpperBound z X Y hx hy
      (2 + twoForestResistance (halfPlaneWindowGraph z X Y)
        (halfPlaneWindowSW z X Y (by omega) (by omega))
        (halfPlaneWindowNE z X Y hx hy)) := by
  classical
  intro n hX hY d
  let current := squareScanCurrent z hx hy hX hY d
  let k := squareScanIndex z hx hy hX hY d
  have hk : k < Fintype.card (Fin n × Fin n) :=
    squareGridIndex_lt current
  let base : Boundary.LatticePoint := (z.1 + d.1.1, z.2 + d.2.1)
  let hsquare := squareScanCurrent_containsUnitSquare z hx hy hX hY d
  have hcoord : squareGridCoord n
      ((wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩) =
      (base.1 + 1, base.2) := by
    have hindex : (⟨k, hk⟩ : Fin (Fintype.card (Fin n × Fin n))) =
        (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm current := by
      apply Fin.ext
      rfl
    rw [hindex,
      (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.apply_symm_apply]
    apply Prod.ext
    · simp [base, current, squareScanCurrent]
      omega
    · simp [base, current, squareScanCurrent]
  let e := halfPlaneWindowGraphHomToSquarePrefix z hx hy hX hY d
  let wsw := halfPlaneWindowSW z X Y (by omega) (by omega)
  let wne := halfPlaneWindowNE z X Y hx hy
  have hesw : e.toEmbedding wsw = unitSquareSWVertex hsquare :=
    halfPlaneWindowToSquareGrid_sw z hx hy hX hY d
  have hene : e.toEmbedding wne = unitSquareNECornerVertex hsquare :=
    halfPlaneWindowToSquareGrid_ne z hx hy hX hY d
  have hWReach : (halfPlaneWindowGraph z X Y).Reachable wsw wne :=
    (halfPlaneWindowGraph_connected z X Y hx hy) wsw wne
  have hPReach :
      (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k).Reachable
        (e.toEmbedding wsw) (e.toEmbedding wne) := by
    rw [hesw, hene]
    exact wordsPrefixGraph_square_neighbors_reachable
      (squareGridCoord n) k hk base hsquare hcoord
  have hwswne : wsw ≠ wne := by
    intro h
    have hc := congrArg (fun w ↦ w.1) h
    dsimp only [wsw, wne, halfPlaneWindowSW, halfPlaneWindowNE] at hc
    have hxcoord := congrArg Prod.fst hc
    simp only at hxcoord
    omega
  have hWnotadj : ¬(halfPlaneWindowGraph z X Y).Adj wsw wne := by
    exact faceLattice_not_adj_diagonal z
  have hPnotadj :
      ¬(wordsPrefixGraph (squareGrid n) (squareGridCoord n) k).Adj
        (e.toEmbedding wsw) (e.toEmbedding wne) := by
    rw [hesw, hene]
    intro hadj
    have hlat := squareGrid_le_faceLattice n hadj.1
    change Boundary.faceLattice.Adj
      (squareGridCoord n (unitSquareSWVertex hsquare))
      (squareGridCoord n (unitSquareNECornerVertex hsquare)) at hlat
    rw [unitSquareSWVertex_coord hsquare,
      unitSquareNECornerVertex_coord hsquare] at hlat
    exact faceLattice_not_adj_diagonal base hlat
  have hray :
      twoForestResistance
          (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)
          (unitSquareSWVertex hsquare) (unitSquareNECornerVertex hsquare) ≤
        twoForestResistance (halfPlaneWindowGraph z X Y) wsw wne := by
    rw [← hesw, ← hene]
    exact twoForestResistance_antitone_embedding_components
      hMatrixTree e wsw wne hwswne hWReach hPReach hWnotadj hPnotadj
  have hmult := wordsPrefixMultiplier_eq_two_add_twoForestResistance
    (squareGrid n) (squareGridCoord n) k hk base
    (squareGrid_le_faceLattice n) hsquare hcoord
  dsimp only [k] at hmult ⊢
  rw [hmult]
  simpa only [add_comm] using add_le_add_left hray 2

/-- The bulk entropy contradiction proves the canonical finite-window lower
bound for every window. -/
theorem canonicalHalfPlaneMultiplierLowerBound_squareLatticeEntropy
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    CanonicalHalfPlaneMultiplierLowerBound squareLatticeEntropy := by
  intro z X Y hx hy
  exact exp_squareLatticeEntropy_le_of_scan_bounds
    (rectangleCofactorInput_of_labeledMatrixTree hMatrixTree)
    z hx hy (squarePrefixMultiplierUpperBound_four_of_matrixTree hMatrixTree)
    (squareScanMultiplierUpperBound_of_window hMatrixTree z X Y hx hy)

/-- End-to-end closure of the half-plane two-forest input used by Tapp's
square-family argument.  Matrix--Tree is the sole remaining parameter. -/
theorem halfPlaneTwoForestResistanceBound_squareLatticeEntropy
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    HalfPlaneTwoForestResistanceBound squareLatticeEntropy :=
  halfPlaneTwoForestResistanceBound_of_canonical hMatrixTree
    (canonicalHalfPlaneMultiplierLowerBound_squareLatticeEntropy hMatrixTree)

end

end Dual
end SquareMaximality
