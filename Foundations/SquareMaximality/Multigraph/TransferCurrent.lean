module

public import SquareMaximality.Multigraph.HadamardFischer

@[expose] public section

/-!
# Transfer-current determinant interface

The analytic content of block negative correlation is proved in
`HadamardFischer`.  This module isolates the remaining graph-theoretic input:
the transfer-current principal-minor identity for forest-containment
probabilities.  The kernel is supplied as a Gram matrix, so positivity is a
theorem rather than an input field.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Multigraph

open scoped BigOperators Matrix

namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)
variable [Fintype V] [Fintype E]

/-- The narrow transfer-current interface needed for forest negative
correlation.  Constructing `transferFactor` and proving
`forestPrincipalMinor` is precisely the Matrix--Tree/transfer-current step;
no correlation inequality is included. -/
structure TransferCurrentDeterminantInput : Type _ where
  transferFactor : Matrix V E ℝ
  forestPrincipalMinor : ∀ (F : Finset E), G.IsEdgeForest F →
    G.containmentRatio F =
      HadamardFischer.principalDet
        (transferFactorᴴ * transferFactor) F

namespace TransferCurrentDeterminantInput

variable {G}

/-- The transfer-current kernel is positive semidefinite because the
interface exposes it as a Gram matrix. -/
theorem kernel_posSemidef (d : G.TransferCurrentDeterminantInput) :
    (d.transferFactorᴴ * d.transferFactor).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self d.transferFactor

/-- The transfer-current determinant interface implies the complete generic
block negative-correlation proposition. -/
theorem forestBlockNegativeCorrelation
    (d : G.TransferCurrentDeterminantInput) :
    G.ForestBlockNegativeCorrelation := by
  intro ι _instFintype _instNonempty F hdisj hforest
  classical
  let K : Matrix E E ℝ := d.transferFactorᴴ * d.transferFactor
  have hK : K.PosSemidef := d.kernel_posSemidef
  have hblockForest (i : ι) : G.IsEdgeForest (F i) := by
    apply G.isEdgeForest_mono hforest
    intro e he
    exact mem_unionEdgeBlocks.mpr ⟨i, he⟩
  calc
    G.containmentRatio (unionEdgeBlocks F) =
        HadamardFischer.principalDet K (unionEdgeBlocks F) :=
      d.forestPrincipalMinor (unionEdgeBlocks F) hforest
    _ ≤ ∏ i, HadamardFischer.principalDet K (F i) :=
      HadamardFischer.principalDet_unionEdgeBlocks_le_prod hK F hdisj
    _ = ∏ i, G.containmentRatio (F i) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact (d.forestPrincipalMinor (F i) (hblockForest i)).symm

end TransferCurrentDeterminantInput

end LabeledMultigraph
end Multigraph
end SquareMaximality
