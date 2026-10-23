module

public import SpanningTreeIsoperimetry.GreenLogDetComparison
public import SquareMaximality.Multigraph.HadamardFischer

@[expose] public section

/-! Actual finite Green-minor products and superadditivity of deletion energy
for disjoint face sets. -/
namespace SpanningTreeIsoperimetry.GreenMinorProducts
open Ferrers CornerEnergy SquareMaximality.Boundary
open SquareMaximality.Multigraph
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def ambientSubset (U M : Diagram) : Finset {p // p∈U} :=
  Finset.univ.filter (fun p => p.val∈M)

theorem mem_ambientSubset (U M : Diagram) (p : {p // p∈U}) :
    p∈ambientSubset U M ↔ p.val∈M := by simp [ambientSubset]

def ambientSubsetEquiv {U M : Diagram} (hM : M⊆U) :
    {p // p∈M} ≃ {p // p∈ambientSubset U M} where
  toFun p := ⟨⟨p.val,hM p.property⟩,(mem_ambientSubset U M _).mpr p.property⟩
  invFun p := ⟨p.val.val,(mem_ambientSubset U M p.val).mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem greenMinor_det_eq_principal {U M : Diagram} (hM : M⊆U) :
    (greenMinor hM).det=
      (HadamardFischer.principalSubmatrix (fourIminusAdjacency U)⁻¹ (ambientSubset U M)).det := by
  exact Matrix.det_submatrix_equiv_self (ambientSubsetEquiv hM)
    (HadamardFischer.principalSubmatrix (fourIminusAdjacency U)⁻¹ (ambientSubset U M))

theorem ambientSubset_biUnion {ι : Type*} [Fintype ι] (U : Diagram) (M : ι → Diagram) :
    ambientSubset U (Finset.univ.biUnion M)=Finset.univ.biUnion (fun i => ambientSubset U (M i)) := by
  ext p
  simp [ambientSubset,Finset.mem_biUnion]

theorem union_fit {ι : Type*} [Fintype ι] {U : Diagram} (M : ι → Diagram)
    (hfit : ∀ i, M i⊆U) : Finset.univ.biUnion M⊆U := by
  intro p hp
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  exact hfit i hi

theorem greenMinor_det_le_prod {ι : Type*} [Fintype ι] {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (M : ι → Diagram) (hfit : ∀ i, M i⊆U)
    (hd : Pairwise fun i j => Disjoint (M i) (M j)) :
    (greenMinor (union_fit M hfit)).det≤∏ i, (greenMinor (hfit i)).det := by
  have hdi : Pairwise fun i j => Disjoint (ambientSubset U (M i)) (ambientSubset U (M j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (hd hij))
      ((mem_ambientSubset U (M i) p).mp hp) ((mem_ambientSubset U (M j) p).mp hq)
  have h := HadamardFischer.det_principal_biUnion_le_prod (dirichlet_posDef hU).inv.posSemidef
    (fun i => ambientSubset U (M i)) hdi
  rw [greenMinor_det_eq_principal,ambientSubset_biUnion]
  simpa only [greenMinor_det_eq_principal] using h

theorem dirichletEnergy_superadditive {ι : Type*} [Fintype ι] {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (M : ι → Diagram) (hfit : ∀ i, M i⊆U)
    (hd : Pairwise fun i j => Disjoint (M i) (M j)) :
    (∑ i, dirichletEnergy (hfit i))≤dirichletEnergy (union_fit M hfit) := by
  have hdet := greenMinor_det_le_prod hU M hfit hd
  have hp (i : ι) : 0<(greenMinor (hfit i)).det := greenMinor_det_pos hU (hfit i)
  have hprod : 0<∏ i, (greenMinor (hfit i)).det := Finset.prod_pos (fun i _ => hp i)
  have hl := (Real.log_le_log_iff (greenMinor_det_pos hU (union_fit M hfit)) hprod).mpr hdet
  rw [Real.log_prod (fun i _ => (hp i).ne')] at hl
  have hc : (Finset.univ.biUnion M).card=∑ i, (M i).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hd hij)]
  simp only [dirichletEnergy,Finset.sum_sub_distrib,Finset.sum_neg_distrib,hc,Nat.cast_sum,
    ← Finset.mul_sum]
  linarith

end
end SpanningTreeIsoperimetry.GreenMinorProducts
