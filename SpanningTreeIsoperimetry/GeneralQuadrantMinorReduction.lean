module

public import SpanningTreeIsoperimetry.QuadrantMinorReduction

@[expose] public section

set_option backward.privateInPublic true

/-! Northeast-boundary reduction for every finite Ferrers diagram.
The interior matrix equations are consequences of the actual quadrant Green
function's Poisson equation; no matrix certificate is assumed. -/
namespace SpanningTreeIsoperimetry.GeneralQuadrantMinorReduction
open Ferrers CornerEnergy BoundaryGreenBounds BoundaryGreenLoss QuadrantMinorEnergy
open SquareMaximality.Boundary Matrix
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Cells whose east and north neighbours both lie in M. -/
def interior (M : Diagram) : Diagram :=
  M.filter (fun p => (p.1+1,p.2)∈M ∧ (p.1,p.2+1)∈M)

/-- The northeast boundary of the diagram. -/
def boundary (M : Diagram) : Diagram := M\interior M

@[simp] theorem mem_interior {M : Diagram} {p : Point} :
    p∈interior M ↔ p∈M ∧ (p.1+1,p.2)∈M ∧ (p.1,p.2+1)∈M := Finset.mem_filter

theorem interior_subset (M : Diagram) : interior M⊆M := Finset.filter_subset _ _
theorem boundary_subset (M : Diagram) : boundary M⊆M := Finset.sdiff_subset

theorem interior_isFerrers {M : Diagram} (hM : IsFerrers M) : IsFerrers (interior M) := by
  intro p hp q hx hy
  obtain ⟨hp,he,hn⟩ := mem_interior.mp hp
  exact mem_interior.mpr ⟨hM p hp q hx hy,
    hM (p.1+1,p.2) he (q.1+1,q.2) (by omega) hy,
    hM (p.1,p.2+1) hn (q.1,q.2+1) hx (by omega)⟩

/-- The actual quadrant Green principal matrix on a finite set. -/
def minor (M : Diagram) : Matrix {p // p∈M} {p // p∈M} ℝ :=
  quadrantMinor Subtype.val

/-- Interior indices followed by boundary indices enumerate every cell once. -/
def splitEquiv (M : Diagram) :
    {p // p∈interior M} ⊕ {p // p∈boundary M} ≃ {p // p∈M} :=
  (Equiv.sumComm _ _).trans (faceSplitEquiv (interior_subset M))

@[simp] theorem splitEquiv_inl (M : Diagram) (p : {p // p∈interior M}) :
    splitEquiv M (.inl p)=⟨p.val,interior_subset M p.property⟩ := rfl

@[simp] theorem splitEquiv_inr (M : Diagram) (p : {p // p∈boundary M}) :
    splitEquiv M (.inr p)=⟨p.val,boundary_subset M p.property⟩ := rfl

def splitGreen (M : Diagram) : Matrix
    ({p // p∈interior M} ⊕ {p // p∈boundary M})
    ({p // p∈interior M} ⊕ {p // p∈boundary M}) ℝ :=
  (minor M).submatrix (splitEquiv M) (splitEquiv M)

def splitDirichlet (M : Diagram) : Matrix
    ({p // p∈interior M} ⊕ {p // p∈boundary M})
    ({p // p∈interior M} ⊕ {p // p∈boundary M}) ℝ :=
  (fourIminusAdjacency M).submatrix (splitEquiv M) (splitEquiv M)

abbrev interiorGreen (M : Diagram) := (splitGreen M).toBlocks₁₁
abbrev interiorBoundaryGreen (M : Diagram) := (splitGreen M).toBlocks₁₂
abbrev boundaryInteriorGreen (M : Diagram) := (splitGreen M).toBlocks₂₁
abbrev boundaryGreen (M : Diagram) := (splitGreen M).toBlocks₂₂
abbrev coupling (M : Diagram) := (splitDirichlet M).toBlocks₁₂

theorem interiorGreen_eq (M : Diagram) : interiorGreen M=minor (interior M) := rfl
theorem boundaryGreen_eq (M : Diagram) : boundaryGreen M=minor (boundary M) := rfl

theorem splitDirichlet_interior (M : Diagram) :
    (splitDirichlet M).toBlocks₁₁=fourIminusAdjacency (interior M) := by
  ext p q
  simp only [splitDirichlet,Matrix.toBlocks₁₁,Matrix.submatrix_apply,splitEquiv_inl,
    fourIminusAdjacency_apply,Subtype.ext_iff,Matrix.of_apply]

/-- All quadrant neighbours of an interior cell belong to the full diagram;
therefore zero extension does not alter its Laplacian. -/
theorem laplacian_extend_interior {M : Diagram} (hM : IsFerrers M)
    {p : Point} (hp : p∈interior M) (f : Point → ℝ) :
    laplacian (extend M (fun q => f q.val)) p=laplacian f p := by
  obtain ⟨hm,he,hn⟩ := mem_interior.mp hp
  have hw : (p.1-1,p.2)∈M := hM p hm (p.1-1,p.2) (Nat.sub_le _ _) le_rfl
  have hs : (p.1,p.2-1)∈M := hM p hm (p.1,p.2-1) le_rfl (Nat.sub_le _ _)
  simp only [laplacian,extend_mem _ hm,extend_mem _ he,extend_mem _ hn,
    extend_mem _ hw,extend_mem _ hs]

/-- The actual Green Poisson equation at every interior row. -/
theorem interior_row {M : Diagram} (hM : IsFerrers M)
    (p : {p // p∈interior M}) (q : {p // p∈M}) :
    (fourIminusAdjacency M*minor M) ⟨p.val,interior_subset M p.property⟩ q=
      if p.val=q.val then 1 else 0 := by
  change (fourIminusAdjacency M*ᵥ (fun t => quadrantGreen t.val q.val))
    ⟨p.val,interior_subset M p.property⟩=_
  rw [dirichlet_mulVec]
  change laplacian (extend M (fun t => quadrantGreen t.val q.val)) p.val=_
  rw [laplacian_extend_interior hM p.property (fun t => quadrantGreen t q.val),quadrantGreen_equation]

private theorem block_product₁₁ (M : Diagram) :
    (splitDirichlet M*splitGreen M).toBlocks₁₁=
      (splitDirichlet M).toBlocks₁₁*interiorGreen M+coupling M*boundaryInteriorGreen M := by
  nth_rw 1 [← Matrix.fromBlocks_toBlocks (splitDirichlet M),← Matrix.fromBlocks_toBlocks (splitGreen M)]
  rw [Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₁]

private theorem block_product₁₂ (M : Diagram) :
    (splitDirichlet M*splitGreen M).toBlocks₁₂=
      (splitDirichlet M).toBlocks₁₁*interiorBoundaryGreen M+coupling M*boundaryGreen M := by
  nth_rw 1 [← Matrix.fromBlocks_toBlocks (splitDirichlet M),← Matrix.fromBlocks_toBlocks (splitGreen M)]
  rw [Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₂]

theorem interior_identity {M : Diagram} (hM : IsFerrers M) :
    fourIminusAdjacency (interior M)*interiorGreen M+coupling M*boundaryInteriorGreen M=1 := by
  rw [← splitDirichlet_interior,← block_product₁₁]
  ext p q
  change ((splitDirichlet M*splitGreen M) (.inl p) (.inl q))=_
  rw [splitDirichlet,splitGreen,Matrix.submatrix_mul_equiv]
  change (fourIminusAdjacency M*minor M) (splitEquiv M (.inl p)) (splitEquiv M (.inl q))=_
  rw [splitEquiv_inl,splitEquiv_inl,interior_row hM]
  simp only [Matrix.one_apply,Subtype.ext_iff]

theorem interior_boundary {M : Diagram} (hM : IsFerrers M) :
    fourIminusAdjacency (interior M)*interiorBoundaryGreen M+coupling M*boundaryGreen M=0 := by
  rw [← splitDirichlet_interior,← block_product₁₂]
  ext p q
  change ((splitDirichlet M*splitGreen M) (.inl p) (.inr q))=_
  rw [splitDirichlet,splitGreen,Matrix.submatrix_mul_equiv]
  change (fourIminusAdjacency M*minor M) (splitEquiv M (.inl p)) (splitEquiv M (.inr q))=_
  rw [splitEquiv_inl,splitEquiv_inr,interior_row hM]
  have hne : p.val≠q.val := by
    intro h
    exact (Finset.mem_sdiff.mp q.property).2 (h ▸ p.property)
  simp only [hne,ite_false,Matrix.zero_apply]

theorem interior_det_pos (M : Diagram) : 0<(fourIminusAdjacency (interior M)).det :=
  (dirichlet_posDef (subset_enclosingSquare (interior M) 0)).det_pos

/-- Full actual quadrant determinant multiplied by the finite interior
Dirichlet determinant equals the actual northeast-boundary minor. -/
theorem det_mul_interior {M : Diagram} (hM : IsFerrers M) :
    (fourIminusAdjacency (interior M)).det*(minor M).det=(minor (boundary M)).det := by
  have h := QuadrantMinorReduction.det_from_interior_rows
    (fourIminusAdjacency (interior M)) (coupling M) (interiorGreen M)
    (interiorBoundaryGreen M) (boundaryInteriorGreen M) (boundaryGreen M)
    (interior_identity hM) (interior_boundary hM)
  rw [Matrix.fromBlocks_toBlocks,boundaryGreen_eq,splitGreen,Matrix.det_submatrix_equiv_self] at h
  exact h

/-- Appendix B's arbitrary-Ferrers determinant reduction, with all kernel,
indexing, geometry and invertibility premises discharged. -/
theorem determinant_reduction {M : Diagram} (hM : IsFerrers M) :
    (minor M).det=(minor (boundary M)).det/(fourIminusAdjacency (interior M)).det := by
  apply (eq_div_iff (interior_det_pos M).ne').mpr
  simpa only [mul_comm] using det_mul_interior hM

theorem boundary_det_pos {M : Diagram} (hM : IsFerrers M) : 0<(minor (boundary M)).det := by
  rw [← det_mul_interior hM]
  apply mul_pos (interior_det_pos M)
  exact quadrantMinor_det_pos hM (Equiv.refl _)

/-- The actual Schur complement of the northeast-boundary Green block is
the inverse of the finite interior Dirichlet matrix. -/
theorem schur_complement {M : Diagram} (hM : IsFerrers M) :
    interiorGreen M-interiorBoundaryGreen M*(boundaryGreen M)⁻¹*boundaryInteriorGreen M=
      (fourIminusAdjacency (interior M))⁻¹ := by
  let A := fourIminusAdjacency (interior M)
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr (interior_det_pos M).ne'
  have hB : IsUnit (boundaryGreen M).det := isUnit_iff_ne_zero.mpr (boundary_det_pos hM).ne'
  have hzero := interior_boundary hM
  have hAG : A*interiorBoundaryGreen M= -(coupling M*boundaryGreen M) :=
    eq_neg_of_add_eq_zero_left hzero
  have hprod : A*(interiorGreen M-interiorBoundaryGreen M*(boundaryGreen M)⁻¹*boundaryInteriorGreen M)=1 := by
    calc
      _=A*interiorGreen M-((A*interiorBoundaryGreen M)*(boundaryGreen M)⁻¹)*boundaryInteriorGreen M := by
        simp only [Matrix.mul_sub,Matrix.mul_assoc]
      _=A*interiorGreen M-((-(coupling M*boundaryGreen M))*(boundaryGreen M)⁻¹)*boundaryInteriorGreen M := by rw [hAG]
      _=A*interiorGreen M+coupling M*boundaryInteriorGreen M := by
        simp only [Matrix.neg_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hB,Matrix.mul_one,sub_neg_eq_add]
      _=1 := interior_identity hM
  calc
    _=A⁻¹*(A*(interiorGreen M-interiorBoundaryGreen M*(boundaryGreen M)⁻¹*boundaryInteriorGreen M)) := by
      rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hA,Matrix.one_mul]
    _=A⁻¹ := by rw [hprod,Matrix.mul_one]

/-- Energy expression using only the actual boundary Green minor and the
finite interior Dirichlet determinant. -/
theorem energy_reduction {M : Diagram} (hM : IsFerrers M) :
    realEnergy M= -Real.log ((minor (boundary M)).det/(fourIminusAdjacency (interior M)).det)-
      SquareMaximality.squareLatticeEntropy*M.card := by
  have h := energy_eq_log_det hM (Equiv.refl {p // p∈M})
  change realEnergy M= -Real.log (minor M).det-SquareMaximality.squareLatticeEntropy*M.card at h
  rw [determinant_reduction hM] at h
  exact h

end
end SpanningTreeIsoperimetry.GeneralQuadrantMinorReduction
