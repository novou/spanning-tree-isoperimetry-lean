import SquareMaximality.Multigraph.Events
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Hadamard--Fischer determinant inequalities

This module proves the finite-dimensional matrix inequality used by the
transfer-current argument in `general.tex`, equation
`forest-negative-correlation`.  It is independent of spanning-tree counting.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Multigraph
namespace HadamardFischer

open scoped BigOperators Matrix MatrixOrder

/-- A positive-semidefinite contraction has determinant at most one. -/
theorem det_le_one_of_posSemidef_one_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (hOneSub : (1 - A).PosSemidef) : Matrix.det A ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  have hprod : (∏ i, hA.isHermitian.eigenvalues i) ≤
      ∏ _i : n, (1 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _hi
      exact hA.eigenvalues_nonneg i
    · intro i _hi
      let v : n → ℝ := ⇑(hA.isHermitian.eigenvectorBasis i)
      have hquad := hOneSub.dotProduct_mulVec_nonneg v
      have heigen := hA.isHermitian.mulVec_eigenvectorBasis i
      have hnorm : star v ⬝ᵥ v = 1 := by
        rw [dotProduct_comm]
        exact hA.isHermitian.eigenvectorBasis.inner_eq_one i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, heigen, dotProduct_sub,
        dotProduct_smul, hnorm] at hquad
      simpa [v] using hquad
  simpa using hprod

/-- Determinant is monotone below a positive-definite upper matrix in the
Loewner order.  The proof normalizes by the positive square root of `D`. -/
theorem det_le_det_of_posSemidef_sub_of_posDef_right
    {n : Type*} [Fintype n] [DecidableEq n]
    {A D : Matrix n n ℝ} (hA : A.PosSemidef)
    (hSub : (D - A).PosSemidef) (hD : D.PosDef) :
    Matrix.det A ≤ Matrix.det D := by
  let P : Matrix n n ℝ := CFC.sqrt D
  have hDnonneg : 0 ≤ D := hD.posSemidef.nonneg
  have hPsq : P * P = D := by
    simpa only [P, pow_two] using CFC.sq_sqrt D hDnonneg
  have hPunit : IsUnit P := by
    exact (CFC.isUnit_sqrt_iff D hDnonneg).mpr hD.isUnit
  letI : Invertible P := hPunit.invertible
  let Q : Matrix n n ℝ := P⁻¹
  have hPstar : Pᴴ = P := by
    have h := (CFC.sqrt_nonneg D).star_eq
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hQstar : Qᴴ = Q := by
    simp only [Q, Matrix.conjTranspose_nonsing_inv, hPstar]
  have hQP : Q * P = 1 := by
    exact Matrix.inv_mul_of_invertible P
  have hPQ : P * Q = 1 := by
    exact Matrix.mul_inv_of_invertible P
  let T : Matrix n n ℝ := Q * A * Q
  have hT : T.PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same Q
    simpa only [T, hQstar] using h
  have hQDQ : Qᴴ * D * Q = 1 := by
    calc
      Qᴴ * D * Q = Q * (P * P) * Q := by rw [hQstar, hPsq]
      _ = (Q * P) * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, hPQ, one_mul]
  have hOneSub : (1 - T).PosSemidef := by
    have h := hSub.conjTranspose_mul_mul_same Q
    have heq : Qᴴ * (D - A) * Q = 1 - T := by
      calc
        Qᴴ * (D - A) * Q = Qᴴ * D * Q - Qᴴ * A * Q := by
          noncomm_ring
        _ = 1 - T := by rw [hQDQ]; simp only [T, hQstar]
    rwa [heq] at h
  have hTle : Matrix.det T ≤ 1 :=
    det_le_one_of_posSemidef_one_sub hT hOneSub
  have hPTP : P * T * P = A := by
    dsimp only [T]
    calc
      P * (Q * A * Q) * P = (P * Q) * A * (Q * P) := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hPQ, hQP, one_mul, mul_one]
  have hdet : Matrix.det A = Matrix.det D * Matrix.det T := by
    calc
      Matrix.det A = Matrix.det (P * T * P) :=
        congrArg Matrix.det hPTP.symm
      _ = Matrix.det P * Matrix.det T * Matrix.det P := by
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = (Matrix.det P * Matrix.det P) * Matrix.det T := by ring
      _ = Matrix.det (P * P) * Matrix.det T := by
        congr 1
        exact (Matrix.det_mul P P).symm
      _ = Matrix.det D * Matrix.det T := by rw [hPsq]
  rw [hdet]
  simpa using mul_le_mul_of_nonneg_left hTle hD.det_pos.le

/-- Two-block Hadamard--Fischer: a positive-semidefinite block matrix has
determinant at most the product of the two diagonal-block determinants. -/
theorem det_fromBlocks_le_det_mul_det
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    Matrix.det (Matrix.fromBlocks A B Bᴴ D) ≤
      Matrix.det A * Matrix.det D := by
  let M : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks A B Bᴴ D
  have hblockA : M.submatrix Sum.inl Sum.inl = A := by
    ext i j
    rfl
  have hblockD : M.submatrix Sum.inr Sum.inr = D := by
    ext i j
    rfl
  have hAsem : A.PosSemidef := by
    rw [← hblockA]
    exact hM.submatrix Sum.inl
  have hDsem : D.PosSemidef := by
    rw [← hblockD]
    exact hM.submatrix Sum.inr
  by_cases hdet : Matrix.det M = 0
  · change Matrix.det M ≤ Matrix.det A * Matrix.det D
    rw [hdet]
    exact mul_nonneg hAsem.det_nonneg hDsem.det_nonneg
  · have hMpos : M.PosDef := hM.posDef_iff_det_ne_zero.mpr hdet
    have hApos : A.PosDef := by
      rw [← hblockA]
      exact hMpos.submatrix Sum.inl_injective
    have hDpos : D.PosDef := by
      rw [← hblockD]
      exact hMpos.submatrix Sum.inr_injective
    letI : Invertible A := hApos.isUnit.invertible
    let S : Matrix n n ℝ := D - Bᴴ * A⁻¹ * B
    have hS : S.PosSemidef := by
      have h :=
        (Matrix.PosDef.fromBlocks₁₁ B D hApos).mp hM
      simpa only [S] using h
    have hSub : (D - S).PosSemidef := by
      have hcross := hApos.posSemidef.inv.conjTranspose_mul_mul_same B
      have heq : D - S = Bᴴ * A⁻¹ * B := by
        dsimp only [S]
        abel
      rw [heq]
      exact hcross
    have hdetSD : Matrix.det S ≤ Matrix.det D :=
      det_le_det_of_posSemidef_sub_of_posDef_right hS hSub hDpos
    change Matrix.det M ≤ Matrix.det A * Matrix.det D
    rw [show M = Matrix.fromBlocks A B Bᴴ D by rfl,
      Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    exact mul_le_mul_of_nonneg_left hdetSD hApos.det_pos.le

/-- Principal submatrix on a finite set of indices. -/
def principalSubmatrix {E : Type*} (K : Matrix E E ℝ)
    (F : Finset E) : Matrix {e // e ∈ F} {e // e ∈ F} ℝ :=
  K.submatrix Subtype.val Subtype.val

/-- Determinant of a finite principal submatrix, with classical decidable
equality kept internal to the definition. -/
noncomputable def principalDet {E : Type*} (K : Matrix E E ℝ)
    (F : Finset E) : ℝ := by
  classical
  exact Matrix.det (principalSubmatrix K F)

/-- Two-set principal-minor form of Hadamard--Fischer. -/
theorem det_principal_union_le
    {E : Type*} [Fintype E] [DecidableEq E]
    {K : Matrix E E ℝ} (hK : K.PosSemidef)
    (F H : Finset E) (hdisj : Disjoint F H) :
    Matrix.det (principalSubmatrix K (F ∪ H)) ≤
      Matrix.det (principalSubmatrix K F) *
        Matrix.det (principalSubmatrix K H) := by
  let e : ({x // x ∈ F} ⊕ {x // x ∈ H}) ≃ {x // x ∈ F ∪ H} :=
    Equiv.Finset.union F H hdisj
  let M := principalSubmatrix K (F ∪ H)
  let A := principalSubmatrix K F
  let D := principalSubmatrix K H
  let B : Matrix {x // x ∈ F} {x // x ∈ H} ℝ :=
    K.submatrix Subtype.val Subtype.val
  have hblocks : M.submatrix e e = Matrix.fromBlocks A B Bᴴ D := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j => rfl
        | inr j => rfl
    | inr i =>
        cases j with
        | inl j =>
            dsimp only [M, A, D, B, principalSubmatrix, e,
              Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
              Equiv.Finset.union_inl, Equiv.Finset.union_inr,
              Matrix.conjTranspose_apply, Matrix.transpose_apply,
              Matrix.map_apply]
            exact (hK.isHermitian.apply i.1 j.1).symm
        | inr j => rfl
  have hM : M.PosSemidef := by
    exact hK.submatrix Subtype.val
  have hblockSem : (Matrix.fromBlocks A B Bᴴ D).PosSemidef := by
    rw [← hblocks]
    exact hM.submatrix e
  have hineq := det_fromBlocks_le_det_mul_det hblockSem
  rw [← hblocks] at hineq
  have hdetReindex : Matrix.det (M.submatrix e e) = Matrix.det M :=
    Matrix.det_submatrix_equiv_self e M
  rw [hdetReindex] at hineq
  exact hineq

/-- Finite-family Hadamard--Fischer for pairwise disjoint principal blocks. -/
theorem det_principal_biUnion_le_prod
    {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    {K : Matrix E E ℝ} (hK : K.PosSemidef)
    (F : ι → Finset E)
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) :
    Matrix.det (principalSubmatrix K (Finset.univ.biUnion F)) ≤
      ∏ i, Matrix.det (principalSubmatrix K (F i)) := by
  classical
  have hfinite (s : Finset ι) :
      Matrix.det (principalSubmatrix K (s.biUnion F)) ≤
        ∏ i ∈ s, Matrix.det (principalSubmatrix K (F i)) := by
    induction s using Finset.induction_on with
    | empty =>
        letI : IsEmpty {e : E // e ∈ (∅ : Finset ι).biUnion F} := ⟨fun e => by
          obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp e.property
          exact Finset.notMem_empty i hi⟩
        have hdet : Matrix.det (principalSubmatrix K ((∅ : Finset ι).biUnion F)) = 1 :=
          Matrix.det_isEmpty
        rw [hdet]
        simp
    | @insert i s hi ih =>
        have hblockDisjoint : Disjoint (F i) (s.biUnion F) := by
          rw [Finset.disjoint_left]
          intro e hei heUnion
          obtain ⟨j, hjs, hej⟩ := Finset.mem_biUnion.mp heUnion
          have hij : i ≠ j := fun hij => hi (hij ▸ hjs)
          exact (Finset.disjoint_left.mp (hdisj hij)) hei hej
        have hFi : (principalSubmatrix K (F i)).PosSemidef :=
          hK.submatrix Subtype.val
        calc
          Matrix.det (principalSubmatrix K ((insert i s).biUnion F)) =
              Matrix.det (principalSubmatrix K (F i ∪ s.biUnion F)) := by
            rw [Finset.biUnion_insert]
          _ ≤ Matrix.det (principalSubmatrix K (F i)) *
              Matrix.det (principalSubmatrix K (s.biUnion F)) :=
            det_principal_union_le hK (F i) (s.biUnion F) hblockDisjoint
          _ ≤ Matrix.det (principalSubmatrix K (F i)) *
              ∏ j ∈ s, Matrix.det (principalSubmatrix K (F j)) :=
            mul_le_mul_of_nonneg_left ih hFi.det_nonneg
          _ = ∏ j ∈ insert i s,
              Matrix.det (principalSubmatrix K (F j)) := by
            rw [Finset.prod_insert hi]
  simpa using hfinite Finset.univ

/-- Instance-independent form of the finite-family inequality. -/
theorem principalDet_unionEdgeBlocks_le_prod
    {E ι : Type*} [Fintype E] [Fintype ι]
    {K : Matrix E E ℝ} (hK : K.PosSemidef)
    (F : ι → Finset E)
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) :
    principalDet K (LabeledMultigraph.unionEdgeBlocks F) ≤
      ∏ i, principalDet K (F i) := by
  classical
  unfold LabeledMultigraph.unionEdgeBlocks principalDet
  exact det_principal_biUnion_le_prod hK F hdisj

end HadamardFischer
end Multigraph
end SquareMaximality
