module

public import SpanningTreeIsoperimetry.CornerDeterminant
public import SpanningTreeIsoperimetry.SmallCases
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option backward.privateInPublic true

/-! The actual rectangular Dirichlet inverse and its scalar moment minors.
No layer-resolvent formula or Hankel determinant identity is assumed. -/
namespace SpanningTreeIsoperimetry.ScalarResolvent

open scoped BigOperators Matrix Kronecker Classical
open SquareMaximality.Boundary
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def pathOperator (w : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  (4 : ℝ) • 1 - (SimpleGraph.pathGraph w).adjMatrix ℝ

theorem pathOperator_apply (w : ℕ) (i j : Fin w) :
    pathOperator w i j = (if i = j then 4 else 0) -
      (if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then 1 else 0) := by
  simp [pathOperator, SimpleGraph.adjMatrix, SimpleGraph.pathGraph_adj, Matrix.one_apply]

theorem pathOperator_below {w : ℕ} (i j : Fin w) (h : j.1 + 1 < i.1) :
    pathOperator w i j = 0 := by
  rw [pathOperator_apply]
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  simp [hij, show ¬(i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) by omega]

theorem pathOperator_isSymm (w : ℕ) : (pathOperator w).IsSymm := by
  rw [Matrix.IsSymm, pathOperator, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, (SimpleGraph.pathGraph w).isSymm_adjMatrix]

/-- No power can travel farther than its exponent along the path. -/
theorem pathPower_support {w : ℕ} (hw : 0 < w) (n : ℕ) (i : Fin w) (hi : n < i.1) :
    (pathOperator w ^ n) i ⟨0, hw⟩ = 0 := by
  induction n generalizing i with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [ite_eq_right (by
      intro he
      have hval : i.1 = 0 := congrArg Fin.val he
      omega)]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : n < j.1
    · rw [ih j hj, mul_zero]
    · rw [pathOperator_below i j (by omega), zero_mul]

/-- At the propagation frontier there is exactly one path, with sign `(-1)^n`. -/
theorem pathPower_frontier {w : ℕ} (hw : 0 < w) (n : ℕ) (hn : n < w) :
    (pathOperator w ^ n) ⟨n, hn⟩ ⟨0, hw⟩ = (-1 : ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < w := by omega
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single (⟨n, hn'⟩ : Fin w)]
    · have hentry : pathOperator w ⟨n + 1, hn⟩ ⟨n, hn'⟩ = -1 := by
        rw [pathOperator_apply]
        have hne : (⟨n + 1, hn⟩ : Fin w) ≠ ⟨n, hn'⟩ := by
          intro h; have hval : n + 1 = n := congrArg Fin.val h; omega
        simp [hne]
      rw [hentry, ih hn']
      simp [pow_succ, mul_comm]
    · intro j _ hj
      have hjval : j.1 ≠ n := by intro h; exact hj (Fin.ext h)
      by_cases hlt : n < j.1
      · rw [pathPower_support hw n j hlt, mul_zero]
      · rw [pathOperator_below _ _ (by change j.1 + 1 < n + 1; omega), zero_mul]
    · simp

noncomputable def krylov {w k : ℕ} (hw : 0 < w) : Matrix (Fin w) (Fin k) ℝ :=
  fun i j => (pathOperator w ^ j.1) i ⟨0, hw⟩

noncomputable def krylovLeading {w k : ℕ} (hw : 0 < w) (hk : k ≤ w) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (pathOperator w ^ j.1) (Fin.castLE hk i) ⟨0, hw⟩

theorem krylovLeading_upperTriangular {w k : ℕ} (hw : 0 < w) (hk : k ≤ w) :
    (krylovLeading hw hk).IsUpperTriangular := by
  intro i j hji
  exact pathPower_support hw j.1 (Fin.castLE hk i) hji

theorem krylovLeading_diagonal {w k : ℕ} (hw : 0 < w) (hk : k ≤ w) (i : Fin k) :
    krylovLeading hw hk i i = (-1 : ℝ)^i.1 :=
  pathPower_frontier hw i.1 (i.2.trans_le hk)

theorem krylovLeading_det_sq {w k : ℕ} (hw : 0 < w) (hk : k ≤ w) :
    (krylovLeading hw hk).det^2 = 1 := by
  have habs : |(krylovLeading hw hk).det| = 1 := by
    rw [Matrix.det_of_isUpperTriangular (krylovLeading_upperTriangular hw hk), Finset.abs_prod]
    simp only [krylovLeading_diagonal, abs_pow, abs_neg, abs_one, one_pow, Finset.prod_const_one]
  nlinarith [sq_abs (krylovLeading hw hk).det]

noncomputable def leadingEmbedding {w k : ℕ} (hk : k ≤ w) : Matrix (Fin w) (Fin k) ℝ :=
  fun i j => if i = Fin.castLE hk j then 1 else 0

theorem leadingEmbedding_gram {w k : ℕ} (hk : k ≤ w) (G : Matrix (Fin w) (Fin w) ℝ) :
    (leadingEmbedding hk)ᵀ * G * leadingEmbedding hk =
      G.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  ext i j
  simp [leadingEmbedding, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]

theorem krylov_factor {w k : ℕ} (hw : 0 < w) (hk : k ≤ w) :
    krylov (k := k) hw = leadingEmbedding hk * krylovLeading hw hk := by
  ext i j
  by_cases hi : i.1 < k
  · let i' : Fin k := ⟨i.1, hi⟩
    have heq : i = Fin.castLE hk i' := Fin.ext rfl
    rw [heq]
    simp [Matrix.mul_apply, leadingEmbedding, krylov, krylovLeading, Fin.castLE_inj]
  · have hzero : krylov (k := k) hw i j = 0 := pathPower_support hw j.1 i (by omega)
    rw [hzero, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro t _
    have hne : i ≠ Fin.castLE hk t := by
      intro h
      have hval : i.1 = t.1 := congrArg Fin.val h
      have := t.2
      omega
    simp [leadingEmbedding, hne]

noncomputable def moment {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (n : ℕ) : ℝ :=
  (G * pathOperator w ^ n) ⟨0, hw⟩ ⟨0, hw⟩

noncomputable def hankel {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j => moment hw G (i.1 + j.1)

/-- The Krylov Gram matrix is the actual moment Hankel matrix. -/
theorem krylov_gram_eq_hankel {w k : ℕ} (hw : 0 < w)
    (G : Matrix (Fin w) (Fin w) ℝ) (hcomm : Commute G (pathOperator w)) :
    (krylov (k := k) hw)ᵀ * G * krylov hw = hankel hw G k := by
  ext i j
  have hsym (n : ℕ) (a b : Fin w) : (pathOperator w ^ n) a b = (pathOperator w ^ n) b a :=
    congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M b a) ((pathOperator_isSymm w).pow n)
  calc
    _ = (pathOperator w ^ i.1 * G * pathOperator w ^ j.1) ⟨0, hw⟩ ⟨0, hw⟩ := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, krylov]
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [hsym i.1 x ⟨0, hw⟩]
    _ = (G * pathOperator w ^ (i.1 + j.1)) ⟨0, hw⟩ ⟨0, hw⟩ := by
      rw [← (hcomm.pow_right i.1).eq, Matrix.mul_assoc, ← pow_add]
    _ = _ := rfl

/-- Every leading Green minor is a Hankel determinant whenever the boundary
block commutes with the path operator. The actual block is supplied below. -/
theorem hankel_determinant_of_commute {w k : ℕ} (hw : 0 < w) (hk : k ≤ w)
    (G : Matrix (Fin w) (Fin w) ℝ) (hcomm : Commute G (pathOperator w)) :
    (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = (hankel hw G k).det := by
  have hgram := krylov_gram_eq_hankel (k := k) hw G hcomm
  rw [krylov_factor hw hk, Matrix.transpose_mul] at hgram
  have hrew :
      (krylovLeading hw hk)ᵀ * (G.submatrix (Fin.castLE hk) (Fin.castLE hk)) * krylovLeading hw hk =
        hankel hw G k := by
    rw [← leadingEmbedding_gram hk G]
    simpa only [Matrix.mul_assoc] using hgram
  have hdet := congrArg Matrix.det hrew
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hs := krylovLeading_det_sq hw hk
  calc
    _ = (krylovLeading hw hk).det^2 * (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by rw [hs, one_mul]
    _ = (krylovLeading hw hk).det * (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).det *
        (krylovLeading hw hk).det := by ring
    _ = _ := hdet

/-- The actual rectangular Dirichlet operator in layer coordinates. -/
noncomputable def rectangleDirichlet (R w : ℕ) : Matrix (Fin R × Fin w) (Fin R × Fin w) ℝ :=
  (1 : Matrix (Fin R) (Fin R) ℝ) ⊗ₖ pathOperator w -
    (SimpleGraph.pathGraph R).adjMatrix ℝ ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℝ)

theorem rectangleDirichlet_eq_grid (R w : ℕ) :
    rectangleDirichlet R w =
      (4 : ℝ) • 1 - ((SimpleGraph.pathGraph R) □ (SimpleGraph.pathGraph w)).adjMatrix ℝ := by
  ext p q
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases hij : i = j <;> by_cases hxy : x = y <;>
    simp [rectangleDirichlet, pathOperator, Matrix.kronecker_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix, SimpleGraph.boxProd_adj, hij, hxy]

/-- Layer coordinates identify the rectangle with its actual bounded faces. -/
def rectangleFacesEquiv (R w : ℕ) : (Fin R × Fin w) ≃ {p // p ∈ faceIndices R w} where
  toFun p := ⟨(p.1.1, p.2.1), mem_faceIndices.mpr ⟨by have := p.1.2; omega, by have := p.2.2; omega⟩⟩
  invFun p := (⟨p.1.1, by have := (mem_faceIndices.mp p.2).1; omega⟩,
    ⟨p.1.2, by have := (mem_faceIndices.mp p.2).2; omega⟩)
  left_inv p := by apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv p := by apply Subtype.ext; rfl

def rectangleFaceGraphIso (R w : ℕ) :
    (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph w) ≃g faceGraph (faceIndices R w) :=
  { rectangleFacesEquiv R w with
    map_rel_iff' := by
      intro p q
      change Nat.dist p.1.1 q.1.1 + Nat.dist p.2.1 q.2.1 = 1 ↔
        (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph w).Adj p q
      simp only [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff]
      unfold Nat.dist
      omega }

theorem rectangleDirichlet_eq_faceMatrix (R w : ℕ) :
    rectangleDirichlet R w = (fourIminusAdjacency (faceIndices R w)).submatrix
      (rectangleFacesEquiv R w) (rectangleFacesEquiv R w) := by
  rw [rectangleDirichlet_eq_grid]
  ext i j
  have heq := (rectangleFacesEquiv R w).injective.eq_iff (a := i) (b := j)
  have hadj := (rectangleFaceGraphIso R w).map_adj_iff (v := i) (w := j)
  simp only [fourIminusAdjacency, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  change 4 * (if i = j then 1 else 0) -
      (if (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph w).Adj i j then 1 else 0) =
    4 * (if rectangleFacesEquiv R w i = rectangleFacesEquiv R w j then 1 else 0) -
      (if (faceGraph (faceIndices R w)).Adj (rectangleFacesEquiv R w i) (rectangleFacesEquiv R w j) then 1 else 0)
  change (faceGraph (faceIndices R w)).Adj (rectangleFacesEquiv R w i) (rectangleFacesEquiv R w j) ↔
    (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph w).Adj i j at hadj
  simp only [heq, hadj]

/-- Positivity and invertibility come from the proved finite-face spectral bound. -/
theorem rectangleDirichlet_posDef (R w : ℕ) : (rectangleDirichlet R w).PosDef := by
  rw [rectangleDirichlet_eq_faceMatrix]
  apply (CornerEnergy.dirichlet_posDef (m := R) (n := w)
    (U := faceIndices R w) ?_).submatrix (rectangleFacesEquiv R w).injective
  rw [CornerEnergy.foundation_faceIndices]

theorem rectangleDirichlet_commute_layers (R w : ℕ) :
    Commute (rectangleDirichlet R w) ((1 : Matrix (Fin R) (Fin R) ℝ) ⊗ₖ pathOperator w) := by
  change (_ - _) * _ = _ * (_ - _)
  rw [sub_mul, mul_sub]
  congr 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- Commutation passes to the total nonsingular matrix inverse, including
its zero value at a nonunit matrix. -/
theorem commute_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (h : Commute A B) : Commute A⁻¹ B := by
  rcases A.nonsing_inv_cancel_or_zero with ⟨hl, hr⟩ | hz
  · change A⁻¹ * B = B * A⁻¹
    calc
      A⁻¹ * B = A⁻¹ * (B * (A * A⁻¹)) := by rw [hr, Matrix.mul_one]
      _ = A⁻¹ * ((B * A) * A⁻¹) := by rw [Matrix.mul_assoc B A A⁻¹]
      _ = A⁻¹ * ((A * B) * A⁻¹) := by rw [h.eq]
      _ = (A⁻¹ * A) * B * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B * A⁻¹ := by rw [hl, Matrix.one_mul]
  · rw [hz]
    exact Commute.zero_left _

noncomputable def boundaryGreen {R : ℕ} (hR : 0 < R) (w : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  (rectangleDirichlet R w)⁻¹.submatrix (fun i => (⟨0, hR⟩, i)) (fun i => (⟨0, hR⟩, i))

/-- The actual boundary inverse block commutes with the path operator. -/
theorem boundaryGreen_commute {R : ℕ} (hR : 0 < R) (w : ℕ) :
    Commute (boundaryGreen hR w) (pathOperator w) := by
  have hc := (commute_inverse _ _ (rectangleDirichlet_commute_layers R w)).eq
  change _ = _
  ext i j
  have h := congrArg (fun M : Matrix (Fin R × Fin w) (Fin R × Fin w) ℝ =>
    M (⟨0, hR⟩, i) (⟨0, hR⟩, j)) hc
  simpa [boundaryGreen, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type] using h

theorem boundaryGreen_posDef {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (boundaryGreen hR w).PosDef := by
  apply (Matrix.posDef_inv_iff.mpr (rectangleDirichlet_posDef R w)).submatrix
  intro i j h
  exact congrArg Prod.snd h

/-- Hankel representation for every leading block of the actual rectangular
Dirichlet inverse, including the empty minor. -/
theorem boundaryGreen_hankel_determinant {R w k : ℕ}
    (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    ((boundaryGreen hR w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      (hankel hw (boundaryGreen hR w) k).det :=
  hankel_determinant_of_commute hw hk _ (boundaryGreen_commute hR w)

/-- The actual moment Hankel determinants are positive throughout the full
width, not merely formal determinants of a chosen sequence. -/
theorem boundaryGreen_hankel_det_pos {R w k : ℕ}
    (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    0 < (hankel hw (boundaryGreen hR w) k).det := by
  rw [← boundaryGreen_hankel_determinant hR hw hk]
  exact ((boundaryGreen_posDef hR w).submatrix (Fin.castLE_injective hk)).det_pos

section Continuant
variable {K : Type*} [CommRing K]

/-- Constant-diagonal path matrix with unit off-diagonal entries. -/
def continuantMatrix (n : ℕ) (x : K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then x else if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then 1 else 0

theorem continuantMatrix_tail (n : ℕ) (x : K) :
    (continuantMatrix (n + 1) x).submatrix Fin.succ Fin.succ = continuantMatrix n x := by
  ext i j
  simp [continuantMatrix, Matrix.submatrix_apply, Fin.ext_iff]

private theorem skipOne_zero (n : ℕ) : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  apply Fin.succAbove_ne_zero_zero
  intro h
  have hh : (1 : ℕ) = 0 := congrArg Fin.val h
  omega

private theorem skipOne_succ {n : ℕ} (i : Fin n) :
    (1 : Fin (n + 2)).succAbove i.succ = i.succ.succ := by
  apply Fin.succAbove_of_le_castSucc
  change 1 ≤ i.1 + 1
  omega

private theorem continuantMatrix_far {n : ℕ} (x : K) (i j : Fin n)
    (h : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) : continuantMatrix n x i j = 0 := by
  unfold continuantMatrix
  split_ifs with he ha
  · have hv := congrArg Fin.val he
    omega
  · omega
  · rfl

private theorem continuant_second_minor (n : ℕ) (x : K) :
    ((continuantMatrix (n + 2) x).submatrix Fin.succ (Fin.succAbove 1)).det =
      (continuantMatrix n x).det := by
  let M := (continuantMatrix (n + 2) x).submatrix Fin.succ (Fin.succAbove 1)
  have h00 : M 0 0 = 1 := by simp [M, skipOne_zero, continuantMatrix, Fin.ext_iff]
  have hzero (i : Fin n) : M i.succ 0 = 0 := by
    change continuantMatrix (n + 2) x i.succ.succ ((1 : Fin (n + 2)).succAbove 0) = 0
    rw [skipOne_zero]
    apply continuantMatrix_far
    right
    change 0 + 1 < i.1 + 1 + 1
    omega
  have hminor : M.submatrix Fin.succ Fin.succ = continuantMatrix n x := by
    ext i j
    change continuantMatrix (n + 2) x i.succ.succ ((1 : Fin (n + 2)).succAbove j.succ) = _
    rw [skipOne_succ]
    simp [continuantMatrix, Fin.ext_iff]
  change M.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h00, hzero, hminor]

/-- The determinant recurrence is proved by two Laplace expansions. -/
theorem continuantMatrix_det_recurrence (n : ℕ) (x : K) :
    (continuantMatrix (n + 2) x).det =
      x * (continuantMatrix (n + 1) x).det - (continuantMatrix n x).det := by
  have h00 : continuantMatrix (n + 2) x 0 0 = x := by simp [continuantMatrix]
  have h01 : continuantMatrix (n + 2) x 0 1 = 1 := by simp [continuantMatrix, Fin.ext_iff]
  have hzero (i : Fin n) : continuantMatrix (n + 2) x 0 i.succ.succ = 0 := by
    apply continuantMatrix_far
    left
    change 0 + 1 < i.1 + 1 + 1
    omega
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [h00, h01, hzero, continuantMatrix_tail, continuant_second_minor, sub_eq_add_neg]

/-- The manuscript continuants are actual tridiagonal determinants. -/
theorem continuantMatrix_det (n : ℕ) (x : K) :
    (continuantMatrix n x).det = SmallCases.continuant x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [SmallCases.continuant]
  | one => simp [continuantMatrix, Matrix.det_fin_one, SmallCases.continuant]
  | more n ih ih1 =>
    rw [continuantMatrix_det_recurrence, ih, ih1, SmallCases.continuant_recurrence]

end Continuant

/-- The actual path resolvent has the manuscript's constant-diagonal matrix. -/
theorem shifted_pathOperator (w : ℕ) (z : ℝ) :
    z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w = continuantMatrix w (z - 4) := by
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, pathOperator_apply]
  by_cases hij : i = j
  · subst j
    simp [continuantMatrix]
  · simp only [hij, ite_eq_right, mul_zero, continuantMatrix]
    split_ifs <;> simp_all

/-- The denominator is computed from the actual resolvent matrix. -/
theorem shifted_pathOperator_det (w : ℕ) (z : ℝ) :
    (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w).det =
      SmallCases.continuant (z - 4) w := by
  rw [shifted_pathOperator, continuantMatrix_det]

/-- The endpoint resolvent is the ratio of successive continuants. This
identity is proved from the actual inverse and its cofactor. -/
theorem endpoint_resolvent (n : ℕ) (z : ℝ) :
    ((z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - pathOperator (n + 1))⁻¹) 0 0 =
      SmallCases.continuant (z - 4) n / SmallCases.continuant (z - 4) (n + 1) := by
  rw [shifted_pathOperator, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero,
    continuantMatrix_tail, continuantMatrix_det, Ring.inverse_eq_inv]
  ring

/-- The concrete denominator polynomial in the manuscript. -/
noncomputable def pathPolynomial (w : ℕ) : Polynomial ℝ :=
  SmallCases.continuant (Polynomial.X - Polynomial.C 4) w

theorem eval_continuant (p : Polynomial ℝ) (z : ℝ) (n : ℕ) :
    (SmallCases.continuant p n).eval z = SmallCases.continuant (p.eval z) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [SmallCases.continuant]
  | one => simp [SmallCases.continuant]
  | more n ih ih1 => simp only [SmallCases.continuant_recurrence, Polynomial.eval_sub,
      Polynomial.eval_mul, ih, ih1]

theorem pathPolynomial_eval (w : ℕ) (z : ℝ) :
    (pathPolynomial w).eval z = SmallCases.continuant (z - 4) w := by
  simp [pathPolynomial, eval_continuant]

/-- `P=f_w(X-4)` is the actual characteristic polynomial of the path operator. -/
theorem pathOperator_charpoly (w : ℕ) : (pathOperator w).charpoly = pathPolynomial w := by
  apply Polynomial.funext
  intro z
  rw [Matrix.eval_charpoly, pathPolynomial_eval]
  have hscalar : Matrix.scalar (Fin w) z = z • (1 : Matrix (Fin w) (Fin w) ℝ) := by
    ext i j
    simp [Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply]
  rw [hscalar, shifted_pathOperator_det]

theorem pathPolynomial_monic (w : ℕ) : (pathPolynomial w).Monic := by
  rw [← pathOperator_charpoly]
  exact Matrix.charpoly_monic _

theorem pathPolynomial_natDegree (w : ℕ) : (pathPolynomial w).natDegree = w := by
  rw [← pathOperator_charpoly, Matrix.charpoly_natDegree_eq_dim]
  simp

/-- Proper scalar numerator extracted from the actual Green block and the
adjugate of the characteristic matrix. Its equality with the modular
continuant construction is a separate subsequent identity. -/
noncomputable def weightedNumerator {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) :
    Polynomial ℝ :=
  ∑ j : Fin w, Polynomial.C (G ⟨0, hw⟩ j) * (pathOperator w).charmatrix.adjugate j ⟨0, hw⟩

theorem eval_charmatrix (w : ℕ) (z : ℝ) :
    (Polynomial.evalRingHom z).mapMatrix (pathOperator w).charmatrix =
      z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply]
  · simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem weightedNumerator_eval {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (z : ℝ) :
    (weightedNumerator hw G).eval z =
      (G * (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w).adjugate) ⟨0, hw⟩ ⟨0, hw⟩ := by
  have hm := (Polynomial.evalRingHom z).map_adjugate (pathOperator w).charmatrix
  rw [eval_charmatrix] at hm
  simp only [weightedNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M j ⟨0, hw⟩) hm

private theorem adjugate_charmatrix_degree {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    (B.charmatrix.adjugate i j).natDegree ≤ n := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix j.succAbove i.succAbove
  let C : Matrix (Fin n) (Fin n) ℝ := (-B).submatrix j.succAbove i.succAbove
  have hlin : B.charmatrix.submatrix j.succAbove i.succAbove =
      (Polynomial.X : Polynomial ℝ) • A.map (Polynomial.C : ℝ → Polynomial ℝ) +
        C.map (Polynomial.C : ℝ → Polynomial ℝ) := by
    ext a b
    by_cases hab : j.succAbove a = i.succAbove b <;>
      simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal_apply, Matrix.submatrix_apply,
        Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, A, C, hab] <;> ring
  have hminor : (B.charmatrix.submatrix j.succAbove i.succAbove).det.natDegree ≤ n := by
    rw [hlin]
    simpa using Polynomial.natDegree_det_X_add_C_le A C
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsign : (-1 : Polynomial ℝ)^(j.1 + i.1) = Polynomial.C ((-1 : ℝ)^(j.1 + i.1)) := by simp
  rw [hsign]
  exact (Polynomial.natDegree_C_mul_le _ _).trans hminor

/-- The scalar numerator is proper: its degree is smaller than the width. -/
theorem weightedNumerator_natDegree_lt {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) :
    (weightedNumerator hw G).natDegree < w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  apply lt_of_le_of_lt _ (Nat.lt_succ_self n)
  unfold weightedNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (adjugate_charmatrix_degree _ j ⟨0, hw⟩)

/-- Scalar resolvent representation with a computed proper numerator and the
explicit continuant denominator. The numerator uses the actual Green block. -/
theorem weighted_resolvent_ratio {w : ℕ} (hw : 0 < w) (G : Matrix (Fin w) (Fin w) ℝ) (z : ℝ) :
    (G * (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩ =
      (weightedNumerator hw G).eval z / (pathPolynomial w).eval z := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul,
    ← weightedNumerator_eval, shifted_pathOperator_det, pathPolynomial_eval]
  ring

/-- The preceding scalar formula specialized to the actual rectangle inverse. -/
theorem boundaryGreen_scalar_resolvent {R w : ℕ} (hR : 0 < R) (hw : 0 < w) (z : ℝ) :
    (boundaryGreen hR w * (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩ =
      (weightedNumerator hw (boundaryGreen hR w)).eval z / (pathPolynomial w).eval z :=
  weighted_resolvent_ratio hw _ z

/-- Away from the displayed denominator's zeros, the total matrix inverse
used above is the ordinary inverse of the resolvent matrix. -/
theorem resolvent_mul_inverse (w : ℕ) (z : ℝ) (hz : (pathPolynomial w).eval z ≠ 0) :
    (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w) *
      (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  apply isUnit_iff_ne_zero.mpr
  rwa [shifted_pathOperator_det, ← pathPolynomial_eval]

/-- Continuants evaluated at the path operator, defined directly in its
noncommutative matrix ring. -/
noncomputable def operatorContinuant (w : ℕ) : ℕ → Matrix (Fin w) (Fin w) ℝ
  | 0 => 1
  | 1 => pathOperator w
  | n + 2 => pathOperator w * operatorContinuant w (n + 1) - operatorContinuant w n

@[simp] theorem operatorContinuant_zero (w : ℕ) : operatorContinuant w 0 = 1 := rfl
@[simp] theorem operatorContinuant_one (w : ℕ) : operatorContinuant w 1 = pathOperator w := rfl

theorem operatorContinuant_recurrence (w n : ℕ) :
    operatorContinuant w (n + 2) =
      pathOperator w * operatorContinuant w (n + 1) - operatorContinuant w n := rfl

/-- Finite nearest-neighbor summation, including both endpoints. -/
theorem path_neighbor_sum {M : Type*} [AddCommMonoid M] {R : ℕ}
    (f : Fin R → M) (i : Fin R) :
    (∑ j : Fin R, if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then f j else 0) =
      (if hn : i.1 + 1 < R then f ⟨i.1 + 1, hn⟩ else 0) +
      (if hp : 0 < i.1 then f ⟨i.1 - 1, by have := i.2; omega⟩ else 0) := by
  have hsplit (j : Fin R) :
      (if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then f j else 0) =
        (if i.1 + 1 = j.1 then f j else 0) + (if j.1 + 1 = i.1 then f j else 0) := by
    by_cases ha : i.1 + 1 = j.1 <;> by_cases hb : j.1 + 1 = i.1
    · omega
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  · split_ifs with hn
    · have he (j : Fin R) : i.1 + 1 = j.1 ↔ j = ⟨i.1 + 1, hn⟩ := by
        rw [Fin.ext_iff]
        change i.1 + 1 = j.1 ↔ j.1 = i.1 + 1
        omega
      simp_rw [he]
      simp
    · have he (j : Fin R) : ¬i.1 + 1 = j.1 := by have := j.2; omega
      simp [he]
  · split_ifs with hp
    · have he (j : Fin R) : j.1 + 1 = i.1 ↔ j = ⟨i.1 - 1, by have := i.2; omega⟩ := by
        rw [Fin.ext_iff]
        change j.1 + 1 = i.1 ↔ j.1 = i.1 - 1
        omega
      simp_rw [he]
      simp
    · have he (j : Fin R) : ¬j.1 + 1 = i.1 := by omega
      simp [he]

private theorem reverseContinuant_step (w : ℕ) {R : ℕ} (i : Fin R) :
    pathOperator w * operatorContinuant w (R - 1 - i.1) -
      ((if hn : i.1 + 1 < R then operatorContinuant w (R - 1 - (i.1 + 1)) else 0) +
       (if hp : 0 < i.1 then operatorContinuant w (R - 1 - (i.1 - 1)) else 0)) =
      if i.1 = 0 then operatorContinuant w R else 0 := by
  have hiR := i.2
  by_cases hi : i.1 = 0
  · by_cases hR : R = 1
    · simp [hi, hR]
    · have hR2 : 2 ≤ R := by omega
      have hrec := operatorContinuant_recurrence w (R - 2)
      rw [show R - 2 + 2 = R by omega, show R - 2 + 1 = R - 1 by omega] at hrec
      simp only [hi, zero_add, Nat.sub_zero, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      rw [dite_eq_left (by omega : 1 < R), show R - 1 - 1 = R - 2 by omega, add_zero]
      exact hrec.symm
  · have hip : 0 < i.1 := by omega
    by_cases hn : i.1 + 1 < R
    · let m := R - 2 - i.1
      have h0 : R - 1 - i.1 = m + 1 := by dsimp [m]; omega
      have hnext : R - 1 - (i.1 + 1) = m := by dsimp [m]; omega
      have hprev : R - 1 - (i.1 - 1) = m + 2 := by dsimp [m]; omega
      rw [dite_eq_left hn, dite_eq_left hip, ite_eq_right hi, h0, hnext, hprev, operatorContinuant_recurrence]
      abel
    · have h0 : R - 1 - i.1 = 0 := by omega
      have hprev : R - 1 - (i.1 - 1) = 1 := by omega
      simp [hn, hip, hi, h0, hprev]

noncomputable def harmonicColumn (R w : ℕ) : Matrix (Fin R × Fin w) (Fin w) ℝ :=
  fun i j => operatorContinuant w (R - 1 - i.1.1) i.2 j

noncomputable def firstLayer {R : ℕ} (hR : 0 < R) (w : ℕ) :
    Matrix (Fin R × Fin w) (Fin w) ℝ :=
  fun i j => if i.1 = ⟨0, hR⟩ then (1 : Matrix (Fin w) (Fin w) ℝ) i.2 j else 0

private theorem rectangleDirichlet_mul_layers (R w : ℕ)
    (F : Fin R → Matrix (Fin w) (Fin w) ℝ) (i : Fin R) (x y : Fin w) :
    (rectangleDirichlet R w * (Matrix.of (fun (j : Fin R × Fin w) (z : Fin w) => F j.1 j.2 z))) (i, x) y =
      (pathOperator w * F i - ∑ j : Fin R,
        if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then F j else 0) x y := by
  simp [rectangleDirichlet, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, sub_mul, Finset.sum_sub_distrib,
    SimpleGraph.adjMatrix, SimpleGraph.pathGraph_adj, Matrix.sum_apply, Matrix.ite_apply, mul_ite, ite_mul,
    Finset.mul_sum]

/-- The reversed continuant column solves the rectangular layer equations. -/
theorem rectangleDirichlet_harmonicColumn {R : ℕ} (hR : 0 < R) (w : ℕ) :
    rectangleDirichlet R w * harmonicColumn R w = firstLayer hR w * operatorContinuant w R := by
  ext p y
  rcases p with ⟨i, x⟩
  let F : Fin R → Matrix (Fin w) (Fin w) ℝ := fun j => operatorContinuant w (R - 1 - j.1)
  calc
    _ = (pathOperator w * F i - ∑ j : Fin R,
        if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then F j else 0) x y :=
      rectangleDirichlet_mul_layers R w F i x y
    _ = _ := by
      rw [path_neighbor_sum]
      have h := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M x y) (reverseContinuant_step w i)
      have he : i = (⟨0, hR⟩ : Fin R) ↔ i.1 = 0 := Fin.ext_iff
      simpa [F, firstLayer, Matrix.mul_apply, Matrix.one_apply, Matrix.ite_apply, he] using h

private theorem inverse_firstLayer_block {R : ℕ} (hR : 0 < R) (w : ℕ)
    (M : Matrix (Fin R × Fin w) (Fin R × Fin w) ℝ)
    (F : Matrix (Fin w) (Fin w) ℝ) (i : Fin R) :
    (M * (firstLayer hR w * F)).submatrix (fun x => (i, x)) id =
      M.submatrix (fun x => (i, x)) (fun y => (⟨0, hR⟩, y)) * F := by
  ext x y
  simp [Matrix.mul_apply, Matrix.submatrix_apply, firstLayer, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul]

/-- Positivity of the actual Dirichlet operator turns the continuant column
into an inverse-matrix identity. -/
theorem harmonicColumn_eq_inverse {R : ℕ} (hR : 0 < R) (w : ℕ) :
    harmonicColumn R w = (rectangleDirichlet R w)⁻¹ *
      (firstLayer hR w * operatorContinuant w R) := by
  have hu : IsUnit (rectangleDirichlet R w).det :=
    isUnit_iff_ne_zero.mpr (rectangleDirichlet_posDef R w).det_pos.ne'
  symm
  calc
    _ = (rectangleDirichlet R w)⁻¹ * (rectangleDirichlet R w * harmonicColumn R w) := by
      rw [rectangleDirichlet_harmonicColumn hR w]
    _ = harmonicColumn R w := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- Every block in the first Green column satisfies the same continuant
identity. The last block supplies invertibility of `f_R(B)`. -/
theorem green_first_column_continuant {R : ℕ} (hR : 0 < R) (w : ℕ) (i : Fin R) :
    ((rectangleDirichlet R w)⁻¹.submatrix (fun x => (i, x)) (fun y => (⟨0, hR⟩, y))) *
      operatorContinuant w R = operatorContinuant w (R - 1 - i.1) := by
  have h := congrArg (fun M : Matrix (Fin R × Fin w) (Fin w) ℝ =>
    M.submatrix (fun x => (i, x)) id) (harmonicColumn_eq_inverse hR w)
  rw [inverse_firstLayer_block] at h
  exact h.symm

/-- The operator continuant is invertible because it has an explicit inverse
block furnished by the actual Dirichlet Green matrix. -/
theorem operatorContinuant_det_ne_zero {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (operatorContinuant w R).det ≠ 0 := by
  let last : Fin R := ⟨R - 1, by omega⟩
  have h := green_first_column_continuant hR w last
  simp only [last, Nat.sub_self, operatorContinuant_zero] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  rw [hz, mul_zero] at hd
  norm_num at hd

/-- The manuscript's boundary layer formula for the actual Green block. -/
theorem boundaryGreen_eq_continuants {R : ℕ} (hR : 0 < R) (w : ℕ) :
    boundaryGreen hR w = operatorContinuant w (R - 1) * (operatorContinuant w R)⁻¹ := by
  have h := green_first_column_continuant hR w ⟨0, hR⟩
  change boundaryGreen hR w * operatorContinuant w R = operatorContinuant w (R - 1 - 0) at h
  simp only [Nat.sub_zero] at h
  have hu : IsUnit (operatorContinuant w R).det :=
    isUnit_iff_ne_zero.mpr (operatorContinuant_det_ne_zero hR w)
  calc
    boundaryGreen hR w = boundaryGreen hR w *
        (operatorContinuant w R * (operatorContinuant w R)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = (boundaryGreen hR w * operatorContinuant w R) * (operatorContinuant w R)⁻¹ :=
      (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h]

/-- The recursive matrices are exactly evaluation of the manuscript
continuant polynomials, not a separately postulated operator family. -/
theorem operatorContinuant_eq_aeval (w n : ℕ) :
    operatorContinuant w n =
      Polynomial.aeval (pathOperator w) (SmallCases.continuant (Polynomial.X : Polynomial ℝ) n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [SmallCases.continuant]
  | one => simp [SmallCases.continuant]
  | more n ih ih1 =>
    rw [operatorContinuant_recurrence, SmallCases.continuant_recurrence]
    simp only [map_sub, map_mul, Polynomial.aeval_X, ih, ih1]

end SpanningTreeIsoperimetry.ScalarResolvent
