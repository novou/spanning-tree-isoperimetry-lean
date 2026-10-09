import SpanningTreeIsoperimetry.Grid
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The polynomial calculations in the exceptional small hulls

This module checks the continuant algebra in Appendix B, “The exceptional hulls”.
The identities hold in any commutative ring, hence in particular as identities
of integer polynomials.  Their integer evaluations at four are also checked.

Concrete coordinate graphs are linked to their actual adjacency characteristic
polynomials by direct determinant expansion. For all five configurations at
seventeen, their coordinate lists are identified with the faces of the stated
primal domains. The planar matrix-tree bridge and the reduction of all
maximizers to these cases remain separate dependencies.
-/

namespace SpanningTreeIsoperimetry.SmallCases

section Algebra

variable {R : Type*} [CommRing R]

/-- The continuant for a path with `n` vertices. -/
def continuant (t : R) : ℕ → R
  | 0 => 1
  | 1 => t
  | n + 2 => t * continuant t (n + 1) - continuant t n

@[simp] theorem continuant_zero (t : R) : continuant t 0 = 1 := rfl
@[simp] theorem continuant_one (t : R) : continuant t 1 = t := rfl
theorem continuant_recurrence (t : R) (n : ℕ) :
    continuant t (n + 2) = t * continuant t (n + 1) - continuant t n := rfl

theorem continuant_two (t : R) : continuant t 2 = t ^ 2 - 1 := by
  simp [continuant]; ring

theorem continuant_three (t : R) : continuant t 3 = t ^ 3 - 2 * t := by
  simp [continuant]; ring

theorem continuant_four (t : R) : continuant t 4 = t ^ 4 - 3 * t ^ 2 + 1 := by
  simp [continuant]; ring

theorem continuant_five (t : R) : continuant t 5 = t ^ 5 - 4 * t ^ 3 + 3 * t := by
  simp [continuant]; ring

/-- Cassini's identity for the path continuants, at every index. -/
theorem continuant_consecutive (t : R) (n : ℕ) :
    continuant t (n + 1) ^ 2 - continuant t n * continuant t (n + 2) = 1 := by
  induction n with
  | zero => simp [continuant]; ring
  | succ n ih =>
    change continuant t (n + 2) ^ 2 - continuant t (n + 1) * continuant t (n + 3) = 1
    rw [continuant_recurrence t (n + 1)]
    calc
      _ = continuant t (n + 1) ^ 2 - continuant t n * continuant t (n + 2) := by
        rw [continuant_recurrence t n]
        ring
      _ = 1 := ih

/-- The four-cycle expression `c(t)`. -/
def cycle (t : R) : R := t ^ 4 - 4 * t ^ 2

/-- The ladder expression `l_n(t) = f_n(t-1) f_n(t+1)`. -/
def ladder (t : R) (n : ℕ) : R := continuant (t - 1) n * continuant (t + 1) n

/-- The corner-deleted ladder recurrence.  Index zero is a convenience. -/
def cornerLadder (t : R) : ℕ → R
  | 0 => 0
  | 1 => t
  | n + 2 => t * ladder t (n + 1) - cornerLadder t (n + 1)

theorem cornerLadder_recurrence (t : R) (n : ℕ) :
    cornerLadder t (n + 2) = t * ladder t (n + 1) - cornerLadder t (n + 1) := rfl

theorem ladder_two (t : R) : ladder t 2 = cycle t := by
  simp [ladder, continuant, cycle]; ring

theorem ladder_three (t : R) :
    ladder t 3 = t ^ 6 - 7 * t ^ 4 + 7 * t ^ 2 - 1 := by
  simp [ladder, continuant]; ring

theorem ladder_four (t : R) :
    ladder t 4 = t ^ 8 - 10 * t ^ 6 + 23 * t ^ 4 - 10 * t ^ 2 + 1 := by
  simp [ladder, continuant]; ring

theorem cornerLadder_three (t : R) :
    cornerLadder t 3 = t * cycle t - continuant t 3 := by
  simp [cornerLadder, ladder, continuant, cycle]; ring

/-- Opposite two-cell strip and singleton on the 4 by 4 hull. -/
def opposite13 (t : R) : R := continuant t 2 * cycle t - t * continuant t 3

/-- The L-shaped deletion on the 4 by 4 hull. -/
def ell13 (t : R) : R := t ^ 2 * cycle t - 2 * t * continuant t 3 + t ^ 2

/-- Three deleted corner singletons on the 4 by 4 hull. -/
def triple13 (t : R) : R := t ^ 2 * cycle t - 2 * t * continuant t 3

theorem opposite13_sub_ell13 (t : R) : opposite13 t - ell13 t = t ^ 2 := by
  simp [opposite13, ell13, continuant, cycle]; ring

theorem ell13_sub_triple13 (t : R) : ell13 t - triple13 t = t ^ 2 := by
  simp [ell13, triple13]

theorem opposite13_sub_triple13 (t : R) : opposite13 t - triple13 t = 2 * t ^ 2 := by
  simp [opposite13, triple13, continuant, cycle]; ring

/-- Two four-cycles joined at one vertex. -/
def opposite14 (t : R) : R :=
  2 * cycle t * continuant t 3 - t * continuant t 3 ^ 2

theorem opposite14_sub_canonical (t : R) :
    opposite14 t - cornerLadder t 4 = 3 * t := by
  simp [opposite14, cornerLadder, ladder, continuant, cycle]; ring

/-- The eight-vertex core expression obtained from the two symmetry blocks. -/
def core (t : R) : R :=
  t * continuant t 3 * ((t ^ 2 - 3) * (t ^ 2 - 5) - 9)

theorem core_factorization (t : R) :
    core t = t ^ 2 * (t ^ 2 - 2) * (t ^ 4 - 8 * t ^ 2 + 6) := by
  simp [core, continuant]; ring

/-- The long-side opposite configuration, denoted `w(t)` in the paper. -/
def winner17 (t : R) : R :=
  ladder t 3 * continuant t 3 + cornerLadder t 3 * (cycle t - t * continuant t 3)

/-- The L-shaped and short-side opposite configuration, denoted `u(t)`. -/
def alternative17 (t : R) : R := t * core t - (t * ladder t 3 - continuant t 5)

/-- Three corner singletons, denoted `v(t)` in the paper. -/
def triple17 (t : R) : R :=
  t * core t -
    (t * continuant t 2 * cycle t - (t ^ 2 + continuant t 2) * continuant t 3 +
      t * continuant t 2)

theorem winner17_sub_alternative (t : R) :
    winner17 t - alternative17 t = t * (t ^ 4 + 4 * t ^ 2 - 2) := by
  simp [winner17, alternative17, core, cornerLadder, ladder, continuant, cycle]; ring

theorem alternative17_sub_triple (t : R) :
    alternative17 t - triple17 t = t * (t ^ 4 - t ^ 2 + 1) := by
  simp [alternative17, triple17, core, ladder, continuant, cycle]; ring

theorem winner17_sub_canonical (t : R) :
    winner17 t - cornerLadder t 5 = 3 * t ^ 3 - 2 * t := by
  simp [winner17, cornerLadder, ladder, continuant, cycle]; ring

end Algebra

/-! The coordinate graph on an explicitly listed collection of lattice points.
The list need not be assumed injective for the matrix identity; every concrete
list below consists of distinct vertices. -/

section Matrices

variable {R : Type*} [CommRing R]

def pointGraph {n : ℕ} (p : Fin n → ℤ × ℤ) : SimpleGraph (Fin n) where
  Adj i j := ((p i).1 = (p j).1 ∧ |(p i).2 - (p j).2| = 1) ∨
      ((p i).2 = (p j).2 ∧ |(p i).1 - (p j).1| = 1)
  symm := ⟨by
    intro i j h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩
    · exact Or.inr ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩⟩
  loopless := ⟨by intro i; simp⟩
instance {n : ℕ} (p : Fin n → ℤ × ℤ) : DecidableRel (pointGraph p).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
def pointMatrix {n : ℕ} (p : Fin n → ℤ × ℤ) (t : R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then t else if
      ((p i).1 = (p j).1 ∧ |(p i).2 - (p j).2| = 1) ∨
      ((p i).2 = (p j).2 ∧ |(p i).1 - (p j).1| = 1)
    then -1 else 0
theorem pointGraph_charmatrix {n : ℕ} (p : Fin n → ℤ × ℤ) :
    ((pointGraph p).adjMatrix ℤ).charmatrix = pointMatrix p Polynomial.X := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [pointMatrix, pointGraph, SimpleGraph.adjMatrix]
  · rw [Matrix.charmatrix_apply_ne _ _ _ h]
    simp only [SimpleGraph.adjMatrix, Matrix.of_apply, pointGraph, pointMatrix, ite_eq_right h]
    split_ifs with hp <;> simp [hp]

/-- A coordinate graph with distinct listed points is the actual induced
lattice graph on those points. -/
noncomputable def pointGraphIso {n : ℕ} (p : Fin n → ℤ × ℤ) (hinj : Function.Injective p) :
    pointGraph p ≃g domainGraph (Finset.univ.image p) :=
  { Equiv.ofBijective (fun i => ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩)
      ⟨by
        intro i j h
        exact hinj (congrArg Subtype.val h),
       by
        intro v
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
        exact ⟨i, Subtype.ext hi⟩⟩ with
    map_rel_iff' := by intro i j; rfl }

/-- Determinant form of the graph characteristic polynomial. -/
theorem pointGraph_charpoly {n : ℕ} (p : Fin n → ℤ × ℤ) :
    ((pointGraph p).adjMatrix ℤ).charpoly = Matrix.det (pointMatrix p Polynomial.X) := by
  rw [Matrix.charpoly, pointGraph_charmatrix]

def cyclePoints : Fin 4 → ℤ × ℤ := ![(0, 0), (0, 1), (1, 0), (1, 1)]

set_option maxHeartbeats 2000000 in
theorem cyclePoints_det (t : R) : Matrix.det (pointMatrix cyclePoints t) = cycle t := by
  have hm : pointMatrix cyclePoints t =
      !![t , -1 , -1 , 0;
      -1 , t , 0 , -1;
      -1 , 0 , t , -1;
      0 , -1 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, cyclePoints]
  rw [hm]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    Fin.succAbove, cycle]
  ring

def ladderThreePoints : Fin 6 → ℤ × ℤ := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

set_option maxHeartbeats 2000000 in
theorem ladderThreePoints_det (t : R) : Matrix.det (pointMatrix ladderThreePoints t) = ladder t 3 := by
  have hm : pointMatrix ladderThreePoints t =
      !![t , -1 , 0 , -1 , 0 , 0;
      -1 , t , -1 , 0 , -1 , 0;
      0 , -1 , t , 0 , 0 , -1;
      -1 , 0 , 0 , t , -1 , 0;
      0 , -1 , 0 , -1 , t , -1;
      0 , 0 , -1 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, ladderThreePoints]
  rw [hm]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    Fin.succAbove, ladder, continuant]
  ring

def corePoints : Fin 8 → ℤ × ℤ := ![(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

set_option maxHeartbeats 2000000 in
theorem corePoints_det (t : R) : Matrix.det (pointMatrix corePoints t) = core t := by
  have hm : pointMatrix corePoints t =
      !![t , -1 , 0 , -1 , 0 , 0 , 0 , 0;
      -1 , t , 0 , 0 , -1 , 0 , 0 , 0;
      0 , 0 , t , -1 , 0 , -1 , 0 , 0;
      -1 , 0 , -1 , t , -1 , 0 , -1 , 0;
      0 , -1 , 0 , -1 , t , 0 , 0 , -1;
      0 , 0 , -1 , 0 , 0 , t , -1 , 0;
      0 , 0 , 0 , -1 , 0 , -1 , t , -1;
      0 , 0 , 0 , 0 , -1 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, corePoints]
  rw [hm]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    Fin.succAbove, core, continuant]
  ring

/-! Explicit face-coordinate lists for the four nine-vertex matrices at
`N = 17`. Each determinant is checked directly from lattice adjacency; no
leaf-deletion or gluing formula is assumed. -/

def winner17Points : Fin 9 → ℤ × ℤ := ![(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2)]

set_option maxHeartbeats 4000000 in
theorem winner17Points_det (t : R) : Matrix.det (pointMatrix winner17Points t) = winner17 t := by
  have hm : pointMatrix winner17Points t =
      !![t , -1 , 0 , 0 , -1 , 0 , 0 , 0 , 0;
      -1 , t , 0 , 0 , 0 , -1 , 0 , 0 , 0;
      0 , 0 , t , -1 , 0 , 0 , -1 , 0 , 0;
      0 , 0 , -1 , t , -1 , 0 , 0 , -1 , 0;
      -1 , 0 , 0 , -1 , t , -1 , 0 , 0 , -1;
      0 , -1 , 0 , 0 , -1 , t , 0 , 0 , 0;
      0 , 0 , -1 , 0 , 0 , 0 , t , -1 , 0;
      0 , 0 , 0 , -1 , 0 , 0 , -1 , t , -1;
      0 , 0 , 0 , 0 , -1 , 0 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, winner17Points]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, winner17, ladder, cornerLadder, continuant, cycle]
  ring

def alternative17Points : Fin 9 → ℤ × ℤ := ![(0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3)]

set_option maxHeartbeats 4000000 in
theorem alternative17Points_det (t : R) : Matrix.det (pointMatrix alternative17Points t) = alternative17 t := by
  have hm : pointMatrix alternative17Points t =
      !![t , -1 , 0 , -1 , 0 , 0 , 0 , 0 , 0;
      -1 , t , 0 , 0 , -1 , 0 , 0 , 0 , 0;
      0 , 0 , t , -1 , 0 , 0 , -1 , 0 , 0;
      -1 , 0 , -1 , t , -1 , 0 , 0 , -1 , 0;
      0 , -1 , 0 , -1 , t , 0 , 0 , 0 , -1;
      0 , 0 , 0 , 0 , 0 , t , -1 , 0 , 0;
      0 , 0 , -1 , 0 , 0 , -1 , t , -1 , 0;
      0 , 0 , 0 , -1 , 0 , 0 , -1 , t , -1;
      0 , 0 , 0 , 0 , -1 , 0 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, alternative17Points]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, alternative17, core, ladder, continuant]
  ring

def triple17Points : Fin 9 → ℤ × ℤ := ![(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)]

set_option maxHeartbeats 4000000 in
theorem triple17Points_det (t : R) : Matrix.det (pointMatrix triple17Points t) = triple17 t := by
  have hm : pointMatrix triple17Points t =
      !![t , -1 , 0 , -1 , 0 , 0 , 0 , 0 , 0;
      -1 , t , 0 , 0 , -1 , 0 , 0 , 0 , 0;
      0 , 0 , t , -1 , 0 , 0 , 0 , 0 , 0;
      -1 , 0 , -1 , t , -1 , 0 , -1 , 0 , 0;
      0 , -1 , 0 , -1 , t , -1 , 0 , -1 , 0;
      0 , 0 , 0 , 0 , -1 , t , 0 , 0 , -1;
      0 , 0 , 0 , -1 , 0 , 0 , t , -1 , 0;
      0 , 0 , 0 , 0 , -1 , 0 , -1 , t , -1;
      0 , 0 , 0 , 0 , 0 , -1 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, triple17Points]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, triple17, core, continuant, cycle]
  ring

def canonical17Points : Fin 9 → ℤ × ℤ := ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

set_option maxHeartbeats 4000000 in
theorem canonical17Points_det (t : R) : Matrix.det (pointMatrix canonical17Points t) = cornerLadder t 5 := by
  have hm : pointMatrix canonical17Points t =
      !![t , -1 , 0 , 0 , 0 , -1 , 0 , 0 , 0;
      -1 , t , -1 , 0 , 0 , 0 , -1 , 0 , 0;
      0 , -1 , t , -1 , 0 , 0 , 0 , -1 , 0;
      0 , 0 , -1 , t , 0 , 0 , 0 , 0 , -1;
      0 , 0 , 0 , 0 , t , -1 , 0 , 0 , 0;
      -1 , 0 , 0 , 0 , -1 , t , -1 , 0 , 0;
      0 , -1 , 0 , 0 , 0 , -1 , t , -1 , 0;
      0 , 0 , -1 , 0 , 0 , 0 , -1 , t , -1;
      0 , 0 , 0 , -1 , 0 , 0 , 0 , -1 , t] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix, canonical17Points]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, cornerLadder, ladder, continuant]
  ring

/-- Face coordinates for the opposite short-side deletion at seventeen. -/
def short17Points : Fin 9 → ℤ × ℤ :=
  ![(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2)]

/-- The short-side and L configurations have isomorphic face graphs. -/
def shortToEll : Equiv.Perm (Fin 9) where
  toFun := ![8, 4, 1, 7, 3, 0, 5, 6, 2]
  invFun := ![5, 2, 8, 4, 1, 6, 7, 3, 0]
  left_inv := by decide
  right_inv := by decide

theorem short17Points_matrix (t : R) :
    pointMatrix short17Points t =
      (pointMatrix alternative17Points t).submatrix shortToEll shortToEll := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pointMatrix, short17Points, alternative17Points, shortToEll, Matrix.submatrix]

theorem short17Points_det (t : R) : Matrix.det (pointMatrix short17Points t) = alternative17 t := by
  rw [short17Points_matrix, Matrix.det_submatrix_equiv_self, alternative17Points_det]

theorem seventeen_characteristic_polynomials :
    ((pointGraph winner17Points).adjMatrix ℤ).charpoly = winner17 Polynomial.X ∧
    ((pointGraph alternative17Points).adjMatrix ℤ).charpoly = alternative17 Polynomial.X ∧
    ((pointGraph triple17Points).adjMatrix ℤ).charpoly = triple17 Polynomial.X ∧
    ((pointGraph canonical17Points).adjMatrix ℤ).charpoly = cornerLadder Polynomial.X 5 ∧
    ((pointGraph short17Points).adjMatrix ℤ).charpoly = alternative17 Polynomial.X := by
  simp only [pointGraph_charpoly, winner17Points_det, alternative17Points_det,
    triple17Points_det, canonical17Points_det, short17Points_det, and_self]

/-- Lower-left coordinates of unit-square faces inside a given hull. -/
def boundedFaces (r s : ℕ) (S : Domain) : Domain :=
  (rectangle (r - 1) (s - 1)).filter fun p => p ∈ S ∧
    (p.1 + 1, p.2) ∈ S ∧ (p.1, p.2 + 1) ∈ S ∧ (p.1 + 1, p.2 + 1) ∈ S

def winner17Domain : Domain := rectangle 4 5 \ {(0, 0), (0, 1), (3, 4)}
def alternative17Domain : Domain := rectangle 4 5 \ {(0, 0), (0, 1), (1, 0)}
def triple17Domain : Domain := rectangle 4 5 \ {(0, 0), (3, 0), (0, 4)}
def canonical17Domain : Domain := rectangle 3 6 \ {(0, 0)}
def short17Domain : Domain := rectangle 4 5 \ {(0, 0), (1, 0), (3, 4)}

theorem seventeen_domain_sizes :
    winner17Domain.card = 17 ∧ alternative17Domain.card = 17 ∧
    triple17Domain.card = 17 ∧ canonical17Domain.card = 17 ∧ short17Domain.card = 17 := by
  decide

theorem seventeen_face_sets :
    boundedFaces 4 5 winner17Domain = Finset.univ.image winner17Points ∧
    boundedFaces 4 5 alternative17Domain = Finset.univ.image alternative17Points ∧
    boundedFaces 4 5 triple17Domain = Finset.univ.image triple17Points ∧
    boundedFaces 3 6 canonical17Domain = Finset.univ.image canonical17Points ∧
    boundedFaces 4 5 short17Domain = Finset.univ.image short17Points := by
  decide

theorem seventeen_points_injective :
    Function.Injective winner17Points ∧ Function.Injective alternative17Points ∧
    Function.Injective triple17Points ∧ Function.Injective canonical17Points ∧
    Function.Injective short17Points := by
  decide

end Matrices

/-! Specializing the preceding identities to `Polynomial ℤ` gives literal
polynomial equalities, not just comparisons at a single numerical point. -/

theorem winner17_polynomial_difference :
    winner17 (Polynomial.X : Polynomial ℤ) - cornerLadder Polynomial.X 5 =
      3 * Polynomial.X ^ 3 - 2 * Polynomial.X := winner17_sub_canonical _

/-! Exact integer evaluations of every recurrence value displayed in the small
case calculation.  `norm_num` constructs kernel-checked arithmetic proofs. -/

theorem continuant_values :
    continuant (4 : ℤ) 0 = 1 ∧ continuant (4 : ℤ) 2 = 15 ∧
    continuant (4 : ℤ) 3 = 56 ∧ continuant (4 : ℤ) 4 = 209 ∧
    continuant (4 : ℤ) 5 = 780 := by norm_num [continuant]

theorem cycle_value : cycle (4 : ℤ) = 192 := by norm_num [cycle]

theorem ladder_values : ladder (4 : ℤ) 3 = 2415 ∧ ladder (4 : ℤ) 4 = 30305 := by
  norm_num [ladder, continuant]

theorem cornerLadder_values :
    cornerLadder (4 : ℤ) 3 = 712 ∧ cornerLadder (4 : ℤ) 4 = 8948 ∧
    cornerLadder (4 : ℤ) 5 = 112272 := by
  norm_num [cornerLadder, ladder, continuant]

theorem core_value : core (4 : ℤ) = 30016 := by norm_num [core, continuant]

theorem thirteen_values :
    opposite13 (4 : ℤ) = 2656 ∧ ell13 (4 : ℤ) = 2640 ∧ triple13 (4 : ℤ) = 2624 := by
  norm_num [opposite13, ell13, triple13, continuant, cycle]

theorem fourteen_value : opposite14 (4 : ℤ) = 8960 := by
  norm_num [opposite14, cycle, continuant]

theorem seventeen_values :
    winner17 (4 : ℤ) = 112456 ∧ alternative17 (4 : ℤ) = 111184 ∧
    triple17 (4 : ℤ) = 110220 := by
  norm_num [winner17, alternative17, triple17, core, cornerLadder, ladder, continuant, cycle]

theorem thirteen_order :
    triple13 (4 : ℤ) < ell13 4 ∧ ell13 (4 : ℤ) < opposite13 4 := by
  rw [thirteen_values.1, thirteen_values.2.1, thirteen_values.2.2]
  norm_num

theorem fourteen_improvement : opposite14 (4 : ℤ) - cornerLadder 4 4 = 12 := by
  rw [opposite14_sub_canonical]
  norm_num

theorem seventeen_improvement : winner17 (4 : ℤ) - cornerLadder 4 5 = 184 := by
  rw [winner17_sub_canonical]
  norm_num

theorem seventeen_order :
    triple17 (4 : ℤ) < alternative17 4 ∧ alternative17 (4 : ℤ) < winner17 4 ∧
    cornerLadder (4 : ℤ) 5 < winner17 4 := by
  rw [seventeen_values.1, seventeen_values.2.1, seventeen_values.2.2,
    cornerLadder_values.2.2]
  norm_num

/-- Exact determinants of the explicit nine-vertex adjacency characteristic matrices. -/
theorem seventeen_matrix_values :
    Matrix.det (pointMatrix winner17Points (4 : ℤ)) = 112456 ∧
    Matrix.det (pointMatrix alternative17Points (4 : ℤ)) = 111184 ∧
    Matrix.det (pointMatrix triple17Points (4 : ℤ)) = 110220 ∧
    Matrix.det (pointMatrix canonical17Points (4 : ℤ)) = 112272 := by
  rw [winner17Points_det, alternative17Points_det, triple17Points_det, canonical17Points_det]
  exact ⟨seventeen_values.1, seventeen_values.2.1, seventeen_values.2.2,
    cornerLadder_values.2.2⟩

end SpanningTreeIsoperimetry.SmallCases
