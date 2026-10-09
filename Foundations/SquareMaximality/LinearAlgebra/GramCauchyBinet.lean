import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A Gram form of Cauchy--Binet

This file proves the maximal-minor identity needed by the Matrix--Tree
theorem.  Instead of expanding a rectangular matrix product directly, the
proof compares

`det (1 + X • B Bᵀ)` and `det (1 + X • Bᵀ B)`

using the Weinstein--Aronszajn identity, then takes the coefficient in the
top degree on the smaller side.  Mathlib's principal-minor coefficient
formula turns that coefficient into the required sum.
-/

set_option autoImplicit false

namespace SquareMaximality.GramCauchyBinet

open scoped BigOperators Matrix Polynomial

variable {R I E : Type*} [CommRing R]

/-- The polynomial Gram identity underlying Cauchy--Binet. -/
theorem polynomial_gram_identity
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) :
    Matrix.det (1 + (Polynomial.X : R[X]) • (B * Bᵀ).map Polynomial.C) =
      Matrix.det (1 + (Polynomial.X : R[X]) • (Bᵀ * B).map Polynomial.C) := by
  simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.transpose_apply] using
    (Matrix.det_one_add_mul_comm
      ((Polynomial.X : R[X]) • B.map Polynomial.C)
      (Bᵀ.map Polynomial.C))

/-- The determinant of a Gram matrix is the sum of the principal Gram
minors whose size is the number of rows of the original matrix. -/
theorem det_gram_eq_sum_maximal_principal_gram_minors
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) :
    Matrix.det (B * Bᵀ) =
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card I),
        Matrix.det ((Bᵀ * B).submatrix
          (Subtype.val : s → E) (Subtype.val : s → E)) := by
  have hcoeff := congrArg (fun p : R[X] ↦ p.coeff (Fintype.card I))
    (polynomial_gram_identity B)
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors] at hcoeff
  have huniv :
      Matrix.det ((B * Bᵀ).submatrix
        (Subtype.val : ↑(Finset.univ : Finset I) → I)
        (Subtype.val : ↑(Finset.univ : Finset I) → I)) =
        Matrix.det (B * Bᵀ) := by
    let e : ↑(Finset.univ : Finset I) ≃ I :=
      { toFun := Subtype.val
        invFun := fun i ↦ ⟨i, Finset.mem_univ i⟩
        left_inv := fun _ ↦ Subtype.ext rfl
        right_inv := fun _ ↦ rfl }
    exact Matrix.det_submatrix_equiv_self e (B * Bᵀ)
  have hpowerset :
      Finset.univ.powersetCard (Fintype.card I) =
        ({Finset.univ} : Finset (Finset I)) := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset I)
  rw [hpowerset, Finset.sum_singleton, huniv] at hcoeff
  exact hcoeff

/-- A principal Gram minor is the square of any corresponding maximal
minor.  The equivalence merely chooses an ordering of the selected columns. -/
theorem det_principal_gram_eq_sq_minor
    [Fintype I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) (s : Finset E) (e : ↑s ≃ I) :
    Matrix.det ((Bᵀ * B).submatrix
      (Subtype.val : s → E) (Subtype.val : s → E)) =
      Matrix.det (B.submatrix e Subtype.val) ^ 2 := by
  let C : Matrix s s R := B.submatrix e Subtype.val
  have hmatrix :
      (Bᵀ * B).submatrix
          (Subtype.val : s → E) (Subtype.val : s → E) =
        Cᵀ * C := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, C]
    exact (e.sum_comp (fun i ↦ B i x.1 * B i y.1)).symm
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, pow_two]

/-- A canonical ordering of a maximal set of columns.  It is deliberately
noncomputable: only the square of its determinant will be used. -/
noncomputable def maximalMinor
    [Fintype I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) (s : Finset E) : R :=
  if h : Fintype.card s = Fintype.card I then
    Matrix.det (B.submatrix (Fintype.equivOfCardEq h) Subtype.val)
  else
    0

theorem det_principal_gram_eq_sq_maximalMinor
    [Fintype I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) (s : Finset E)
    (hs : s.card = Fintype.card I) :
    Matrix.det ((Bᵀ * B).submatrix
      (Subtype.val : s → E) (Subtype.val : s → E)) =
      maximalMinor B s ^ 2 := by
  have hcard : Fintype.card s = Fintype.card I := by
    simpa using hs
  rw [maximalMinor, dif_pos hcard]
  exact det_principal_gram_eq_sq_minor B s (Fintype.equivOfCardEq hcard)

/-- Cauchy--Binet for a Gram matrix: its determinant is the sum of the
squares of all maximal minors. -/
theorem det_gram_eq_sum_sq_maximalMinors
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (B : Matrix I E R) :
    Matrix.det (B * Bᵀ) =
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card I),
        maximalMinor B s ^ 2 := by
  rw [det_gram_eq_sum_maximal_principal_gram_minors B]
  apply Finset.sum_congr rfl
  intro s hs
  exact det_principal_gram_eq_sq_maximalMinor B s
    (Finset.mem_powersetCard.mp hs).2

end SquareMaximality.GramCauchyBinet
