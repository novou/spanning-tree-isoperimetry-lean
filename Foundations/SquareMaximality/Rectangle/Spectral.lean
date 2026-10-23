module

public import SquareMaximality.Rectangle.ProductInputs
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

@[expose] public section

set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Cosine diagonalization of rectangular path products

This module develops the remaining finite linear algebra behind
`ProductInputs.RectangularSpectralCofactorInput`.  The eigenvectors of a path
are the discrete cosine modes with half-integer spatial phase.
-/

namespace SquareMaximality.Rectangle.Spectral

open SimpleGraph
open Product
open Module
open scoped Matrix TensorProduct

noncomputable section

noncomputable local instance pathAdjDecidable (n : ℕ) :
    DecidableRel (pathGraph n).Adj := Classical.decRel _

noncomputable local instance rectangleAdjDecidable (a t : ℕ) :
    DecidableRel (pathGraph a □ pathGraph t).Adj := Classical.decRel _

/-- The `j`th Laplacian eigenvalue of the path on `n` vertices. -/
noncomputable def pathEigenvalue (n j : ℕ) : ℝ :=
  2 - 2 * Real.cos (Real.pi * ((j : ℝ) / (n : ℝ)))

/-- The half-shifted discrete cosine mode. -/
noncomputable def pathCosineMode (n : ℕ) (j x : Fin n) : ℝ :=
  Real.cos (Real.pi * ((j : ℝ) / (n : ℝ)) * ((x : ℝ) + 1 / 2))

private theorem path_neighborFinset_singleton_zero
    {n : ℕ} (hn : 2 ≤ n) :
    Finset.univ.filter
        (fun y => (pathGraph n).Adj (⟨0, by omega⟩ : Fin n) y) =
      {⟨1, by omega⟩} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathGraph_adj,
    Finset.mem_singleton]
  apply Iff.intro
  · intro h
    apply Fin.ext
    change y.1 = 1
    omega
  · intro h
    subst y
    simp

private theorem path_neighborFinset_singleton_last
    {n : ℕ} (hn : 2 ≤ n) :
    Finset.univ.filter
        (fun y => (pathGraph n).Adj (⟨n - 1, by omega⟩ : Fin n) y) =
      {⟨n - 2, by omega⟩} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathGraph_adj,
    Finset.mem_singleton]
  apply Iff.intro
  · intro h
    apply Fin.ext
    change y.1 = n - 2
    omega
  · intro h
    subst y
    change n - 1 + 1 = n - 2 ∨ n - 2 + 1 = n - 1
    omega

private theorem path_neighborFinset_pair
    {n : ℕ} (x : Fin n) (hx0 : 0 < x.1) (hxn : x.1 + 1 < n) :
    Finset.univ.filter (fun y => (pathGraph n).Adj x y) =
      {⟨x.1 - 1, by omega⟩, ⟨x.1 + 1, hxn⟩} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathGraph_adj,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h
    · right
      apply Fin.ext
      change y.1 = x.1 + 1
      omega
    · left
      apply Fin.ext
      change y.1 = x.1 - 1
      omega
  · intro h
    rcases h with h | h
    · subst y
      right
      change x.1 - 1 + 1 = x.1
      omega
    · subst y
      left
      change x.1 + 1 = x.1 + 1
      rfl

private theorem path_lapMatrix_mulVec_zero
    {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℝ) :
    ((pathGraph n).lapMatrix ℝ *ᵥ f) (⟨0, by omega⟩ : Fin n) =
      f ⟨0, by omega⟩ - f ⟨1, by omega⟩ := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  have hneighbors : Finset.univ.filter (fun y => (pathGraph n).Adj z y) = {o} :=
    path_neighborFinset_singleton_zero hn
  change ((pathGraph n).lapMatrix ℝ *ᵥ f) z = f z - f o
  rw [lapMatrix_mulVec_apply]
  simp only [SimpleGraph.degree, neighborFinset_eq_filter, hneighbors,
    Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton]

private theorem path_lapMatrix_mulVec_last
    {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℝ) :
    ((pathGraph n).lapMatrix ℝ *ᵥ f) (⟨n - 1, by omega⟩ : Fin n) =
      f ⟨n - 1, by omega⟩ - f ⟨n - 2, by omega⟩ := by
  let z : Fin n := ⟨n - 1, by omega⟩
  let p : Fin n := ⟨n - 2, by omega⟩
  have hneighbors : Finset.univ.filter (fun y => (pathGraph n).Adj z y) = {p} :=
    path_neighborFinset_singleton_last hn
  change ((pathGraph n).lapMatrix ℝ *ᵥ f) z = f z - f p
  rw [lapMatrix_mulVec_apply]
  simp only [SimpleGraph.degree, neighborFinset_eq_filter, hneighbors,
    Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton]

private theorem path_lapMatrix_mulVec_interior
    {n : ℕ} (x : Fin n) (hx0 : 0 < x.1) (hxn : x.1 + 1 < n)
    (f : Fin n → ℝ) :
    ((pathGraph n).lapMatrix ℝ *ᵥ f) x =
      2 * f x - f ⟨x.1 - 1, by omega⟩ - f ⟨x.1 + 1, hxn⟩ := by
  let p : Fin n := ⟨x.1 - 1, by omega⟩
  let q : Fin n := ⟨x.1 + 1, hxn⟩
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    dsimp only [p, q] at hval
    omega
  have hneighbors : Finset.univ.filter (fun y => (pathGraph n).Adj x y) = {p, q} :=
    path_neighborFinset_pair x hx0 hxn
  change ((pathGraph n).lapMatrix ℝ *ᵥ f) x =
    2 * f x - f p - f q
  rw [lapMatrix_mulVec_apply]
  simp only [SimpleGraph.degree, neighborFinset_eq_filter, hneighbors]
  rw [Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
  rw [Finset.sum_insert (by simpa using hpq), Finset.sum_singleton]
  norm_num
  ring

private theorem path_lapMatrix_mulVec_one (f : Fin 1 → ℝ) :
    (pathGraph 1).lapMatrix ℝ *ᵥ f = 0 := by
  ext x
  have hneighbors : Finset.univ.filter (fun y => (pathGraph 1).Adj x y) = ∅ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathGraph_adj,
      Finset.notMem_empty, iff_false]
    omega
  change ((pathGraph 1).lapMatrix ℝ *ᵥ f) x = 0
  rw [lapMatrix_mulVec_apply]
  simp only [SimpleGraph.degree, neighborFinset_eq_filter, hneighbors,
    Finset.card_empty, Nat.cast_zero, zero_mul, Finset.sum_empty, sub_zero]

private theorem cosine_second_difference (φ u : ℝ) :
    2 * Real.cos (φ * u) - Real.cos (φ * (u - 1)) -
        Real.cos (φ * (u + 1)) =
      (2 - 2 * Real.cos φ) * Real.cos (φ * u) := by
  rw [show φ * (u - 1) = φ * u - φ by ring,
    show φ * (u + 1) = φ * u + φ by ring,
    Real.cos_sub, Real.cos_add]
  ring

private theorem cosine_left_boundary (φ : ℝ) :
    Real.cos (φ * (1 / 2)) - Real.cos (φ * (1 + 1 / 2)) =
      (2 - 2 * Real.cos φ) * Real.cos (φ * (1 / 2)) := by
  have h := cosine_second_difference φ (1 / 2)
  have hneg : Real.cos (φ * (1 / 2 - 1)) = Real.cos (φ * (1 / 2)) := by
    rw [show φ * (1 / 2 - 1) = -(φ * (1 / 2)) by ring, Real.cos_neg]
  rw [hneg] at h
  linarith

private theorem cosine_right_boundary (φ N : ℝ)
    (hsin : Real.sin (N * φ) = 0) :
    Real.cos (φ * (N - 1 + 1 / 2)) -
        Real.cos (φ * (N - 2 + 1 / 2)) =
      (2 - 2 * Real.cos φ) * Real.cos (φ * (N - 1 + 1 / 2)) := by
  have hghost : Real.cos (φ * (N - 1 + 1 / 2 + 1)) =
      Real.cos (φ * (N - 1 + 1 / 2)) := by
    rw [show φ * (N - 1 + 1 / 2 + 1) = N * φ + φ / 2 by ring,
      show φ * (N - 1 + 1 / 2) = N * φ - φ / 2 by ring,
      Real.cos_add, Real.cos_sub, hsin]
    ring
  have h := cosine_second_difference φ (N - 1 + 1 / 2)
  rw [hghost] at h
  have hprev : N - 1 + 1 / 2 - 1 = N - 2 + 1 / 2 := by ring
  rw [hprev] at h
  linarith

/-- Every discrete cosine mode is an eigenvector of the path Laplacian. -/
theorem pathCosineMode_mulVec {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (pathGraph n).lapMatrix ℝ *ᵥ pathCosineMode n j =
      pathEigenvalue n j • pathCosineMode n j := by
  by_cases hn1 : n = 1
  · subst n
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rw [path_lapMatrix_mulVec_one]
    ext x
    simp [pathEigenvalue, pathCosineMode]
  · have hn2 : 2 ≤ n := by omega
    ext x
    let φ : ℝ := Real.pi * ((j : ℝ) / (n : ℝ))
    by_cases hx0 : x.1 = 0
    · have hx : x = (⟨0, by omega⟩ : Fin n) := Fin.ext hx0
      subst x
      rw [path_lapMatrix_mulVec_zero hn2]
      have h := cosine_left_boundary φ
      simpa only [pathCosineMode, pathEigenvalue, φ, Fin.val_zero,
        Nat.cast_zero, Nat.cast_one, Pi.smul_apply, smul_eq_mul,
        zero_add, one_div] using h
    · by_cases hxlast : x.1 + 1 = n
      · have hx : x = (⟨n - 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          change x.1 = n - 1
          omega
        rw [hx]
        rw [path_lapMatrix_mulVec_last hn2]
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hphase : (n : ℝ) * φ = (j : ℝ) * Real.pi := by
          dsimp only [φ]
          field_simp
        have hsin : Real.sin ((n : ℝ) * φ) = 0 := by
          rw [hphase]
          exact Real.sin_nat_mul_pi j
        have h := cosine_right_boundary φ (n : ℝ) hsin
        simpa only [pathCosineMode, pathEigenvalue, φ, Pi.smul_apply,
          smul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n),
          Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_one,
          Nat.cast_ofNat] using h
      · have hxpos : 0 < x.1 := Nat.pos_of_ne_zero hx0
        have hxnext : x.1 + 1 < n := by omega
        rw [path_lapMatrix_mulVec_interior x hxpos hxnext]
        have h := cosine_second_difference φ ((x : ℝ) + 1 / 2)
        have hprev : ((x.1 - 1 : ℕ) : ℝ) + 1 / 2 =
            (x : ℝ) + 1 / 2 - 1 := by
          have hnat : x.1 - 1 + 1 = x.1 := by omega
          have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
          push_cast at hreal
          linarith
        have hnext : ((x.1 + 1 : ℕ) : ℝ) + 1 / 2 =
            (x : ℝ) + 1 / 2 + 1 := by
          push_cast
          ring
        simpa only [pathCosineMode, pathEigenvalue, φ, Pi.smul_apply,
          smul_eq_mul, hprev, hnext] using h

theorem pathEigenvalue_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun j : Fin n => pathEigenvalue n j) := by
  intro j k hjk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let θ : Fin n → ℝ := fun i => Real.pi * ((i : ℝ) / (n : ℝ))
  have hθmem (i : Fin n) : θ i ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg Real.pi_pos.le (div_nonneg (Nat.cast_nonneg _) hnR.le)
    · have hi : (i : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.le_of_lt i.2)
      have hratio : (i : ℝ) / (n : ℝ) ≤ 1 := (div_le_one₀ hnR).2 hi
      nlinarith [Real.pi_pos]
  have hcos : Real.cos (θ j) = Real.cos (θ k) := by
    dsimp only [pathEigenvalue, θ] at hjk ⊢
    linarith
  have hθ := Real.strictAntiOn_cos.injOn (hθmem j) (hθmem k) hcos
  apply Fin.ext
  dsimp only [θ] at hθ
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hn0, hpi0] at hθ
  exact_mod_cast hθ

theorem pathCosineMode_ne_zero {n : ℕ} (hn : 0 < n) (j : Fin n) :
    pathCosineMode n j ≠ 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let z : Fin n := ⟨0, hn⟩
  let θ : ℝ := Real.pi * ((j : ℝ) / (n : ℝ)) * (1 / 2)
  have hjR : (j : ℝ) < (n : ℝ) := by exact_mod_cast j.2
  have hratio : (j : ℝ) / (n : ℝ) < 1 := (div_lt_one₀ hnR).2 hjR
  have hθ0 : 0 ≤ θ := by
    exact mul_nonneg
      (mul_nonneg Real.pi_pos.le (div_nonneg (Nat.cast_nonneg _) hnR.le))
      (by norm_num)
  have hθhalf : θ < Real.pi / 2 := by
    have hmul : Real.pi * ((j : ℝ) / (n : ℝ)) < Real.pi :=
      by simpa using mul_lt_mul_of_pos_left hratio Real.pi_pos
    dsimp only [θ]
    nlinarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθhalf⟩
  intro hzero
  have hz : Real.cos θ = 0 := by
    simpa [pathCosineMode, z, θ] using congrFun hzero z
  linarith

theorem pathCosineMode_hasEigenvector {n : ℕ} (hn : 0 < n) (j : Fin n) :
    Module.End.HasEigenvector
      (Matrix.toLin' ((pathGraph n).lapMatrix ℝ) : Module.End ℝ (Fin n → ℝ))
      (pathEigenvalue n j) (pathCosineMode n j) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact pathCosineMode_mulVec hn j
  · exact pathCosineMode_ne_zero hn j

theorem pathCosineMode_linearIndependent {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℝ (pathCosineMode n) := by
  exact Module.End.eigenvectors_linearIndependent'
    (Matrix.toLin' ((pathGraph n).lapMatrix ℝ) : Module.End ℝ (Fin n → ℝ))
    (fun j : Fin n => pathEigenvalue n j) (pathEigenvalue_injective hn) (pathCosineMode n)
    (pathCosineMode_hasEigenvector hn)

/-- The finite discrete cosine modes, bundled as a basis. -/
noncomputable def pathCosineBasis (n : ℕ) (hn : 0 < n) :
    Module.Basis (Fin n) ℝ (Fin n → ℝ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (pathCosineMode_linearIndependent hn)

@[simp] theorem pathCosineBasis_apply {n : ℕ} (hn : 0 < n) (j : Fin n) :
    pathCosineBasis n hn j = pathCosineMode n j := by
  classical
  simp [pathCosineBasis]

/-- Uncurrying, as a linear equivalence, in the coordinate order used by
the rectangular vertex type. -/
private def uncurryLinearEquiv (α β : Type*) :
    (β → α → ℝ) ≃ₗ[ℝ] (α × β → ℝ) where
  toFun f p := f p.2 p.1
  invFun f y x := f (x, y)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical tensor/function-space equivalence sends a pure tensor to
the pointwise product of its two factors. -/
private noncomputable def rectangleTensorEquiv (a t : ℕ) :
    ((Fin a → ℝ) ⊗[ℝ] (Fin t → ℝ)) ≃ₗ[ℝ] (Fin a × Fin t → ℝ) :=
  (TensorProduct.piScalarRight ℝ ℝ (Fin a → ℝ) (Fin t)).trans
    (uncurryLinearEquiv (Fin a) (Fin t))

@[simp] private theorem rectangleTensorEquiv_tmul (a t : ℕ)
    (f : Fin a → ℝ) (g : Fin t → ℝ) (p : Fin a × Fin t) :
    rectangleTensorEquiv a t (f ⊗ₜ[ℝ] g) p = f p.1 * g p.2 := by
  simp [rectangleTensorEquiv, uncurryLinearEquiv, mul_comm]

/-- The product of two path cosine modes. -/
noncomputable def rectangleCosineMode (a t : ℕ)
    (jk xy : Fin a × Fin t) : ℝ :=
  pathCosineMode a jk.1 xy.1 * pathCosineMode t jk.2 xy.2

/-- Tensoring the two path cosine bases gives a basis of functions on the
rectangular vertex set. -/
noncomputable def rectangleCosineBasis (a t : ℕ) (ha : 0 < a) (ht : 0 < t) :
    Module.Basis (Fin a × Fin t) ℝ (Fin a × Fin t → ℝ) :=
  ((pathCosineBasis a ha).tensorProduct (pathCosineBasis t ht)).map
    (rectangleTensorEquiv a t)

@[simp] theorem rectangleCosineBasis_apply {a t : ℕ} (ha : 0 < a) (ht : 0 < t)
    (jk : Fin a × Fin t) :
    rectangleCosineBasis a t ha ht jk = rectangleCosineMode a t jk := by
  rcases jk with ⟨j, k⟩
  ext xy
  simp [rectangleCosineBasis, rectangleCosineMode]

private theorem rectangle_lapMatrix_mulVec_product (a t : ℕ)
    (f : Fin a → ℝ) (g : Fin t → ℝ) :
    (pathGraph a □ pathGraph t).lapMatrix ℝ *ᵥ
        (fun xy => f xy.1 * g xy.2) =
      fun xy =>
        ((pathGraph a).lapMatrix ℝ *ᵥ f) xy.1 * g xy.2 +
          f xy.1 * ((pathGraph t).lapMatrix ℝ *ᵥ g) xy.2 := by
  classical
  ext xy
  rw [lapMatrix_mulVec_apply, lapMatrix_mulVec_apply, lapMatrix_mulVec_apply,
    degree_boxProd, neighborFinset_boxProd]
  simp only [Finset.sum_disjUnion, Finset.sum_product, Finset.sum_singleton,
    Nat.cast_add, add_mul, SimpleGraph.degree, neighborFinset_eq_filter]
  ring_nf
  rw [Finset.mul_sum
      (Finset.univ.filter fun x => (pathGraph t).Adj xy.2 x) g (f xy.1),
    Finset.mul_sum
      (Finset.univ.filter fun x => (pathGraph a).Adj xy.1 x) f (g xy.2)]
  ring_nf

/-- The tensor cosine modes diagonalize the rectangular Laplacian. -/
theorem rectangleCosineMode_mulVec {a t : ℕ} (ha : 0 < a) (ht : 0 < t)
    (jk : Fin a × Fin t) :
    (pathGraph a □ pathGraph t).lapMatrix ℝ *ᵥ rectangleCosineMode a t jk =
      eigenvalue a t jk.1 jk.2 • rectangleCosineMode a t jk := by
  change
    (pathGraph a □ pathGraph t).lapMatrix ℝ *ᵥ
        (fun xy => pathCosineMode a jk.1 xy.1 * pathCosineMode t jk.2 xy.2) = _
  rw [rectangle_lapMatrix_mulVec_product,
    pathCosineMode_mulVec ha jk.1, pathCosineMode_mulVec ht jk.2]
  ext xy
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [rectangleCosineMode, eigenvalue, pathEigenvalue]
  ring

/-- In the tensor cosine basis, the rectangular Laplacian is diagonal. -/
theorem rectangleLaplacian_toMatrix_cosine {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    LinearMap.toMatrix (rectangleCosineBasis a t ha ht)
        (rectangleCosineBasis a t ha ht)
        (Matrix.toLin' ((pathGraph a □ pathGraph t).lapMatrix ℝ)) =
      Matrix.diagonal (fun jk : Fin a × Fin t => eigenvalue a t jk.1 jk.2) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply,
    rectangleCosineBasis_apply, rectangleCosineMode_mulVec ha ht]
  rw [← rectangleCosineBasis_apply ha ht j, map_smul]
  simp only [Finsupp.smul_apply]
  rw [Basis.repr_self_apply]
  simp only [smul_eq_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst i
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- Characteristic polynomial of the rectangular Laplacian, with every
frequency displayed explicitly. -/
theorem rectangleLaplacian_charpoly {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    ((pathGraph a □ pathGraph t).lapMatrix ℝ).charpoly =
      ∏ jk : Fin a × Fin t,
        (Polynomial.X - Polynomial.C (eigenvalue a t jk.1 jk.2)) := by
  classical
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix
    (Matrix.toLin' ((pathGraph a □ pathGraph t).lapMatrix ℝ))
    (rectangleCosineBasis a t ha ht), rectangleLaplacian_toMatrix_cosine ha ht,
    Matrix.charpoly_diagonal]

private theorem coeff_one_prod_X_sub_C {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι) (μ : ι → ℝ) (hz : μ z = 0) :
    (∏ i : ι, (Polynomial.X - Polynomial.C (μ i))).coeff 1 =
      (-1 : ℝ) ^ (Fintype.card ι - 1) * ∏ i ∈ Finset.univ.erase z, μ i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ z), hz]
  simp only [map_zero, sub_zero, Polynomial.coeff_X_mul]
  rw [Polynomial.coeff_zero_prod]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, zero_sub]
  rw [Finset.prod_neg]
  simp [Finset.card_erase_of_mem]

private theorem prod_erase_eq_prod_ite {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (z : ι) (f : ι → M) :
    (∏ i ∈ Finset.univ.erase z, f i) = ∏ i : ι, if i = z then 1 else f i := by
  rw [Fintype.prod_eq_prod_compl_mul z]
  simp only [if_pos, mul_one]
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    simp only [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [hi]

private theorem prod_nonzero_rectangleEigenvalues {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t) :
    (∏ jk ∈ Finset.univ.erase (ProductInputs.cornerRoot a t ha ht),
        eigenvalue a t jk.1 jk.2) =
      zeroRowProduct t * ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let za : Fin (n + 1) := 0
  let zt : Fin (m + 1) := 0
  change
    (∏ jk ∈ Finset.univ.erase (za, zt),
        eigenvalue (n + 1) (m + 1) jk.1 jk.2) = _
  rw [prod_erase_eq_prod_ite, Fintype.prod_prod_type]
  rw [Fin.prod_univ_succ]
  simp only [Prod.mk.injEq, Fin.succ_ne_zero, false_and, if_false, za, zt,
    Fin.val_zero, true_and]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.succ_ne_zero, if_false, if_true, one_mul]
  have hzero :
      (∏ k : Fin m,
          eigenvalue (n + 1) (m + 1) 0 k.succ) = zeroRowProduct (m + 1) := by
    rw [zeroRowProduct]
    simp only [Nat.add_sub_cancel]
    have hfin := Fin.prod_univ_eq_prod_range
      (fun k => eigenvalue (n + 1) (m + 1) 0 (k + 1)) m
    rw [show (∏ k : Fin m, eigenvalue (n + 1) (m + 1) 0 k.succ) =
        ∏ k ∈ Finset.range m, eigenvalue (n + 1) (m + 1) 0 (k + 1) by
      simpa only [Fin.val_succ] using hfin]
    apply Finset.prod_congr rfl
    intro k hk
    simp only [eigenvalue, Nat.cast_zero, zero_div, mul_zero, Real.cos_zero,
      Nat.cast_add, Nat.cast_one]
    ring_nf
  have hrows :
      (∏ j : Fin n, ∏ k : Fin (m + 1),
          eigenvalue (n + 1) (m + 1) j.succ k) =
        ∏ j ∈ Finset.Ico 1 (n + 1), eigenRowProduct (n + 1) (m + 1) j := by
    calc
      (∏ j : Fin n, ∏ k : Fin (m + 1),
          eigenvalue (n + 1) (m + 1) j.succ k) =
          ∏ j : Fin n, eigenRowProduct (n + 1) (m + 1) (j + 1) := by
            apply Fintype.prod_congr
            intro j
            rw [eigenRowProduct]
            simpa only [Fin.val_succ] using Fin.prod_univ_eq_prod_range
              (fun k => eigenvalue (n + 1) (m + 1) (j + 1) k) (m + 1)
      _ = ∏ j ∈ Finset.range n,
          eigenRowProduct (n + 1) (m + 1) (j + 1) := by
            simpa only using Fin.prod_univ_eq_prod_range
              (fun j => eigenRowProduct (n + 1) (m + 1) (j + 1)) n
      _ = ∏ j ∈ Finset.Ico 1 (n + 1),
          eigenRowProduct (n + 1) (m + 1) j := by
            rw [Finset.prod_Ico_eq_prod_range]
            simp [Nat.add_comm]
  rw [hzero, hrows]

theorem rectangleLaplacian_charpoly_coeff_one {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t) :
    ((pathGraph a □ pathGraph t).lapMatrix ℝ).charpoly.coeff 1 =
      (-1 : ℝ) ^ (a * t - 1) *
        (zeroRowProduct t * ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j) := by
  rw [rectangleLaplacian_charpoly ha ht,
    coeff_one_prod_X_sub_C (ProductInputs.cornerRoot a t ha ht)
      (fun jk : Fin a × Fin t => eigenvalue a t jk.1 jk.2)]
  · rw [prod_nonzero_rectangleEigenvalues ha ht]
    simp only [Fintype.card_prod, Fintype.card_fin]
  · simp [ProductInputs.cornerRoot, eigenvalue]
    norm_num

private theorem map_lapMatrix_int_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Int.castRingHom ℝ).mapMatrix (G.lapMatrix ℤ) = G.lapMatrix ℝ := by
  ext i j
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply]

private theorem map_rectangleReducedLapMatrix (a t : ℕ) (root : Fin a × Fin t) :
    (Int.castRingHom ℝ).mapMatrix (rectangleReducedLapMatrix a t root) =
      ((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
        (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t)
        (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t) := by
  classical
  ext u v
  have hmap := congrArg
    (fun M : Matrix (Fin a × Fin t) (Fin a × Fin t) ℝ => M u.1 v.1)
    (map_lapMatrix_int_real (pathGraph a □ pathGraph t))
  simpa [rectangleReducedLapMatrix, reducedLapMatrix, RingHom.mapMatrix_apply,
    Matrix.map_apply] using hmap

private theorem det_rectangleReducedLapMatrix_cast (a t : ℕ)
    (root : Fin a × Fin t) :
    (((rectangleReducedLapMatrix a t root).det : ℤ) : ℝ) =
      (((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
        (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t)
        (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t)).det := by
  calc
    (((rectangleReducedLapMatrix a t root).det : ℤ) : ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (rectangleReducedLapMatrix a t root)).det :=
      RingHom.map_det (Int.castRingHom ℝ) _
    _ = _ := by rw [map_rectangleReducedLapMatrix]

private theorem principalMinor_eq_tauRect
    (hMatrixTree : RectangleCofactorInput) {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t)
    (s : Finset (Fin a × Fin t))
    (hs : s ∈ Finset.univ.powersetCard (a * t - 1)) :
    (((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
      (Subtype.val : s → Fin a × Fin t)
      (Subtype.val : s → Fin a × Fin t)).det = (tauRect a t : ℝ) := by
  classical
  have hsdata := Finset.mem_powersetCard.mp hs
  have hscard : s.card = a * t - 1 := hsdata.2
  have hNpos : 0 < a * t := Nat.mul_pos ha ht
  have hcardlt : s.card < (Finset.univ : Finset (Fin a × Fin t)).card := by
    simp only [hscard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨root, _hrootUniv, hroot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hs_eq : s = (Finset.univ : Finset (Fin a × Fin t)).erase root := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun hvr => hroot (hvr ▸ hv)
    · simp [Finset.card_erase_of_mem, hscard]
  let e : s ≃ {v : Fin a × Fin t // v ≠ root} :=
    (Equiv.refl (Fin a × Fin t)).subtypeEquiv (fun v => by simp [hs_eq])
  let reducedReal :=
    ((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
      (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t)
      (Subtype.val : {v : Fin a × Fin t // v ≠ root} → Fin a × Fin t)
  have hreindex :
      ((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
          (Subtype.val : s → Fin a × Fin t)
          (Subtype.val : s → Fin a × Fin t) =
        reducedReal.submatrix e e := by
    ext u v
    rfl
  calc
    (((pathGraph a □ pathGraph t).lapMatrix ℝ).submatrix
        (Subtype.val : s → Fin a × Fin t)
        (Subtype.val : s → Fin a × Fin t)).det =
        (reducedReal.submatrix e e).det := by rw [hreindex]
    _ = reducedReal.det := Matrix.det_submatrix_equiv_self e reducedReal
    _ = (((rectangleReducedLapMatrix a t root).det : ℤ) : ℝ) := by
      symm
      exact det_rectangleReducedLapMatrix_cast a t root
    _ = (tauRect a t : ℝ) := by
      exact_mod_cast (hMatrixTree a t ha ht root).symm

theorem rectangleLaplacian_charpoly_coeff_one_eq_tau
    (hMatrixTree : RectangleCofactorInput) {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t) :
    ((pathGraph a □ pathGraph t).lapMatrix ℝ).charpoly.coeff 1 =
      (-1 : ℝ) ^ (a * t - 1) * ((a * t : ℕ) : ℝ) * (tauRect a t : ℝ) := by
  classical
  let L := (pathGraph a □ pathGraph t).lapMatrix ℝ
  let k := a * t - 1
  have hNpos : 0 < a * t := Nat.mul_pos ha ht
  have hk : k ≤ Fintype.card (Fin a × Fin t) := by
    simp only [k, Fintype.card_prod, Fintype.card_fin]
    omega
  have hcoeff := Matrix.charpoly_coeff_eq_sum_minors L k hk
  have hindex : Fintype.card (Fin a × Fin t) - k = 1 := by
    simp only [k, Fintype.card_prod, Fintype.card_fin]
    omega
  have hchoose : Nat.choose (a * t) (a * t - 1) = a * t := by
    rw [← Nat.choose_symm (Nat.sub_le (a * t) 1)]
    have hsub : a * t - (a * t - 1) = 1 := by omega
    rw [hsub, Nat.choose_one_right]
  have hsum :
      (∑ s ∈ Finset.univ.powersetCard k,
          (L.submatrix (Subtype.val : s → Fin a × Fin t)
            (Subtype.val : s → Fin a × Fin t)).det) =
        ((a * t : ℕ) : ℝ) * (tauRect a t : ℝ) := by
    calc
      (∑ s ∈ Finset.univ.powersetCard k,
          (L.submatrix (Subtype.val : s → Fin a × Fin t)
            (Subtype.val : s → Fin a × Fin t)).det) =
          ∑ _s ∈ Finset.univ.powersetCard k, (tauRect a t : ℝ) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact principalMinor_eq_tauRect hMatrixTree ha ht s (by simpa [k] using hs)
      _ = ((a * t : ℕ) : ℝ) * (tauRect a t : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        rw [show k = a * t - 1 from rfl, hchoose]
  rw [hindex, hsum] at hcoeff
  simpa only [L, k, mul_assoc] using hcoeff

/-- The Matrix--Tree cofactor, combined with the explicit cosine
diagonalization above, is the normalized product of the nonzero rectangular
Laplacian eigenvalues. -/
theorem tauRect_eq_fullSpectralTreeProduct
    (hMatrixTree : RectangleCofactorInput) {a t : ℕ}
    (ha : 0 < a) (ht : 0 < t) :
    (tauRect a t : ℝ) = fullSpectralTreeProduct a t := by
  have hcompare :=
    (rectangleLaplacian_charpoly_coeff_one ha ht).symm.trans
      (rectangleLaplacian_charpoly_coeff_one_eq_tau hMatrixTree ha ht)
  have hsign : (-1 : ℝ) ^ (a * t - 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hproduct :
      ((a * t : ℕ) : ℝ) * (tauRect a t : ℝ) =
        zeroRowProduct t *
          ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j := by
    symm
    apply mul_left_cancel₀ hsign
    simpa only [mul_assoc] using hcompare
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hvertices : (a : ℝ) * (t : ℝ) ≠ 0 := mul_ne_zero ha0 ht0
  rw [fullSpectralTreeProduct]
  calc
    (tauRect a t : ℝ) =
        ((a : ℝ) * (t : ℝ))⁻¹ *
          ((a : ℝ) * (t : ℝ) * (tauRect a t : ℝ)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hvertices, one_mul]
    _ = ((a : ℝ) * (t : ℝ))⁻¹ *
          (zeroRowProduct t *
            ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j) := by
          rw [← Nat.cast_mul, hproduct]
    _ = ((a : ℝ) * (t : ℝ))⁻¹ * zeroRowProduct t *
          ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j := by
          rw [mul_assoc]

/-- The exact spectral cofactor input is constructed from the rectangular
Matrix--Tree interface; no additional spectral assumption remains. -/
theorem rectangularSpectralCofactor
    (hMatrixTree : RectangleCofactorInput) :
    ProductInputs.RectangularSpectralCofactorInput := by
  intro a t ha ht
  have hcofactor :=
    hMatrixTree a t ha ht (ProductInputs.cornerRoot a t ha ht)
  calc
    (((rectangleReducedLapMatrix a t
        (ProductInputs.cornerRoot a t ha ht)).det : ℤ) : ℝ) =
        (tauRect a t : ℝ) := by exact_mod_cast hcofactor.symm
    _ = fullSpectralTreeProduct a t :=
      tauRect_eq_fullSpectralTreeProduct hMatrixTree ha ht

end

end SquareMaximality.Rectangle.Spectral
