module

public import SpanningTreeIsoperimetry.BoundaryProfileTransfer
public import SpanningTreeIsoperimetry.BoundarySingletonIntegral
public import SpanningTreeIsoperimetry.ShortDefectPolynomials
public import SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge

@[expose] public section

/-! Actual small-defect lower densities factor as the singleton density times
the checked inverse-quadrant quadratic polynomials. -/
namespace SpanningTreeIsoperimetry.ShortDefectDensities
open Ferrers CornerEnergy CornerStripBridge BoundaryGreenLoss BoundaryGreenBounds
  QuadrantLowerTrace BoundaryLowerIntegral BoundaryLayerGreen BoundaryGreenPolynomials
  BoundaryKernelMajorant BoundarySingletonIntegral BoundarySingletonWeight RectangularRemainder
  ShortDefectPolynomials Filter Set
open scoped Classical BigOperators Matrix Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem twoRow_quadrant (p q : Fin 3 × Fin 2) :
    quadrantGreen (p.1.val,p.2.val) (q.1.val,q.2.val)=twoRowValue t0 p q := by
  have hq := (green_tendsto_quadrant (p.1.val,p.2.val) (q.1.val,q.2.val)).comp (tendsto_add_atTop_nat 4)
  have he (N : ℕ) : green (box (N+4)) (p.1.val,p.2.val) (q.1.val,q.2.val)=twoRowFinite N p q := by
    have hb : box (N+4)=BoundaryLayerGreen.window N := by
      unfold box BoundaryLayerGreen.window QuadrantBoundaryGreen.window
      rw [foundation_faceIndices]
    have hp : (p.1.val,p.2.val)∈BoundaryLayerGreen.window N := (twoRowSite N p).property
    have hq : (q.1.val,q.2.val)∈BoundaryLayerGreen.window N := (twoRowSite N q).property
    rw [hb,green_mem hp hq]
    rfl
  have hv := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp twoRowFinite_tendsto p) q
  apply tendsto_nhds_unique hq
  exact hv.congr (fun N => (he N).symm)

def twoEquiv := FiniteBoundaryMinorBridge.verticalEquiv 2
def fourEquiv : Fin 4 ≃ {p // p∈faceRectangle 2 2} :=
  (Equiv.swap (1 : Fin 4) 2).trans SmallCornerEnergies.squareEquiv

def twoPoints : Fin 2 → Fin 3 × Fin 2 := ![(0,0),(0,1)]
def fourPoints : Fin 4 → Fin 3 × Fin 2 := ![(0,0),(1,0),(0,1),(1,1)]

theorem twoEquiv_point (i : Fin 2) : (twoEquiv i).val=((twoPoints i).1.val,(twoPoints i).2.val) := by
  fin_cases i <;> rfl

theorem fourEquiv_point (i : Fin 4) : (fourEquiv i).val=((fourPoints i).1.val,(fourPoints i).2.val) := by
  fin_cases i <;> rfl

theorem two_minor : (minor (verticalDiagram 2)).submatrix twoEquiv twoEquiv=twoMatrix t0 := by
  have he : (minor (verticalDiagram 2)).submatrix twoEquiv twoEquiv=
      (twoRowValue t0).submatrix twoPoints twoPoints := by
    ext i j
    change quadrantGreen (twoEquiv i).val (twoEquiv j).val=_
    rw [twoEquiv_point,twoEquiv_point]
    exact twoRow_quadrant _ _
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.submatrix_apply,twoPoints,twoMatrix,a,b,c,twoRowValue,crossValue,upperValue,
      cornerEntry,planeEntry,lowerIndex,nextIndex,prevIndex,Nat.dist] <;> ring

theorem four_minor : (minor (faceRectangle 2 2)).submatrix fourEquiv fourEquiv=SmallGreenPolynomials.squareMatrix t0 := by
  have he : (minor (faceRectangle 2 2)).submatrix fourEquiv fourEquiv=
      (twoRowValue t0).submatrix fourPoints fourPoints := by
    ext i j
    change quadrantGreen (fourEquiv i).val (fourEquiv j).val=_
    rw [fourEquiv_point,fourEquiv_point]
    exact twoRow_quadrant _ _
  rw [he,SmallGreenPolynomials.squareMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.submatrix_apply,fourPoints,SmallGreenPolynomials.squareLiteral,twoRowValue,
      crossValue,upperValue,cornerEntry,planeEntry,lowerIndex,nextIndex,prevIndex,Nat.dist] <;> ring

theorem inverse_quadratic_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ κ ℝ) (v : κ → ℝ) (e : ι ≃ κ) :
    (v ∘ e) ⬝ᵥ ((A.submatrix e e)⁻¹ *ᵥ (v ∘ e))=v ⬝ᵥ (A⁻¹ *ᵥ v) := by
  rw [Matrix.inv_submatrix_equiv,Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ e) ∘ e.symm=v := by funext i; simp
  rw [he]
  exact comp_equiv_dotProduct_comp_equiv _ _ e

theorem two_rawMode (θ : ℝ) : rawMode (verticalDiagram 2) θ ∘ twoEquiv=
    (Real.sin θ*Real.sinh (gamma θ)) • twoVector (Real.cosh (gamma θ)-1) := by
  have hc : Real.cos θ=2-Real.cosh (gamma θ) := by linarith [cosh_gamma θ]
  funext i
  rw [Function.comp_apply]
  unfold rawMode
  rw [twoEquiv_point]
  fin_cases i <;> norm_num [twoPoints,twoVector,Pi.smul_apply,smul_eq_mul,Real.sin_two_mul,hc] <;> ring

theorem four_rawMode (θ : ℝ) : rawMode (faceRectangle 2 2) θ ∘ fourEquiv=
    (Real.sin θ*Real.sinh (gamma θ)) • fourVector (Real.cosh (gamma θ)-1) := by
  have hc : Real.cos θ=2-Real.cosh (gamma θ) := by linarith [cosh_gamma θ]
  funext i
  rw [Function.comp_apply]
  unfold rawMode
  rw [fourEquiv_point]
  fin_cases i <;> norm_num [fourPoints,fourVector,Pi.smul_apply,smul_eq_mul,
    Real.sin_two_mul,Real.sinh_two_mul,hc] <;> ring

theorem densityTrace_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℕ) {M : Diagram} (e : ι ≃ {p // p∈M}) (A : Matrix ι ι ℝ) (v : ι → ℝ)
    {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi)
    (hA : (minor M).submatrix e e=A)
    (hv : rawMode M θ ∘ e=(Real.sin θ*Real.sinh (gamma θ)) • v) :
    densityTrace R M θ=density ((R : ℝ)+1) 1 1 1 1 θ*(v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
  have hg := BoundaryKernelBounds.gamma_pos hθ
  have hs : Real.sinh (gamma θ)≠0 := (Real.sinh_pos_iff.mpr hg).ne'
  have he : Real.exp (2*((R : ℝ)+1)*gamma θ)-1≠0 := by
    have hh := Real.one_lt_exp_iff.mpr (show 0 < 2*((R : ℝ)+1)*gamma θ by positivity)
    linarith
  rw [densityTrace_eq_quadratic]
  simp only [star_trivial]
  rw [← inverse_quadratic_reindex (minor M) (rawMode M θ) e,hA,hv,
    Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  rw [density_singleton_eq]
  field_simp
  <;> ring

theorem two_density (R : ℕ) {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) :
    densityTrace R (verticalDiagram 2) θ=density ((R : ℝ)+1) 1 1 1 1 θ*
      (twoVector (Real.cosh (gamma θ)-1) ⬝ᵥ
        ((twoMatrix t0)⁻¹ *ᵥ twoVector (Real.cosh (gamma θ)-1))) :=
  densityTrace_factor R twoEquiv _ _ hθ two_minor (two_rawMode θ)

theorem square_density (R : ℕ) {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) :
    densityTrace R (faceRectangle 2 2) θ=density ((R : ℝ)+1) 1 1 1 1 θ*
      (fourVector (Real.cosh (gamma θ)-1) ⬝ᵥ
        ((SmallGreenPolynomials.squareMatrix t0)⁻¹ *ᵥ fourVector (Real.cosh (gamma θ)-1))) :=
  densityTrace_factor R fourEquiv _ _ hθ four_minor (four_rawMode θ)

end
end SpanningTreeIsoperimetry.ShortDefectDensities
