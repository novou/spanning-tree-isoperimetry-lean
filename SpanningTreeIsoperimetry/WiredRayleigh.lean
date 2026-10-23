module

public import SquareMaximality.Multigraph.TransferCurrentConstruction
public import SquareMaximality.Inputs.MatrixTreeTheorem
public import SpanningTreeIsoperimetry.InteriorSurcharge
public import SpanningTreeIsoperimetry.AvoidanceDeterminant

@[expose] public section

/-!
# Rayleigh comparison under vertex wiring

Wiring may identify vertices; the comparison is therefore expressed through
pullback of potentials, rather than an injective map on vertices. Edge labels
that retain two distinct endpoints remain distinct. This module supplies the
matrix and finite-energy comparison used for two simultaneous currents.
-/

set_option backward.isDefEq.respectTransparency false

namespace SpanningTreeIsoperimetry.WiredRayleigh

open SquareMaximality SquareMaximality.Multigraph
open scoped BigOperators Matrix

noncomputable section

/-- A potential pullback can be rectangular and need not be injective. The
Schur-complement argument gives the corresponding inverse-energy comparison. -/
theorem inverse_compression {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} (P : Matrix m n ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hEnergy : (B - Pᴴ * A * P).PosSemidef) :
    (A⁻¹ - P * B⁻¹ * Pᴴ).PosSemidef := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible A⁻¹ := hA.inv.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hblock : (Matrix.fromBlocks A⁻¹ P Pᴴ B).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₁₁ P B hA.inv).mpr
    simpa only [Matrix.inv_inv_of_invertible] using hEnergy
  exact (Matrix.PosDef.fromBlocks₂₂ A⁻¹ P hB).mp hblock

/-- The simultaneous response matrix of a finite family of current vectors. -/
def response {m k : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (C : Matrix m k ℝ) : Matrix k k ℝ := Cᴴ * A⁻¹ * C

/-- The inverse-energy comparison holds simultaneously for every current
combination, and hence in positive-semidefinite matrix order. -/
theorem response_compression {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} (P : Matrix m n ℝ) (C : Matrix m k ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hEnergy : (B - Pᴴ * A * P).PosSemidef) :
    (response A C - response B (Pᴴ * C)).PosSemidef := by
  have h := (inverse_compression P hA hB hEnergy).conjTranspose_mul_mul_same C
  simpa only [response, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

/-- A positive avoidance determinant increases when the current kernel
 decreases in matrix order. -/
theorem determinant_complement_mono {k : Type*} [Fintype k] [DecidableEq k]
    {K L : Matrix k k ℝ} (hK : (1 - K).PosDef) (hKL : (K - L).PosSemidef) :
    (1 - K).det ≤ (1 - L).det := by
  have hL : (1 - L).PosDef := by
    have h := hK.add_posSemidef hKL
    have heq : (1 - K) + (K - L) = 1 - L := by noncomm_ring
    rwa [heq] at h
  apply HadamardFischer.det_le_det_of_posSemidef_sub_of_posDef_right hK.posSemidef
    (show ((1 - L) - (1 - K)).PosSemidef from ?_) hL
  simpa only [sub_sub_sub_cancel_left] using hKL

/-- A finite vertex wiring retains all edge labels whose endpoints remain
 distinct. Edges collapsed to loops contribute no Dirichlet energy. -/
structure Wiring {V W E F : Type*} (G : LabeledMultigraph V E) (H : LabeledMultigraph W F) where
  vertexMap : V → W
  edgeMap : {e : E // ¬(Sym2.map vertexMap (G.ends e)).IsDiag} ↪ F
  map_ends (e : {e : E // ¬(Sym2.map vertexMap (G.ends e)).IsDiag}) :
    H.ends (edgeMap e) = Sym2.map vertexMap (G.ends e)

/-- Labelled-edge Dirichlet energy; loops vanish and parallel edges count
separately. -/
def edgeEnergy {V E : Type*} [Fintype E] (G : LabeledMultigraph V E) (f : V → ℝ) : ℝ :=
  ∑ e, (f (G.edgeSource e) - f (G.edgeTarget e)) ^ 2

namespace Wiring
variable {V W E F : Type*} [Fintype E] [Fintype F]
  {G : LabeledMultigraph V E} {H : LabeledMultigraph W F} (d : Wiring G H)

private theorem active_iff (e : E) :
    ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag ↔
      d.vertexMap (G.edgeSource e) ≠ d.vertexMap (G.edgeTarget e) := by
  rw [G.ends_edgeSource_edgeTarget]
  simp

private theorem energy_term (f : W → ℝ)
    (e : {e : E // ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag}) :
    (f (d.vertexMap (G.edgeSource e.1)) - f (d.vertexMap (G.edgeTarget e.1))) ^ 2 =
      (f (H.edgeSource (d.edgeMap e)) - f (H.edgeTarget (d.edgeMap e))) ^ 2 := by
  have hp := d.map_ends e
  rw [H.ends_edgeSource_edgeTarget, G.ends_edgeSource_edgeTarget] at hp
  simp only [Sym2.map_mk] at hp
  rcases Sym2.eq_iff.mp hp with hp | hp
  · rcases hp with ⟨hp1, hp2⟩
    rw [hp1, hp2]
  · rcases hp with ⟨hp1, hp2⟩
    rw [hp1, hp2]
    ring

/-- Pullback across a wiring can only decrease the labelled Dirichlet energy.
No injectivity of the vertex map is required. -/
theorem energy_pullback_le (f : W → ℝ) :
    edgeEnergy G (f ∘ d.vertexMap) ≤ edgeEnergy H f := by
  classical
  let active : E → Prop := fun e => ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag
  let term : E → ℝ := fun e =>
    (f (d.vertexMap (G.edgeSource e)) - f (d.vertexMap (G.edgeTarget e))) ^ 2
  have hinactive : (∑ e : {e : E // ¬active e}, term e) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have heq : d.vertexMap (G.edgeSource e.1) = d.vertexMap (G.edgeTarget e.1) := by
      have h := (d.active_iff e.1).not.mp e.2
      simpa only [not_not] using h
    simp [term, heq]
  have hsplit := Fintype.sum_subtype_add_sum_subtype active term
  rw [hinactive, add_zero] at hsplit
  change (∑ e, term e) ≤ _
  rw [← hsplit]
  apply Finset.sum_le_sum_of_injOn d.edgeMap d.edgeMap.injective.injOn (Finset.subset_univ _)
  · intro e _
    exact (d.energy_term f e).le
  · intro e _ _
    exact sq_nonneg _

end Wiring

/-- A potential normalized to zero at the root. -/
def extendPotential {V : Type*} [DecidableEq V] (root : V)
    (x : LabeledMultigraph.AwayFrom root → ℝ) (v : V) : ℝ :=
  if h : v ≠ root then x ⟨v, h⟩ else 0

@[simp] theorem extendPotential_root {V : Type*} [DecidableEq V] (root : V)
    (x : LabeledMultigraph.AwayFrom root → ℝ) : extendPotential root x root = 0 := by
  simp [extendPotential]

@[simp] theorem extendPotential_away {V : Type*} [DecidableEq V] (root : V)
    (x : LabeledMultigraph.AwayFrom root → ℝ) (v : LabeledMultigraph.AwayFrom root) :
    extendPotential root x v.1 = x v := by simp [extendPotential, v.2]

private theorem indicator_sum {V : Type*} [Fintype V] [DecidableEq V] (root a : V)
    (x : LabeledMultigraph.AwayFrom root → ℝ) :
    (∑ v : LabeledMultigraph.AwayFrom root, (if v.1 = a then (1 : ℝ) else 0) * x v) =
      extendPotential root x a := by
  classical
  by_cases ha : a = root
  · subst a
    rw [extendPotential_root]
    apply Finset.sum_eq_zero
    intro v _
    simp [v.2]
  · rw [Finset.sum_eq_single ⟨a, ha⟩]
    · simp [extendPotential, ha]
    · intro v _ hv
      have hva : v.1 ≠ a := fun h => hv (Subtype.ext h)
      simp [hva]
    · simp

/-- Reduced incidence applied to a rooted potential gives the edge voltage. -/
theorem reduced_gradient {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : LabeledMultigraph V E) (root : V) (x : LabeledMultigraph.AwayFrom root → ℝ) (e : E) :
    ((G.reducedSignedIncidence root)ᵀ *ᵥ x) e =
      extendPotential root x (G.edgeSource e) - extendPotential root x (G.edgeTarget e) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    LabeledMultigraph.reducedSignedIncidence_apply, sub_mul, Finset.sum_sub_distrib]
  convert congrArg₂ (fun a b : ℝ => a - b)
    (indicator_sum root (G.edgeSource e) x) (indicator_sum root (G.edgeTarget e) x) using 1 <;>
    congr 1
  all_goals
    apply Finset.sum_congr
    · ext v
      simp
    · intro v hv
      split_ifs <;> rfl

/-- The combinatorial energy equals the reduced-Laplacian quadratic form. -/
theorem edgeEnergy_eq_quadratic {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : LabeledMultigraph V E) (root : V) (x : LabeledMultigraph.AwayFrom root → ℝ) :
    edgeEnergy G (extendPotential root x) = x ⬝ᵥ (G.reducedLaplacian ℝ root *ᵥ x) := by
  let B := G.reducedSignedIncidence root
  rw [← G.reducedSignedIncidence_mul_transpose root, ← Matrix.mulVec_mulVec]
  have h := Matrix.dotProduct_transpose_mulVec B (Bᵀ *ᵥ x) x
  rw [← h]
  simp only [edgeEnergy, dotProduct, B, reduced_gradient, pow_two]

section Graph
variable {V W E F : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W

/-- Pullback of rooted potentials, including the constant shift needed when
source and target roots do not correspond. -/
def potentialPullback (φ : V → W) (rootV : V) (rootW : W) :
    Matrix (LabeledMultigraph.AwayFrom rootV) (LabeledMultigraph.AwayFrom rootW) ℝ :=
  fun v w => (if w.1 = φ v.1 then 1 else 0) - (if w.1 = φ rootV then 1 else 0)

theorem potentialPullback_mulVec (φ : V → W) (rootV : V) (rootW : W)
    (x : LabeledMultigraph.AwayFrom rootW → ℝ) (v : LabeledMultigraph.AwayFrom rootV) :
    (potentialPullback φ rootV rootW *ᵥ x) v =
      extendPotential rootW x (φ v.1) - extendPotential rootW x (φ rootV) := by
  simp only [Matrix.mulVec, dotProduct, potentialPullback, sub_mul, Finset.sum_sub_distrib]
  rw [indicator_sum, indicator_sum]

theorem extendPotential_pullback (φ : V → W) (rootV : V) (rootW : W)
    (x : LabeledMultigraph.AwayFrom rootW → ℝ) (v : V) :
    extendPotential rootV (potentialPullback φ rootV rootW *ᵥ x) v =
      extendPotential rootW x (φ v) - extendPotential rootW x (φ rootV) := by
  by_cases hv : v = rootV
  · subst v
    simp
  · rw [extendPotential, dif_pos hv]
    exact potentialPullback_mulVec φ rootV rootW x ⟨v,hv⟩

private theorem edgeEnergy_sub_const (G : LabeledMultigraph V E) (f : V → ℝ) (c : ℝ) :
    edgeEnergy G (fun v => f v - c) = edgeEnergy G f := by
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  ring

private theorem reducedLaplacian_posSemidef (G : LabeledMultigraph V E) (root : V) :
    (G.reducedLaplacian ℝ root).PosSemidef := by
  rw [← G.reducedSignedIncidence_mul_transpose root]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (G.reducedSignedIncidence root)

/-- The concrete wiring fields imply the matrix energy inequality required
by inverse compression; this is proved, not an additional wiring assumption. -/
theorem Wiring.pullback_energy_posSemidef {G : LabeledMultigraph V E} {H : LabeledMultigraph W F}
    (d : Wiring G H) (rootG : V) (rootH : W) :
    (H.reducedLaplacian ℝ rootH -
      (potentialPullback d.vertexMap rootG rootH)ᴴ * G.reducedLaplacian ℝ rootG *
        potentialPullback d.vertexMap rootG rootH).PosSemidef := by
  let P := potentialPullback d.vertexMap rootG rootH
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (reducedLaplacian_posSemidef H rootH).isHermitian.sub
      (Matrix.isHermitian_conjTranspose_mul_mul P
        (reducedLaplacian_posSemidef G rootG).isHermitian)
  · intro x
    have he := d.energy_pullback_le (extendPotential rootH x)
    have hp : edgeEnergy G ((extendPotential rootH x) ∘ d.vertexMap) =
        edgeEnergy G (extendPotential rootG (P *ᵥ x)) := by
      symm
      rw [show extendPotential rootG (P *ᵥ x) =
          (fun v => extendPotential rootH x (d.vertexMap v) -
            extendPotential rootH x (d.vertexMap rootG)) by
        funext v; exact extendPotential_pullback d.vertexMap rootG rootH x v]
      exact edgeEnergy_sub_const G _ _
    rw [hp, edgeEnergy_eq_quadratic, edgeEnergy_eq_quadratic] at he
    have hfactor : x ⬝ᵥ ((Pᴴ * G.reducedLaplacian ℝ rootG * P) *ᵥ x) =
        (P *ᵥ x) ⬝ᵥ (G.reducedLaplacian ℝ rootG *ᵥ (P *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    rw [hfactor]
    exact sub_nonneg.mpr he

/-- Wiring decreases the full simultaneous-current response matrix. -/
theorem Wiring.response_order {G : LabeledMultigraph V E} {H : LabeledMultigraph W F}
    (d : Wiring G H) (rootG : V) (rootH : W) {k : Type*} [Fintype k]
    (C : Matrix (LabeledMultigraph.AwayFrom rootG) k ℝ)
    (hG : 0 < G.spanningTreeCount) (hH : 0 < H.spanningTreeCount) :
    (response (G.reducedLaplacian ℝ rootG) C -
      response (H.reducedLaplacian ℝ rootH)
        ((potentialPullback d.vertexMap rootG rootH)ᴴ * C)).PosSemidef := by
  exact response_compression (potentialPullback d.vertexMap rootG rootH) C
    (G.reducedLaplacian_posDef labeledMultigraphCofactorInput hG rootG)
    (H.reducedLaplacian_posDef labeledMultigraphCofactorInput hH rootH)
    (d.pullback_energy_posSemidef rootG rootH)

/-- The avoidance determinant is independent of the orientation and indexing
of deleted-edge current columns; only their Gram update matters. -/
theorem avoidanceRatio_eq_response_of_gram (G : LabeledMultigraph V E)
    (root : V) (A : Finset E) {k : Type*} [Fintype k] [DecidableEq k]
    (C : Matrix (LabeledMultigraph.AwayFrom root) k ℝ)
    (hCount : 0 < G.spanningTreeCount)
    (hGram : C * Cᵀ = G.selectedIncidence root A * (G.selectedIncidence root A)ᵀ) :
    G.avoidanceRatio A = (1 - response (G.reducedLaplacian ℝ root) C).det := by
  have hL := G.reducedLaplacian_posDef labeledMultigraphCofactorInput hCount root
  have hunit : IsUnit (G.reducedLaplacian ℝ root).det := isUnit_iff_ne_zero.mpr hL.det_pos.ne'
  have hdet := Matrix.det_add_mul (A := G.reducedLaplacian ℝ root) (-C) Cᵀ hunit
  simp only [Matrix.neg_mul, Matrix.mul_neg, ← sub_eq_add_neg] at hdet
  have hdelete : ((G.loopDelete root A).reducedLaplacian ℝ root).det =
      (G.reducedLaplacian ℝ root).det * (1 - response (G.reducedLaplacian ℝ root) C).det := by
    rw [G.loopDelete_laplacian, ← hGram]
    simpa only [response, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hdet
  unfold LabeledMultigraph.avoidanceRatio
  rw [← G.loopDelete_treeCount root A,
    (G.loopDelete root A).spanningTreeCount_eq_det_real root,
    G.spanningTreeCount_eq_det_real root, hdelete]
  field_simp [hL.det_pos.ne']

end Graph

section Currents
variable {V W E F : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W
local instance : DecidableEq E := Classical.decEq E
local instance : DecidableEq F := Classical.decEq F

/-- A family of oriented unit current dipoles, with the root coordinate omitted. -/
def currentMatrix {k : Type*} (root : V) (a b : k → V) :
    Matrix (LabeledMultigraph.AwayFrom root) k ℝ :=
  fun v i => (if v.1 = a i then 1 else 0) - (if v.1 = b i then 1 else 0)

private theorem extendPotential_pullback_column (φ : V → W) (rootV : V) (rootW : W)
    (w : LabeledMultigraph.AwayFrom rootW) (v : V) :
    extendPotential rootV (fun u => potentialPullback φ rootV rootW u w) v =
      (if w.1 = φ v then (1 : ℝ) else 0) - (if w.1 = φ rootV then 1 else 0) := by
  by_cases hv : v = rootV
  · subst v
    simp
  · simp [extendPotential, potentialPullback, hv]

/-- Adjoint potential pullback pushes current dipoles to their wired endpoints. -/
theorem transport_currentMatrix (φ : V → W) (rootV : V) (rootW : W)
    {k : Type*} (a b : k → V) :
    (potentialPullback φ rootV rootW)ᴴ * currentMatrix rootV a b =
      currentMatrix rootW (φ ∘ a) (φ ∘ b) := by
  ext w i
  let P := potentialPullback φ rootV rootW
  have hsum (v : V) :
      (∑ u : LabeledMultigraph.AwayFrom rootV,
        P u w * (if u.1 = v then (1 : ℝ) else 0)) =
        extendPotential rootV (fun u => P u w) v := by
    simpa only [mul_comm] using indicator_sum rootV v (fun u => P u w)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, currentMatrix,
    mul_sub, Finset.sum_sub_distrib]
  change (∑ u, P u w * (if u.1 = a i then 1 else 0)) -
    (∑ u, P u w * (if u.1 = b i then 1 else 0)) = _
  rw [hsum, hsum]
  change extendPotential rootV (fun u => potentialPullback φ rootV rootW u w) (a i) -
    extendPotential rootV (fun u => potentialPullback φ rootV rootW u w) (b i) = _
  rw [extendPotential_pullback_column, extendPotential_pullback_column]
  simp only [Function.comp_apply]
  ring

namespace Wiring
variable {G : LabeledMultigraph V E} {H : LabeledMultigraph W F} (d : Wiring G H)
  (A : Finset E) (hActive : ∀ e ∈ A, ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag)

/-- Surviving selected labels map injectively, including boundary-parallel labels. -/
def selectedLabelMap : A ↪ F where
  toFun e := d.edgeMap ⟨e.1,hActive e.1 e.2⟩
  inj' e f h := by
    have he := d.edgeMap.injective h
    apply Subtype.ext
    exact congrArg (fun z : {e : E // ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag} => z.1) he

def selectedLabels : Finset F := A.attach.image (d.selectedLabelMap A hActive)

def selectedLabelEquiv : A ≃ d.selectedLabels A hActive :=
  Equiv.ofBijective
    (fun e => ⟨d.selectedLabelMap A hActive e,
      Finset.mem_image.mpr ⟨e,Finset.mem_attach A e,rfl⟩⟩)
    ⟨fun e f h => (d.selectedLabelMap A hActive).injective (congrArg Subtype.val h), by
      intro f
      obtain ⟨e,_,he⟩ := Finset.mem_image.mp f.2
      exact ⟨e,Subtype.ext he⟩⟩

/-- A target selected-current column may reverse orientation. Its pairwise
outer products agree with the canonical target incidence column. -/
private theorem current_outer_product (rootH : W)
    (u v : LabeledMultigraph.AwayFrom rootH) (e : A) :
    currentMatrix rootH (fun j : A => d.vertexMap (G.edgeSource j.1))
        (fun j : A => d.vertexMap (G.edgeTarget j.1)) u e *
      currentMatrix rootH (fun j : A => d.vertexMap (G.edgeSource j.1))
        (fun j : A => d.vertexMap (G.edgeTarget j.1)) v e =
      H.reducedSignedIncidence rootH u (d.selectedLabelMap A hActive e) *
        H.reducedSignedIncidence rootH v (d.selectedLabelMap A hActive e) := by
  have hp := d.map_ends ⟨e.1,hActive e.1 e.2⟩
  rw [H.ends_edgeSource_edgeTarget, G.ends_edgeSource_edgeTarget, Sym2.map_mk] at hp
  simp only [currentMatrix, LabeledMultigraph.reducedSignedIncidence_apply]
  change _ =
    ((if u.1 = H.edgeSource (d.edgeMap ⟨e.1,hActive e.1 e.2⟩) then 1 else 0) -
      (if u.1 = H.edgeTarget (d.edgeMap ⟨e.1,hActive e.1 e.2⟩) then 1 else 0)) *
    ((if v.1 = H.edgeSource (d.edgeMap ⟨e.1,hActive e.1 e.2⟩) then 1 else 0) -
      (if v.1 = H.edgeTarget (d.edgeMap ⟨e.1,hActive e.1 e.2⟩) then 1 else 0))
  rcases Sym2.eq_iff.mp hp with hp | hp
  · rw [hp.1,hp.2]
  · rw [hp.1,hp.2]
    ring

/-- The wired current matrix has exactly the Gram update of deleting the
corresponding target edge labels, without any orientation convention. -/
theorem transported_selected_gram (rootG : V) (rootH : W) :
    let C := (potentialPullback d.vertexMap rootG rootH)ᴴ * G.selectedIncidence rootG A
    C * Cᵀ = H.selectedIncidence rootH (d.selectedLabels A hActive) *
      (H.selectedIncidence rootH (d.selectedLabels A hActive))ᵀ := by
  dsimp only
  have hC : G.selectedIncidence rootG A =
      currentMatrix rootG (fun e : A => G.edgeSource e.1) (fun e : A => G.edgeTarget e.1) := rfl
  rw [hC, transport_currentMatrix]
  ext u v
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← (d.selectedLabelEquiv A hActive).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  exact d.current_outer_product A hActive rootH u v e

end Wiring
end Currents

section Avoidance
variable {V W E F : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W
local instance : DecidableEq E := Classical.decEq E
local instance : DecidableEq F := Classical.decEq F

private theorem selected_response (G : LabeledMultigraph V E) (root : V) (A : Finset E) :
    response (G.reducedLaplacian ℝ root) (G.selectedIncidence root A) =
      HadamardFischer.principalSubmatrix (G.reducedTransferKernel root) A := by
  simpa only [response, Matrix.conjTranspose_eq_transpose_of_trivial] using
    G.selectedIncidence_transfer root A

private theorem selected_complement (G : LabeledMultigraph V E) (root : V) (A : Finset E) :
    1 - response (G.reducedLaplacian ℝ root) (G.selectedIncidence root A) =
      HadamardFischer.principalSubmatrix (1 - G.reducedTransferKernel root) A := by
  rw [selected_response]
  ext e f
  simp only [Matrix.sub_apply, HadamardFischer.principalSubmatrix, Matrix.submatrix_apply,
    Matrix.one_apply]
  by_cases he : e = f
  · subst f
    simp
  · have hv : e.1 ≠ f.1 := fun h => he (Subtype.ext h)
    simp [he,hv]

private theorem selected_avoidance_determinant (G : LabeledMultigraph V E)
    (root : V) (A : Finset E) (hG : 0 < G.spanningTreeCount) :
    G.avoidanceRatio A =
      (1 - response (G.reducedLaplacian ℝ root) (G.selectedIncidence root A)).det := by
  rw [G.avoidanceRatio_eq_principalDet root A hG, selected_complement]
  rfl

/-- Actual UST avoidance probabilities increase under vertex wiring and
additional edges, provided selected edge labels survive distinctly. -/
theorem Wiring.avoidanceRatio_le {G : LabeledMultigraph V E} {H : LabeledMultigraph W F}
    (d : Wiring G H) (rootG : V) (rootH : W) (A : Finset E)
    (hActive : ∀ e ∈ A, ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag)
    (hG : 0 < G.spanningTreeCount) (hH : 0 < H.spanningTreeCount) :
    G.avoidanceRatio A ≤ H.avoidanceRatio (d.selectedLabels A hActive) := by
  by_cases hAvoid : 0 < G.avoidanceRatio A
  · let C := G.selectedIncidence rootG A
    let P := potentialPullback d.vertexMap rootG rootH
    have hPSD : (1 - response (G.reducedLaplacian ℝ rootG) C).PosSemidef := by
      rw [show C = G.selectedIncidence rootG A from rfl, selected_complement]
      exact (G.one_sub_reducedTransferKernel_posSemidef rootG hG).submatrix Subtype.val
    have hPD : (1 - response (G.reducedLaplacian ℝ rootG) C).PosDef := by
      apply hPSD.posDef_iff_det_ne_zero.mpr
      rw [show C = G.selectedIncidence rootG A from rfl, ← selected_avoidance_determinant G rootG A hG]
      exact ne_of_gt hAvoid
    have horder := d.response_order rootG rootH C hG hH
    have hdet := determinant_complement_mono hPD horder
    have htarget := avoidanceRatio_eq_response_of_gram H rootH
      (d.selectedLabels A hActive) (Pᴴ * C) hH
      (d.transported_selected_gram A hActive rootG rootH)
    calc
      G.avoidanceRatio A =
          (1 - response (G.reducedLaplacian ℝ rootG) C).det :=
        selected_avoidance_determinant G rootG A hG
      _ ≤ (1 - response (H.reducedLaplacian ℝ rootH) (Pᴴ * C)).det := hdet
      _ = H.avoidanceRatio (d.selectedLabels A hActive) := htarget.symm
  · apply (le_of_not_gt hAvoid).trans
    unfold LabeledMultigraph.avoidanceRatio
    positivity

end Avoidance

end
end SpanningTreeIsoperimetry.WiredRayleigh
