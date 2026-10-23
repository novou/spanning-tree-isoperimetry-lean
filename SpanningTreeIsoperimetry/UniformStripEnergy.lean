module

public import SpanningTreeIsoperimetry.GreenExhaustion
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-! Uniform strip-energy bound from actual finite Green minors and their
half-plane limit. No asymptotic determinant theorem is assumed. -/
namespace SpanningTreeIsoperimetry.UniformStripEnergy

open Ferrers CornerEnergy HalfPlaneWalks GreenExhaustion StripLoopBound
open SquareMaximality.Boundary Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def boundarySet {ι : Type*} [Fintype ι] (N : ℕ) (f : ι → Fin 6) : Diagram :=
  Finset.univ.image (fun i => (boundarySite N (f i)).val)

theorem boundarySet_subset {ι : Type*} [Fintype ι] (N : ℕ) (f : ι → Fin 6) :
    boundarySet N f ⊆ window N := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  exact (boundarySite N (f i)).property

def boundarySetEquiv {ι : Type*} [Fintype ι] (N : ℕ) (f : ι → Fin 6)
    (hf : Function.Injective f) : ι ≃ {p // p ∈ boundarySet N f} :=
  Equiv.ofBijective (fun i => ⟨(boundarySite N (f i)).val,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      apply hf
      apply Fin.ext
      have hx := congrArg (fun p : {p // p ∈ boundarySet N f} => p.val.1) h
      dsimp [boundarySite] at hx
      omega
    · intro p
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp p.property
      exact ⟨i,Subtype.ext hi⟩)

theorem boundarySet_green_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (f : ι → Fin 6) (hf : Function.Injective f) :
    Matrix.det (greenMinor (boundarySet_subset N f))=
      Matrix.det (fun i j => boundaryGreenEntry N (f i) (f j)) := by
  rw [← Matrix.det_submatrix_equiv_self (boundarySetEquiv N f hf)]
  congr 1

def leftIndex (i : Fin 3) : Fin 6 := indexSix (.inl i)
def rightIndex (i : Fin 3) : Fin 6 := indexSix (.inr i)

theorem leftIndex_injective : Function.Injective leftIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun t : Fin 6 => t.val) h

theorem rightIndex_injective : Function.Injective rightIndex := by
  intro i j h
  apply Fin.ext
  have hx := congrArg Fin.val h
  dsimp [rightIndex,indexSix] at hx
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem indexSix_injective : Function.Injective indexSix := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (leftIndex_injective h)
    | inr j => have hx:=congrArg Fin.val h; dsimp [indexSix] at hx; have hi:=i.isLt; have hj:=j.isLt; omega
  | inr i =>
    cases j with
    | inl j => have hx:=congrArg Fin.val h; dsimp [indexSix] at hx; have hi:=i.isLt; have hj:=j.isLt; omega
    | inr j => exact congrArg Sum.inr (rightIndex_injective h)

theorem boundarySet_left (N : ℕ) :
    boundarySet N leftIndex = {(N,0),(N+1,0),(N+2,0)} := by
  ext p
  simp only [boundarySet,Finset.mem_image,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [leftIndex,indexSix,boundarySite]
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem boundarySet_right (N : ℕ) :
    boundarySet N rightIndex = {(N+3,0),(N+4,0),(N+5,0)} := by
  ext p
  simp only [boundarySet,Finset.mem_image,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [rightIndex,indexSix,boundarySite]
  · rintro (rfl|rfl|rfl)
    · exact ⟨2,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨0,rfl⟩

theorem boundarySet_six (N : ℕ) :
    boundarySet N indexSix = boundarySet N leftIndex ∪ boundarySet N rightIndex := by
  ext p
  simp only [boundarySet,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i,hi⟩
    | inr i => exact Or.inr ⟨i,hi⟩
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Sum.inl i,hi⟩
    · exact ⟨Sum.inr i,hi⟩

theorem greenMinor_det_transport {U V M L : Diagram} (hU : U=V) (hM : M=L)
    (h : M ⊆ U) (h' : L ⊆ V) : Matrix.det (greenMinor h)=Matrix.det (greenMinor h') := by
  subst V
  subst L
  rfl

def correlation (N : ℕ) : ℝ :=
  Real.log (Matrix.det (boundaryLeftThree N))+
    Real.log (Matrix.det (boundaryRightThree N))-
      Real.log (Matrix.det (boundaryMatrixSix N))

theorem finite_comparison (k N : ℕ) :
    2*realEnergy (horizontalStrip k)+correlation N ≤
      SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2) := by
  let m := 2*N+6
  let n := N+1
  let V : Diagram := {(N+1,0),(N+2,0)}
  let W : Diagram := {(N+4,0),(N+5,0)}
  have heA : markedFaces m n V=boundarySet N leftIndex := by
    rw [boundarySet_left]
    exact markedFaces_boundaryPair m n N (by dsimp [m]; omega) (by dsimp [n]; omega)
  have heB : markedFaces m n W=boundarySet N rightIndex := by
    rw [boundarySet_right]
    have h := markedFaces_boundaryPair m n (N+3) (by dsimp [m]; omega) (by dsimp [n]; omega)
    convert h using 1
  have hV : ∀ p ∈ markedFaces m n V, p.2=0 ∧ p.1<N+3 := by
    rw [heA,boundarySet_left]
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff] at hp
    omega
  have hW : ∀ p ∈ markedFaces m n W, p.2=0 ∧ N+3≤p.1 := by
    rw [heB,boundarySet_right]
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff] at hp
    omega
  have hU : faceRectangle m n=window N := (foundation_faceIndices m n).symm
  have ht := strip_energy_le_finite_green k m n (N+3) V W hV hW
  dsimp only at ht
  have hA : markedFaces m n V ⊆ faceRectangle m n := by
    rw [heA,hU]; exact boundarySet_subset N leftIndex
  have hB : markedFaces m n W ⊆ faceRectangle m n := by
    rw [heB,hU]; exact boundarySet_subset N rightIndex
  have hdA := greenMinor_det_transport hU heA hA (boundarySet_subset N leftIndex)
  have hdB := greenMinor_det_transport hU heB hB (boundarySet_subset N rightIndex)
  have heAB : markedFaces m n V ∪ markedFaces m n W=boundarySet N indexSix := by
    rw [heA,heB,boundarySet_six]
  have hdAB := greenMinor_det_transport hU heAB (Finset.union_subset hA hB)
    (boundarySet_subset N indexSix)
  rw [hdA,hdB,hdAB,boundarySet_green_det N leftIndex leftIndex_injective,
    boundarySet_green_det N rightIndex rightIndex_injective,
    boundarySet_green_det N indexSix indexSix_injective] at ht
  exact ht

theorem correlation_tendsto :
    Tendsto correlation atTop (𝓝 (Real.log
      ((Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))^2/
        Matrix.det (StripEnergyBound.boundarySix (1/Real.pi))))) := by
  obtain ⟨h3,hp0,_,hm0,_⟩ := StripEnergyBound.determinant_polynomial_bounds
  have ht3 : 0<Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)) := by
    rw [StripEnergyBound.boundaryThree_det]; linarith
  have ht6 : 0<Matrix.det (StripEnergyBound.boundarySix (1/Real.pi)) := by
    rw [StripEnergyBound.boundarySix_det]
    exact mul_pos (by linarith) (by linarith)
  have hl := boundaryLeftThree_det_tendsto.log ht3.ne'
  have hr := boundaryRightThree_det_tendsto.log ht3.ne'
  have hs := boundarySix_det_tendsto.log ht6.ne'
  have he : Real.log (Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))+
      Real.log (Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))-
      Real.log (Matrix.det (StripEnergyBound.boundarySix (1/Real.pi)))=
      Real.log ((Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))^2/
        Matrix.det (StripEnergyBound.boundarySix (1/Real.pi))) := by
    rw [Real.log_div (pow_pos ht3 2).ne' ht6.ne',Real.log_pow]
    ring
  have h := (hl.add hr).sub hs
  rw [he] at h
  exact h

theorem halfPlane_comparison (k : ℕ) :
    2*realEnergy (horizontalStrip k)+Real.log
      ((Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))^2/
        Matrix.det (StripEnergyBound.boundarySix (1/Real.pi))) ≤
      SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2) := by
  exact le_of_tendsto (tendsto_const_nhds.add correlation_tendsto)
    (Eventually.of_forall (finite_comparison k))

/-- Uniform in every finite strip length, obtained from actual lattice walks. -/
theorem realEnergy_strip_lt (k : ℕ) : realEnergy (horizontalStrip k)<(81 : ℝ)/1250 := by
  have hc := halfPlane_comparison k
  have hm := StripEnergyBound.remaining_margin_lt
  have hl := StripEnergyBound.boundarySix_log_ratio_lower
  linarith

theorem realEnergy_strip_lt_13_200 (k : ℕ) : realEnergy (horizontalStrip k)<(13 : ℝ)/200 :=
  (realEnergy_strip_lt k).trans StripEnergyBound.margin_lt_target

def stripEnergyLimit : ℝ := ⨆ k : ℕ, realEnergy (horizontalStrip k)

theorem stripEnergy_bddAbove : BddAbove (Set.range (fun k => realEnergy (horizontalStrip k))) :=
  ⟨(81 : ℝ)/1250,fun _ ⟨k,hk⟩ => hk ▸ (realEnergy_strip_lt k).le⟩

theorem realEnergy_strip_le_limit (k : ℕ) : realEnergy (horizontalStrip k)≤stripEnergyLimit :=
  le_ciSup stripEnergy_bddAbove k

/-- The common upper estimate has a strict margin even after taking the supremum. -/
theorem stripEnergyLimit_lt : stripEnergyLimit<(81 : ℝ)/1250 := by
  have hle : stripEnergyLimit≤
      (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2)-Real.log
        ((Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))^2/
          Matrix.det (StripEnergyBound.boundarySix (1/Real.pi))))/2 := by
    apply ciSup_le
    intro k
    linarith [halfPlane_comparison k]
  have hl := StripEnergyBound.boundarySix_log_ratio_lower
  have hm := StripEnergyBound.remaining_margin_lt
  linarith

theorem realEnergy_strip_tendsto :
    Tendsto (fun k => realEnergy (horizontalStrip k)) atTop (𝓝 stripEnergyLimit) :=
  tendsto_atTop_ciSup realEnergy_strip_monotone stripEnergy_bddAbove

end
end SpanningTreeIsoperimetry.UniformStripEnergy
