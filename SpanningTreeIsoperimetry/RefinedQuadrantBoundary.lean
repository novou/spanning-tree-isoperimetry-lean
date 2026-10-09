import SpanningTreeIsoperimetry.BoundaryGreenRefined
import SpanningTreeIsoperimetry.QuadrantBoundaryGreen
import SpanningTreeIsoperimetry.QuadrantMinorEnergy

/-! The actual first six quadrant boundary sites and the exact strip-energy
interface for the refined corner comparisons. -/
namespace SpanningTreeIsoperimetry.RefinedQuadrantBoundary
open Ferrers CornerEnergy BoundaryGreen BoundaryGreenRefined QuadrantWalkCount
open BoundaryGreenBounds BoundaryGreenLoss Filter SquareMaximality.Boundary
open scoped BigOperators Topology Classical Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def cornerEntry (t : ℝ) (i j : Fin 6) : ℝ :=
  planeEntry13 t ⟨Nat.dist i.val j.val,by have hi:=i.isLt; have hj:=j.isLt; unfold Nat.dist; omega⟩-
    planeEntry13 t ⟨i.val+j.val+2,by have hi:=i.isLt; have hj:=j.isLt; omega⟩

theorem quadrantCoefficient_hasSum (a b : Fin 6) :
    HasSum (fun n => quadrantCoefficient n a.val b.val) (cornerEntry (1/Real.pi) a b) := by
  have hdist : Nat.dist a.val b.val<13 := by have ha:=a.isLt; have hb:=b.isLt; unfold Nat.dist; omega
  have hsum : a.val+b.val+2<13 := by have ha:=a.isLt; have hb:=b.isLt; omega
  have h := ((halfPlaneCoefficient_thirteen_hasSum ⟨Nat.dist a.val b.val,hdist⟩).sub
    (halfPlaneCoefficient_thirteen_hasSum ⟨a.val+b.val+2,hsum⟩)).congr_fun
      (fun n => quadrantCoefficient_eq n a.val b.val)
  simpa only [boundaryValueThirteen_eq,cornerEntry] using h

theorem boundaryEntry_tendsto (a b : Fin 6) :
    Tendsto (fun N => QuadrantBoundaryGreen.greenEntry N a b) atTop
      (𝓝 (cornerEntry (1/Real.pi) a b)) := by
  have hs := quadrantCoefficient_hasSum a b
  have ht := tendsto_tsum_of_dominated_convergence hs.summable
    (f := fun N n => QuadrantBoundaryGreen.finiteCoefficient N a b n)
    (g := fun n => quadrantCoefficient n a.val b.val)
    (fun n => (tendsto_const_nhds : Tendsto (fun _ : ℕ => quadrantCoefficient n a.val b.val)
      atTop (𝓝 (quadrantCoefficient n a.val b.val))).congr'
      ((eventually_ge_atTop n).mono (fun N hN => (QuadrantBoundaryGreen.finiteCoefficient_eq a b hN).symm)))
    (Eventually.of_forall (fun N n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (QuadrantBoundaryGreen.finiteCoefficient_nonneg N a b n)]
      exact QuadrantBoundaryGreen.finiteCoefficient_le N a b n))
  have hf : (fun N => ∑' n,QuadrantBoundaryGreen.finiteCoefficient N a b n)=
      (fun N => QuadrantBoundaryGreen.greenEntry N a b) := by
    funext N
    exact (QuadrantBoundaryGreen.greenEntry_hasSum N a b).tsum_eq
  rw [hf,hs.tsum_eq] at ht
  exact ht

/-- The affine formula describes the genuine quadrant Green function. -/
theorem quadrantGreen_boundary (a b : Fin 6) :
    quadrantGreen (a.val,0) (b.val,0)=cornerEntry (1/Real.pi) a b := by
  have hi : Tendsto (fun N : ℕ => N+6) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N≤N+6; omega) tendsto_id
  have hq := (green_tendsto_quadrant (a.val,0) (b.val,0)).comp hi
  have he (N : ℕ) : green (box (N+6)) (a.val,0) (b.val,0)=
      QuadrantBoundaryGreen.greenEntry N a b := by
    have hb : box (N+6)=QuadrantBoundaryGreen.window 6 N := by
      unfold box QuadrantBoundaryGreen.window
      rw [foundation_faceIndices]
    have ha : (a.val,0)∈QuadrantBoundaryGreen.window 6 N :=
      (QuadrantBoundaryGreen.boundarySite N a).property
    have hb' : (b.val,0)∈QuadrantBoundaryGreen.window 6 N :=
      (QuadrantBoundaryGreen.boundarySite N b).property
    rw [hb,green_mem ha hb']
    rfl
  apply tendsto_nhds_unique hq
  exact (boundaryEntry_tendsto a b).congr (fun N => (he N).symm)

def stripEquiv (k : ℕ) : Fin k ≃ {p // p∈horizontalStrip k} where
  toFun i := ⟨(i.val,0),mem_horizontalStrip.mpr ⟨i.isLt,rfl⟩⟩
  invFun p := ⟨p.val.1,(mem_horizontalStrip.mp p.property).1⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (mem_horizontalStrip.mp p.property).2.symm

def stripMatrix (t : ℝ) (k : ℕ) (hk : k≤6) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => cornerEntry t (Fin.castLE hk i) (Fin.castLE hk j)

theorem quadrantMinor_strip {k : ℕ} (hk : k≤6) :
    QuadrantMinorEnergy.quadrantMinor (fun i => ((stripEquiv k) i).val)=
      stripMatrix (1/Real.pi) k hk := by
  ext i j
  exact quadrantGreen_boundary (Fin.castLE hk i) (Fin.castLE hk j)

theorem strip_energy_exact {k : ℕ} (hk : k≤6) :
    realEnergy (horizontalStrip k) = -Real.log ((stripMatrix (1/Real.pi) k hk).det)-
      SquareMaximality.squareLatticeEntropy*k := by
  have h := QuadrantMinorEnergy.energy_eq_log_det (horizontalStrip_isFerrers k) (stripEquiv k)
  rw [quadrantMinor_strip hk,card_horizontalStrip] at h
  exact h

end
end SpanningTreeIsoperimetry.RefinedQuadrantBoundary
