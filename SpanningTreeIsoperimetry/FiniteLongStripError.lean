import SpanningTreeIsoperimetry.BoundaryGreenError
import SpanningTreeIsoperimetry.FiniteStripError
import SpanningTreeIsoperimetry.FluxDefinition

/-! The actual finite long-side strip correction has the manuscript's exact
fourth-order bound. Side lengths R,S below count faces (vertices: R+1,S+1). -/
namespace SpanningTreeIsoperimetry.FiniteLongStripError
open Ferrers CornerEnergy CornerStripBridge BoundaryGreenBounds BoundaryGreenError FiniteStripError
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem square_sum (k : ℕ) : (∑ a : Fin k, ((a.val : ℝ)+1)^2)=
    (k : ℝ)*(k+1)*(2*k+1)/6 := by
  have hs (n : ℕ) : (∑ a ∈ Finset.range n, ((a : ℝ)+1)^2)=(n : ℝ)*(n+1)*(2*n+1)/6 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring
  rw [Fin.sum_univ_eq_sum_range (fun a => ((a : ℝ)+1)^2) k]
  exact hs k

private theorem entryBound_side_le {R S k : ℕ} (hk : k+1<S) (a : Fin (k+1)) :
    entryBound R S (1,a.val) (0,a.val)≤
      (Real.pi^3/30)*((a.val : ℝ)+1)^2*
        (1/(((R : ℝ)+1)^2-4)^2+1/(((S : ℝ)+1)^2-((k : ℝ)+1)^2)^2) := by
  have ha : (a.val : ℝ)+1≤(k : ℝ)+1 := by exact_mod_cast (show a.val+1≤k+1 by have h:=a.isLt; omega)
  have ht : (k : ℝ)+1<S := by exact_mod_cast hk
  have hs0 := Nat.cast_nonneg (α := ℝ) S
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  have ha0 := Nat.cast_nonneg (α := ℝ) a.val
  have hgap : 0<((S : ℝ)+1)^2-((k : ℝ)+1)^2 := by nlinarith
  have hsq : ((a.val : ℝ)+1)^2≤((k : ℝ)+1)^2 := pow_le_pow_left₀ (by positivity) ha 2
  have hden : ((S : ℝ)+1)^2-((k : ℝ)+1)^2≤((S : ℝ)+1)^2-((a.val : ℝ)+1)^2 := by linarith
  have hrec : 1/(((S : ℝ)+1)^2-((a.val : ℝ)+1)^2)^2≤
      1/(((S : ℝ)+1)^2-((k : ℝ)+1)^2)^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hgap) (pow_le_pow_left₀ hgap.le hden 2)
  have he : entryBound R S (1,a.val) (0,a.val)=
      (Real.pi^3/30)*((a.val : ℝ)+1)^2*
        (1/(((R : ℝ)+1)^2-4)^2+1/(((S : ℝ)+1)^2-((a.val : ℝ)+1)^2)^2) := by
    simp only [entryBound,Prod.fst,Prod.snd,max_self,Nat.max_eq_left (show (0 : ℕ)≤1 by omega),
      Nat.cast_one,Nat.cast_zero,zero_add]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (add_le_add
    (show 1/(((R : ℝ)+1)^2-4)^2≤1/(((R : ℝ)+1)^2-4)^2 from le_rfl) hrec) (by positivity)

private theorem entryBound_top (R S k : ℕ) :
    entryBound R S (0,k+1) (0,k)=
      Real.pi^3*((k : ℝ)+1)*((k : ℝ)+2)/60*
        (1/(((R : ℝ)+1)^2-1)^2+1/(((S : ℝ)+1)^2-((k : ℝ)+2)^2)^2) := by
  simp only [entryBound,Prod.fst,Prod.snd,max_self,Nat.max_eq_left (Nat.le_succ k),
    Nat.cast_zero,Nat.cast_add,Nat.cast_succ,Nat.cast_one,zero_add]
  ring

/-- Summing the actual pointwise Green bound on the side and top pairs gives
exactly the independently defined fluxBound, with no entrywise premise. -/
theorem stripFlux_le_fluxBound {R S : ℕ} (hR : 2≤R) (k : ℕ) (hk : k+1<S) :
    stripFlux (faceRectangle R S) k≤FluxBounds.fluxBound ((R : ℝ)+1) ((S : ℝ)+1) ((k : ℝ)+1) := by
  have hside (a : Fin (k+1)) :
      quadrantLoss (faceRectangle R S) (1,a.val) (0,a.val)≤
        (Real.pi^3/30)*((a.val : ℝ)+1)^2*
          (1/(((R : ℝ)+1)^2-4)^2+1/(((S : ℝ)+1)^2-((k : ℝ)+1)^2)^2) := by
    have hp : (1,a.val)∈faceRectangle R S := mem_faceRectangle.mpr ⟨by omega,by have h:=a.isLt; omega⟩
    have hq : (0,a.val)∈faceRectangle R S := mem_faceRectangle.mpr ⟨by omega,by have h:=a.isLt; omega⟩
    exact (quadrantLoss_le_entryBound hp hq).trans (entryBound_side_le hk a)
  have htop : quadrantLoss (faceRectangle R S) (0,k+1) (0,k)≤
      Real.pi^3*((k : ℝ)+1)*((k : ℝ)+2)/60*
        (1/(((R : ℝ)+1)^2-1)^2+1/(((S : ℝ)+1)^2-((k : ℝ)+2)^2)^2) := by
    have hp : (0,k+1)∈faceRectangle R S := mem_faceRectangle.mpr ⟨by omega,hk⟩
    have hq : (0,k)∈faceRectangle R S := mem_faceRectangle.mpr ⟨by omega,by omega⟩
    simpa only [entryBound_top] using quadrantLoss_le_entryBound hp hq
  have hsum := add_le_add (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (k+1)))) (fun (a : Fin (k+1)) _ => hside a)) htop
  change stripFlux (faceRectangle R S) k≤_ at hsum
  convert hsum using 1
  rw [← Finset.sum_mul,← Finset.mul_sum,square_sum]
  unfold FluxBounds.fluxBound FluxBounds.cubic FluxBounds.quadratic
  push_cast
  ring

/-- Actual finite Dirichlet strip energy minus its quadrant energy, with the
precise fourth-order error from the manuscript. -/
theorem finite_long_strip_error {R S : ℕ} (hR : 2≤R) (k : ℕ) (hk : k+1<S) :
    let hstrip := verticalDiagram_subset (by omega : 1≤R) (by omega : k+1≤S)
    0≤dirichletEnergy hstrip-realEnergy (horizontalStrip (k+1)) ∧
    dirichletEnergy hstrip-realEnergy (horizontalStrip (k+1))≤
      FluxBounds.fluxBound ((R : ℝ)+1) ((S : ℝ)+1) ((k : ℝ)+1) := by
  dsimp only
  constructor
  · exact energy_correction_nonneg k _
  · exact (energy_correction_le_flux k _).trans (stripFlux_le_fluxBound hR k hk)

end
end SpanningTreeIsoperimetry.FiniteLongStripError
